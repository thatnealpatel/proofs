package main

import (
	"encoding/json/v2"
	"io"
	"math/big"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"
)

const matrixWidth = 9

type sampledGraph struct {
	Title      string        `json:"title"`
	Scope      string        `json:"scope"`
	Provenance string        `json:"provenance"`
	Path       []string      `json:"path"`
	Nodes      []sampledNode `json:"nodes"`
	Edges      []sampledEdge `json:"edges"`
}

type sampledNode struct {
	ID          string         `json:"id"`
	Rank        int            `json:"rank"`
	PathIndex   *int           `json:"pathIndex"`
	Verified729 bool           `json:"verified729"`
	Movable     int            `json:"movablePairs"`
	ByMode      map[string]int `json:"movableByMode"`
	Reductions  int            `json:"reductions"`
}

type sampledEdge struct {
	ID           string         `json:"id"`
	From         string         `json:"from"`
	To           string         `json:"to"`
	Type         string         `json:"type"`
	Mode         string         `json:"mode"`
	OnPath       bool           `json:"onPath"`
	BasisColumns [][]string     `json:"basisColumns"`
	Removed      []rationalTerm `json:"removed"`
	Added        []rationalTerm `json:"added"`
}

type rationalTerm struct {
	A           [matrixWidth]string `json:"A"`
	B           [matrixWidth]string `json:"B"`
	C           [matrixWidth]string `json:"C"`
	Coefficient string              `json:"coefficient"`
}

func decodeSampledGraph(t *testing.T, data []byte) sampledGraph {
	t.Helper()
	var graph sampledGraph
	if err := json.Unmarshal(data, &graph); err != nil {
		t.Fatalf("decode sampled graph: %v", err)
	}
	return graph
}

func rational(t *testing.T, value string) *big.Rat {
	t.Helper()
	result, ok := new(big.Rat).SetString(value)
	if !ok {
		t.Fatalf("invalid rational %q", value)
	}
	return result
}

func expandRationalTerms(t *testing.T, terms []rationalTerm) [matrixWidth * matrixWidth * matrixWidth]big.Rat {
	t.Helper()
	var result [matrixWidth * matrixWidth * matrixWidth]big.Rat
	for _, term := range terms {
		coefficient := rational(t, term.Coefficient)
		for a, avs := range term.A {
			av := rational(t, avs)
			if av.Sign() == 0 {
				continue
			}
			for b, bvs := range term.B {
				bv := rational(t, bvs)
				if bv.Sign() == 0 {
					continue
				}
				for c, cvs := range term.C {
					cv := rational(t, cvs)
					if cv.Sign() == 0 {
						continue
					}
					var product big.Rat
					product.Mul(coefficient, av)
					product.Mul(&product, bv)
					product.Mul(&product, cv)
					index := (a*matrixWidth+b)*matrixWidth + c
					result[index].Add(&result[index], &product)
				}
			}
		}
	}
	return result
}

func equalRationalExpansions(left, right [matrixWidth * matrixWidth * matrixWidth]big.Rat) bool {
	for index := range left {
		if left[index].Cmp(&right[index]) != 0 {
			return false
		}
	}
	return true
}

func TestSampledGraphHasExactRecordedPathAndTypedNeighborhood(t *testing.T) {
	data, err := staticFiles.ReadFile("static/graph.json")
	if err != nil {
		t.Fatal(err)
	}
	graph := decodeSampledGraph(t, data)
	if got, want := len(graph.Nodes), 76; got != want {
		t.Fatalf("node count = %d, want %d", got, want)
	}
	if got, want := len(graph.Edges), 141; got != want {
		t.Fatalf("edge count = %d, want %d", got, want)
	}
	if got, want := len(graph.Path), 10; got != want {
		t.Fatalf("path length = %d, want %d", got, want)
	}
	if graph.Path[0] != "8c6491682f13" || graph.Path[len(graph.Path)-1] != "e286352231ce" {
		t.Errorf("unexpected path endpoints %q and %q", graph.Path[0], graph.Path[len(graph.Path)-1])
	}

	nodes := make(map[string]sampledNode, len(graph.Nodes))
	for _, node := range graph.Nodes {
		if _, exists := nodes[node.ID]; exists {
			t.Fatalf("duplicate node %q", node.ID)
		}
		if !node.Verified729 {
			t.Errorf("node %q is not marked verified", node.ID)
		}
		nodes[node.ID] = node
	}
	for index, id := range graph.Path {
		node, ok := nodes[id]
		if !ok {
			t.Fatalf("path node %q is absent", id)
		}
		wantRank := 24
		if index == 0 {
			wantRank = 23
		}
		if node.Rank != wantRank {
			t.Errorf("path node %q length = %d, want %d", id, node.Rank, wantRank)
		}
		if node.PathIndex == nil || *node.PathIndex != index {
			t.Errorf("path node %q index = %v, want %d", id, node.PathIndex, index)
		}
	}

	pathEdges := make(map[[2]string]sampledEdge)
	types := make(map[string]bool)
	factorDeltas := 0
	for _, edge := range graph.Edges {
		from, fromOK := nodes[edge.From]
		to, toOK := nodes[edge.To]
		if !fromOK || !toOK {
			t.Fatalf("edge %q has unknown endpoints %q -> %q", edge.ID, edge.From, edge.To)
		}
		types[edge.Type] = true
		switch edge.Type {
		case "flip":
			if from.Rank != to.Rank {
				t.Errorf("flip %q changes length from %d to %d", edge.ID, from.Rank, to.Rank)
			}
			if edge.Mode == "" || len(edge.BasisColumns) != 2 {
				t.Errorf("flip %q lacks its shared mode or basis", edge.ID)
			}
		case "split":
			if to.Rank-from.Rank != 1 {
				t.Errorf("split %q has length change %d", edge.ID, to.Rank-from.Rank)
			}
		case "reduction":
			if to.Rank-from.Rank != -1 {
				t.Errorf("reduction %q has length change %d", edge.ID, to.Rank-from.Rank)
			}
		default:
			t.Errorf("edge %q has unknown type %q", edge.ID, edge.Type)
		}
		if len(edge.Removed) > 0 || len(edge.Added) > 0 {
			factorDeltas++
			left := expandRationalTerms(t, edge.Removed)
			right := expandRationalTerms(t, edge.Added)
			if !equalRationalExpansions(left, right) {
				t.Errorf("edge %q does not preserve the exact local tensor", edge.ID)
			}
		}
		if edge.OnPath {
			pathEdges[[2]string{edge.From, edge.To}] = edge
		}
	}
	if factorDeltas != len(graph.Path) {
		t.Errorf("factor deltas = %d, want %d recorded path edges plus reduction", factorDeltas, len(graph.Path))
	}
	for _, edgeType := range []string{"flip", "split", "reduction"} {
		if !types[edgeType] {
			t.Errorf("sample has no %s edge", edgeType)
		}
	}
	for index := 1; index < len(graph.Path); index++ {
		key := [2]string{graph.Path[index-1], graph.Path[index]}
		if _, ok := pathEdges[key]; !ok {
			t.Errorf("missing recorded path edge %q -> %q", key[0], key[1])
		}
	}
}

func TestEmbeddedAssetsAndGraphHandlerWorkOutsideRepository(t *testing.T) {
	oldDirectory, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() {
		if err := os.Chdir(oldDirectory); err != nil {
			t.Errorf("restore working directory: %v", err)
		}
	})
	if err := os.Chdir(t.TempDir()); err != nil {
		t.Fatal(err)
	}
	handler, err := newHandler()
	if err != nil {
		t.Fatal(err)
	}
	server := httptest.NewServer(handler)
	defer server.Close()
	for _, path := range []string{"/", "/app.js", "/style.css", "/api/graph"} {
		response, err := http.Get(server.URL + path)
		if err != nil {
			t.Fatalf("GET %s: %v", path, err)
		}
		body, readErr := io.ReadAll(response.Body)
		if closeErr := response.Body.Close(); readErr == nil {
			readErr = closeErr
		}
		if readErr != nil {
			t.Fatalf("read %s: %v", path, readErr)
		}
		if response.StatusCode != http.StatusOK || len(body) == 0 {
			t.Errorf("GET %s returned status %d and %d bytes", path, response.StatusCode, len(body))
		}
		if path == "/api/graph" {
			graph := decodeSampledGraph(t, body)
			if len(graph.Nodes) != 76 || len(graph.Edges) != 141 {
				t.Errorf("graph has %d nodes and %d edges", len(graph.Nodes), len(graph.Edges))
			}
		}
	}
}

func TestHandlerAndUIDocumentSafetyAndScope(t *testing.T) {
	handler, err := newHandler()
	if err != nil {
		t.Fatal(err)
	}
	request := httptest.NewRequest(http.MethodPost, "/", nil)
	recorder := httptest.NewRecorder()
	handler.ServeHTTP(recorder, request)
	if recorder.Code != http.StatusMethodNotAllowed || recorder.Header().Get("Allow") != "GET, HEAD" {
		t.Fatalf("POST returned %d Allow %q", recorder.Code, recorder.Header().Get("Allow"))
	}
	body, err := staticFiles.ReadFile("static/index.html")
	if err != nil {
		t.Fatal(err)
	}
	page := string(body)
	for _, phrase := range []string{
		"Every vertex is a complete decomposition",
		"Same-rank flip edges are invertible",
		"reduction back to Laderman rank 23",
		"not an exhaustive search, an optimality proof, or a nonexistence result",
	} {
		if !strings.Contains(page, phrase) {
			t.Errorf("UI does not contain %q", phrase)
		}
	}
}

func TestDefaultListenerAddress(t *testing.T) {
	if defaultAddress != ":11111" {
		t.Fatalf("default address = %q, want %q", defaultAddress, ":11111")
	}
}
