package main

import (
	"encoding/json"
	"fmt"
	"testing"
)

type generatedGraph struct {
	Schema string `json:"schema"`
	Field  string `json:"field"`
	Source string `json:"source"`
	Target string `json:"target"`
	Path   []string
	Nodes  []struct {
		ID        string
		Length    int
		PathIndex *int `json:"pathIndex"`
		X         float64
		Y         float64
	}
	Edges []struct {
		From     string
		To       string
		Type     string
		OnPath   bool `json:"onPath"`
		SelfLoop bool `json:"selfLoop"`
	}
	Stats struct {
		Vertices     int
		Edges        int
		Flips        int
		Reductions   int
		SelfLoops    int
		Diameter     int
		PathDistance int
	}
}

func TestGeneratedM2Graph(t *testing.T) {
	data, err := staticFiles.ReadFile("static/graph-222.json")
	if err != nil {
		t.Fatal(err)
	}
	var graph generatedGraph
	if err := json.Unmarshal(data, &graph); err != nil {
		t.Fatal(err)
	}

	if graph.Schema != "flip-graph/v1" || graph.Field != "F₂" {
		t.Fatalf("schema and field = %q, %q", graph.Schema, graph.Field)
	}
	if graph.Source != "a5274cdb4b34" || graph.Target != "a9538cf70e1b" {
		t.Fatalf("endpoints = %q, %q", graph.Source, graph.Target)
	}
	if len(graph.Path) != 9 {
		t.Fatalf("path has %d vertices; want 9", len(graph.Path))
	}
	if graph.Stats.Vertices != 272 || graph.Stats.Edges != 1183 || graph.Stats.Flips != 1176 ||
		graph.Stats.Reductions != 7 || graph.Stats.SelfLoops != 40 || graph.Stats.Diameter != 12 || graph.Stats.PathDistance != 8 {
		t.Fatalf("unexpected published graph statistics: %+v", graph.Stats)
	}
	if len(graph.Nodes) != graph.Stats.Vertices || len(graph.Edges) != graph.Stats.Edges {
		t.Fatalf("array sizes = %d nodes, %d edges", len(graph.Nodes), len(graph.Edges))
	}

	nodes := make(map[string]struct {
		length int
		path   *int
	}, len(graph.Nodes))
	lengthSeven := 0
	for _, node := range graph.Nodes {
		if _, duplicate := nodes[node.ID]; duplicate {
			t.Fatalf("duplicate node %q", node.ID)
		}
		if node.X < 0 || node.X > 1 || node.Y < 0 || node.Y > 1 {
			t.Fatalf("node %q has non-normalized coordinates (%v, %v)", node.ID, node.X, node.Y)
		}
		if node.Length == 7 {
			lengthSeven++
		}
		nodes[node.ID] = struct {
			length int
			path   *int
		}{node.Length, node.PathIndex}
	}
	if lengthSeven != 1 || nodes[graph.Target].length != 7 || nodes[graph.Source].length != 8 {
		t.Fatalf("length-7 count and endpoint lengths = %d, %d, %d", lengthSeven, nodes[graph.Source].length, nodes[graph.Target].length)
	}

	edges := make(map[string]bool, len(graph.Edges))
	onPath := make(map[string]bool, len(graph.Path)-1)
	loops := 0
	reductions := 0
	for _, edge := range graph.Edges {
		if _, ok := nodes[edge.From]; !ok {
			t.Fatalf("edge has unknown source %q", edge.From)
		}
		if _, ok := nodes[edge.To]; !ok {
			t.Fatalf("edge has unknown target %q", edge.To)
		}
		key := canonicalEdge(edge.From, edge.To)
		if edges[key] {
			t.Fatalf("duplicate canonical edge %q", key)
		}
		edges[key] = true
		if edge.SelfLoop {
			loops++
		}
		if edge.Type == "reduction" {
			reductions++
			if nodes[edge.From].length != nodes[edge.To].length+1 {
				t.Fatalf("reduction %q is not directed long to short", key)
			}
		} else if edge.Type != "flip" {
			t.Fatalf("unknown edge type %q", edge.Type)
		}
		if edge.OnPath {
			onPath[key] = true
		}
	}
	if loops != 40 || reductions != 7 || len(onPath) != 8 {
		t.Fatalf("observed %d loops, %d reductions, %d path edges", loops, reductions, len(onPath))
	}
	for index := 1; index < len(graph.Path); index++ {
		if !onPath[canonicalEdge(graph.Path[index-1], graph.Path[index])] {
			t.Fatalf("path step %d is not marked on-path", index)
		}
		if nodes[graph.Path[index]].path == nil || *nodes[graph.Path[index]].path != index {
			t.Fatalf("path node %d has wrong pathIndex", index)
		}
	}
}

func canonicalEdge(a, b string) string {
	if b < a {
		a, b = b, a
	}
	return fmt.Sprintf("%s--%s", a, b)
}
