package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"
)

func TestBuildCanonicalComponent(t *testing.T) {
	directory := writeFixture(t, map[string]string{
		"s.exp": "(a11)*(b11)*(c11)\n(a12)*(b21)*(c12)\n",
		"m.exp": "(a11 + a12)*(b11)*(c11)\n(a21)*(b12 + b22)*(c21)\n",
		"t.exp": "(a11 + a22)*(b11 + b22)*(c11 + c22)\n",
		"z.exp": "(a11 + a21)*(b11)*(c11)\n(a12)*(b12 + b22)*(c12)\n",
	}, strings.Join([]string{
		"s.exp m.exp",
		"m.exp s.exp",
		"m.exp m.exp",
		"m.exp t.exp",
		"z.exp z.exp",
	}, "\n")+"\n")

	cfg := config{
		input:      directory,
		format:     [3]int{2, 2, 2},
		field:      "F2",
		title:      "fixture",
		scope:      "test graph",
		sourceID:   "s",
		repository: "example.invalid/fixture",
		revision:   "fixture-revision",
		iterations: 8,
	}
	graph, err := build(cfg)
	if err != nil {
		t.Fatal(err)
	}

	if graph.Source != "s" || graph.Target != "t" {
		t.Fatalf("endpoints = %q, %q; want s, t", graph.Source, graph.Target)
	}
	if want := []string{"s", "m", "t"}; !reflect.DeepEqual(graph.Path, want) {
		t.Fatalf("path = %v; want %v", graph.Path, want)
	}
	wantStats := stats{Vertices: 3, Edges: 3, Flips: 2, Reductions: 1, SelfLoops: 1, Diameter: 2, PathDistance: 2}
	if graph.Stats != wantStats {
		t.Fatalf("stats = %+v; want %+v", graph.Stats, wantStats)
	}
	if len(graph.Nodes) != 3 || graph.Nodes[0].ID != "m" || graph.Nodes[1].ID != "s" || graph.Nodes[2].ID != "t" {
		t.Fatalf("unexpected sorted nodes: %+v", graph.Nodes)
	}
	for _, node := range graph.Nodes {
		if node.X < 0 || node.X > 1 || node.Y < 0 || node.Y > 1 {
			t.Errorf("node %q has non-normalized position (%v, %v)", node.ID, node.X, node.Y)
		}
	}

	var reduction edge
	for _, candidate := range graph.Edges {
		if candidate.Type == "reduction" {
			reduction = candidate
		}
	}
	if reduction.From != "m" || reduction.To != "t" || !reduction.OnPath {
		t.Fatalf("reduction = %+v; want directed on-path m to t", reduction)
	}

	again, err := build(cfg)
	if err != nil {
		t.Fatal(err)
	}
	firstJSON, err := json.Marshal(graph)
	if err != nil {
		t.Fatal(err)
	}
	secondJSON, err := json.Marshal(again)
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(firstJSON, secondJSON) {
		t.Error("two builds of the same input were not deterministic")
	}
}

func TestBuildRejectsLargeLengthChange(t *testing.T) {
	directory := writeFixture(t, map[string]string{
		"s.exp":    "(a11)*(b11)*(c11)\n(a12)*(b21)*(c12)\n",
		"long.exp": strings.Repeat("(a11 + a12)*(b11)*(c11)\n", 4),
	}, "s.exp long.exp\n")

	_, err := build(config{input: directory, format: [3]int{2, 2, 2}, sourceID: "s"})
	if err == nil || !strings.Contains(err.Error(), "changes presentation length by 2") {
		t.Fatalf("build error = %v; want length-change error", err)
	}
}

func TestSchoolbookDetection(t *testing.T) {
	var terms []term
	for i := 1; i <= 2; i++ {
		for j := 1; j <= 2; j++ {
			for k := 1; k <= 2; k++ {
				terms = append(terms, term{factors: [3][]string{
					{fmt.Sprintf("a%d%d", i, j)},
					{fmt.Sprintf("b%d%d", j, k)},
					{fmt.Sprintf("c%d%d", k, i)},
				}})
			}
		}
	}
	if !isSchoolbook(terms, [3]int{2, 2, 2}) {
		t.Fatal("schoolbook terms were not recognized")
	}
	if isSchoolbook(terms[:len(terms)-1], [3]int{2, 2, 2}) {
		t.Fatal("incomplete coordinate presentation was recognized as schoolbook")
	}
	terms[0].factors[2][0] = "c12"
	if isSchoolbook(terms, [3]int{2, 2, 2}) {
		t.Fatal("incompatible coordinate factors were recognized as schoolbook")
	}
}

func TestParseFactor(t *testing.T) {
	factor, err := parseFactor("(a22 + a11)", 'a', 2, 2)
	if err != nil {
		t.Fatal(err)
	}
	if want := []string{"a11", "a22"}; !reflect.DeepEqual(factor, want) {
		t.Fatalf("factor = %v; want %v", factor, want)
	}
	for _, value := range []string{"a11", "()", "(a13)", "(b11)", "(a11 + a11)"} {
		if _, err := parseFactor(value, 'a', 2, 2); err == nil {
			t.Errorf("parseFactor(%q) succeeded; want error", value)
		}
	}
}

func writeFixture(t *testing.T, representatives map[string]string, edges string) string {
	t.Helper()
	directory := t.TempDir()
	vertices := filepath.Join(directory, "vertices")
	if err := os.Mkdir(vertices, 0o755); err != nil {
		t.Fatal(err)
	}
	for name, contents := range representatives {
		if err := os.WriteFile(filepath.Join(vertices, name), []byte(contents), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	if err := os.WriteFile(filepath.Join(directory, "edges.txt"), []byte(edges), 0o644); err != nil {
		t.Fatal(err)
	}
	return directory
}
