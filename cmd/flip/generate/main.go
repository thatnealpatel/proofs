// Command generate imports an orbit flip graph from the machine-readable
// output published with Moosbauer and Poole's flip-graph paper.
package main

import (
	"bufio"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"hash/fnv"
	"math"
	"os"
	"path/filepath"
	"slices"
	"strconv"
	"strings"
)

const schema = "flip-graph/v1"

type config struct {
	input      string
	output     string
	format     [3]int
	field      string
	title      string
	scope      string
	sourceID   string
	targetID   string
	repository string
	revision   string
	license    string
	iterations int
}

type term struct {
	factors [3][]string
}

type scheme struct {
	id        string
	terms     []term
	standard  bool
	histogram [3][]int
}

type pair struct {
	a string
	b string
}

type graphFile struct {
	Schema        string     `json:"schema"`
	Title         string     `json:"title"`
	Scope         string     `json:"scope"`
	Field         string     `json:"field"`
	Format        [3]int     `json:"format"`
	OrbitQuotient bool       `json:"orbitQuotient"`
	Source        string     `json:"source"`
	Target        string     `json:"target"`
	Path          []string   `json:"path"`
	Nodes         []node     `json:"nodes"`
	Edges         []edge     `json:"edges"`
	Stats         stats      `json:"stats"`
	Provenance    provenance `json:"provenance"`
}

type node struct {
	ID               string   `json:"id"`
	Name             string   `json:"name"`
	Length           int      `json:"length"`
	Degree           int      `json:"degree"`
	FlipEdges        int      `json:"flipEdges"`
	Reductions       int      `json:"reductions"`
	SelfLoops        int      `json:"selfLoops"`
	SupportHistogram [3][]int `json:"supportHistogram"`
	PathIndex        *int     `json:"pathIndex,omitempty"`
	X                float64  `json:"x"`
	Y                float64  `json:"y"`
}

type edge struct {
	ID       string `json:"id"`
	From     string `json:"from"`
	To       string `json:"to"`
	Type     string `json:"type"`
	OnPath   bool   `json:"onPath,omitempty"`
	SelfLoop bool   `json:"selfLoop,omitempty"`
}

type stats struct {
	Vertices     int `json:"vertices"`
	Edges        int `json:"edges"`
	Flips        int `json:"flips"`
	Reductions   int `json:"reductions"`
	SelfLoops    int `json:"selfLoops"`
	Diameter     int `json:"diameter"`
	PathDistance int `json:"pathDistance"`
}

type provenance struct {
	Repository string `json:"repository"`
	Revision   string `json:"revision"`
	Dataset    string `json:"dataset"`
	License    string `json:"license,omitempty"`
	Generated  string `json:"generated"`
}

type point struct {
	x float64
	y float64
}

func main() {
	cfg := config{}
	format := "2,2,2"
	flag.StringVar(&cfg.input, "input", "", "dataset directory containing edges.txt and vertices/*.exp")
	flag.StringVar(&cfg.output, "output", "", "output JSON file (default stdout)")
	flag.StringVar(&format, "format", format, "matrix multiplication format n,m,l")
	flag.StringVar(&cfg.field, "field", "F2", "coefficient field label")
	flag.StringVar(&cfg.title, "title", "Orbit flip graph", "graph title")
	flag.StringVar(&cfg.scope, "scope", "", "short scope statement")
	flag.StringVar(&cfg.sourceID, "source", "", "source representative ID (auto-detect schoolbook when empty)")
	flag.StringVar(&cfg.targetID, "target", "", "target representative ID (choose shortest presentation when empty)")
	flag.StringVar(&cfg.repository, "repository", "https://github.com/jakobmoosbauer/flips", "source repository URL")
	flag.StringVar(&cfg.revision, "revision", "", "source repository revision")
	flag.StringVar(&cfg.license, "license", "", "SPDX license identifier for the source dataset")
	flag.IntVar(&cfg.iterations, "layout-iterations", 500, "deterministic force-layout iterations")
	flag.Parse()

	var err error
	cfg.format, err = parseFormat(format)
	if err != nil {
		fatal(err)
	}
	if cfg.input == "" {
		fatal(errors.New("-input is required"))
	}
	if cfg.iterations < 0 {
		fatal(errors.New("-layout-iterations must not be negative"))
	}

	graph, err := build(cfg)
	if err != nil {
		fatal(err)
	}
	if err := writeJSON(cfg.output, graph); err != nil {
		fatal(err)
	}
}

func fatal(err error) {
	fmt.Fprintln(os.Stderr, "flip graph generator:", err)
	os.Exit(1)
}

func parseFormat(value string) ([3]int, error) {
	var result [3]int
	parts := strings.Split(value, ",")
	if len(parts) != len(result) {
		return result, fmt.Errorf("format %q must have three comma-separated dimensions", value)
	}
	for i, part := range parts {
		dimension, err := strconv.Atoi(strings.TrimSpace(part))
		if err != nil || dimension < 1 || dimension > 9 {
			return result, fmt.Errorf("format dimension %q must be an integer from 1 through 9", part)
		}
		result[i] = dimension
	}
	return result, nil
}

func build(cfg config) (graphFile, error) {
	schemes, err := readSchemes(filepath.Join(cfg.input, "vertices"), cfg.format)
	if err != nil {
		return graphFile{}, err
	}
	pairs, err := readEdges(filepath.Join(cfg.input, "edges.txt"), schemes)
	if err != nil {
		return graphFile{}, err
	}

	source, err := chooseSource(schemes, cfg.sourceID)
	if err != nil {
		return graphFile{}, err
	}
	component := connectedComponent(source, pairs)
	for id := range schemes {
		if !component[id] {
			delete(schemes, id)
		}
	}
	pairs = filterEdges(pairs, component)
	target, err := chooseTarget(schemes, cfg.targetID)
	if err != nil {
		return graphFile{}, err
	}
	path, err := shortestPath(source, target, pairs)
	if err != nil {
		return graphFile{}, err
	}

	nodes, edges, err := assemble(schemes, pairs, path)
	if err != nil {
		return graphFile{}, err
	}
	positions := layout(nodes, edges, path, cfg.iterations)
	for i := range nodes {
		nodes[i].X = round(positions[nodes[i].ID].x, 2)
		nodes[i].Y = round(positions[nodes[i].ID].y, 2)
	}

	graph := graphFile{
		Schema:        schema,
		Title:         cfg.title,
		Scope:         cfg.scope,
		Field:         cfg.field,
		Format:        cfg.format,
		OrbitQuotient: true,
		Source:        source,
		Target:        target,
		Path:          path,
		Nodes:         nodes,
		Edges:         edges,
		Provenance: provenance{
			Repository: cfg.repository,
			Revision:   cfg.revision,
			Dataset:    filepath.Base(filepath.Clean(cfg.input)),
			License:    cfg.license,
			Generated:  "Parsed from .exp representatives and deduplicated edges.txt; layout is deterministic and is not copied from the paper figure.",
		},
	}
	graph.Stats = summarize(nodes, edges, pairs)
	graph.Stats.PathDistance = len(path) - 1
	return graph, nil
}

func readSchemes(directory string, format [3]int) (map[string]*scheme, error) {
	entries, err := os.ReadDir(directory)
	if err != nil {
		return nil, fmt.Errorf("read vertices: %w", err)
	}
	schemes := make(map[string]*scheme, len(entries))
	for _, entry := range entries {
		if entry.IsDir() || filepath.Ext(entry.Name()) != ".exp" {
			continue
		}
		id := strings.TrimSuffix(entry.Name(), filepath.Ext(entry.Name()))
		terms, err := readScheme(filepath.Join(directory, entry.Name()), format)
		if err != nil {
			return nil, fmt.Errorf("read representative %s: %w", id, err)
		}
		s := &scheme{id: id, terms: terms, standard: isSchoolbook(terms, format)}
		for mode := range s.histogram {
			width := format[mode] * format[(mode+1)%3]
			s.histogram[mode] = make([]int, width)
			for _, term := range terms {
				s.histogram[mode][len(term.factors[mode])-1]++
			}
		}
		schemes[id] = s
	}
	if len(schemes) == 0 {
		return nil, errors.New("no .exp representatives found")
	}
	return schemes, nil
}

func readScheme(path string, format [3]int) ([]term, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer file.Close()

	var terms []term
	scanner := bufio.NewScanner(file)
	for line := 1; scanner.Scan(); line++ {
		value := strings.TrimSpace(scanner.Text())
		if value == "" {
			continue
		}
		parts := strings.Split(value, "*")
		if len(parts) != 3 {
			return nil, fmt.Errorf("line %d: expected three factors", line)
		}
		var parsed term
		for mode, part := range parts {
			factor, err := parseFactor(part, "abc"[mode], format[mode], format[(mode+1)%3])
			if err != nil {
				return nil, fmt.Errorf("line %d: %w", line, err)
			}
			parsed.factors[mode] = factor
		}
		terms = append(terms, parsed)
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	if len(terms) == 0 {
		return nil, errors.New("empty representative")
	}
	return terms, nil
}

func parseFactor(value string, variable byte, rows, columns int) ([]string, error) {
	value = strings.TrimSpace(value)
	if len(value) < 3 || value[0] != '(' || value[len(value)-1] != ')' {
		return nil, fmt.Errorf("invalid factor %q", value)
	}
	pieces := strings.Split(value[1:len(value)-1], "+")
	factor := make([]string, 0, len(pieces))
	seen := make(map[string]bool, len(pieces))
	for _, piece := range pieces {
		name := strings.TrimSpace(piece)
		if len(name) != 3 || name[0] != variable || name[1] < '1' || name[1] > byte('0'+rows) || name[2] < '1' || name[2] > byte('0'+columns) {
			return nil, fmt.Errorf("invalid %c factor entry %q", variable, name)
		}
		if seen[name] {
			return nil, fmt.Errorf("duplicate factor entry %q", name)
		}
		seen[name] = true
		factor = append(factor, name)
	}
	slices.Sort(factor)
	return factor, nil
}

func isSchoolbook(terms []term, format [3]int) bool {
	if len(terms) != format[0]*format[1]*format[2] {
		return false
	}
	seen := make(map[[3]byte]bool, len(terms))
	for _, term := range terms {
		for _, factor := range term.factors {
			if len(factor) != 1 {
				return false
			}
		}
		a, b, c := term.factors[0][0], term.factors[1][0], term.factors[2][0]
		if a[2] != b[1] || b[2] != c[1] || c[2] != a[1] {
			return false
		}
		triple := [3]byte{a[1], a[2], b[2]}
		if seen[triple] {
			return false
		}
		seen[triple] = true
	}
	return len(seen) == len(terms)
}

func readEdges(path string, schemes map[string]*scheme) ([]pair, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, fmt.Errorf("read edges: %w", err)
	}
	defer file.Close()

	unique := make(map[pair]bool)
	scanner := bufio.NewScanner(file)
	for line := 1; scanner.Scan(); line++ {
		fields := strings.Fields(scanner.Text())
		if len(fields) == 0 {
			continue
		}
		if len(fields) != 2 {
			return nil, fmt.Errorf("edges line %d: expected two endpoints", line)
		}
		a := strings.TrimSuffix(filepath.Base(fields[0]), filepath.Ext(fields[0]))
		b := strings.TrimSuffix(filepath.Base(fields[1]), filepath.Ext(fields[1]))
		if schemes[a] == nil || schemes[b] == nil {
			return nil, fmt.Errorf("edges line %d: unknown endpoint %q or %q", line, a, b)
		}
		if b < a {
			a, b = b, a
		}
		unique[pair{a: a, b: b}] = true
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	pairs := make([]pair, 0, len(unique))
	for edge := range unique {
		pairs = append(pairs, edge)
	}
	slices.SortFunc(pairs, func(a, b pair) int {
		if order := strings.Compare(a.a, b.a); order != 0 {
			return order
		}
		return strings.Compare(a.b, b.b)
	})
	return pairs, nil
}

func chooseSource(schemes map[string]*scheme, requested string) (string, error) {
	if requested != "" {
		if schemes[requested] == nil {
			return "", fmt.Errorf("source representative %q not found", requested)
		}
		return requested, nil
	}
	var candidates []string
	for id, scheme := range schemes {
		if scheme.standard {
			candidates = append(candidates, id)
		}
	}
	slices.Sort(candidates)
	if len(candidates) != 1 {
		return "", fmt.Errorf("schoolbook auto-detection found %d candidates; use -source", len(candidates))
	}
	return candidates[0], nil
}

func chooseTarget(schemes map[string]*scheme, requested string) (string, error) {
	if requested != "" {
		if schemes[requested] == nil {
			return "", fmt.Errorf("target representative %q is outside the source component", requested)
		}
		return requested, nil
	}
	ids := sortedSchemeIDs(schemes)
	target := ids[0]
	for _, id := range ids[1:] {
		if len(schemes[id].terms) < len(schemes[target].terms) {
			target = id
		}
	}
	return target, nil
}

func connectedComponent(source string, pairs []pair) map[string]bool {
	adjacency := adjacency(pairs)
	seen := map[string]bool{source: true}
	queue := []string{source}
	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]
		for _, next := range adjacency[current] {
			if !seen[next] {
				seen[next] = true
				queue = append(queue, next)
			}
		}
	}
	return seen
}

func filterEdges(pairs []pair, component map[string]bool) []pair {
	filtered := make([]pair, 0, len(pairs))
	for _, edge := range pairs {
		if component[edge.a] && component[edge.b] {
			filtered = append(filtered, edge)
		}
	}
	return filtered
}

func adjacency(pairs []pair) map[string][]string {
	result := make(map[string][]string)
	for _, edge := range pairs {
		if edge.a == edge.b {
			continue
		}
		result[edge.a] = append(result[edge.a], edge.b)
		result[edge.b] = append(result[edge.b], edge.a)
	}
	for id := range result {
		slices.Sort(result[id])
	}
	return result
}

func shortestPath(source, target string, pairs []pair) ([]string, error) {
	if source == target {
		return []string{source}, nil
	}
	adjacency := adjacency(pairs)
	previous := map[string]string{source: ""}
	queue := []string{source}
	for len(queue) > 0 {
		current := queue[0]
		queue = queue[1:]
		for _, next := range adjacency[current] {
			if _, seen := previous[next]; seen {
				continue
			}
			previous[next] = current
			if next == target {
				var reverse []string
				for at := target; at != ""; at = previous[at] {
					reverse = append(reverse, at)
				}
				slices.Reverse(reverse)
				return reverse, nil
			}
			queue = append(queue, next)
		}
	}
	return nil, fmt.Errorf("no path from %q to %q", source, target)
}

func assemble(schemes map[string]*scheme, pairs []pair, path []string) ([]node, []edge, error) {
	pathIndex := make(map[string]int, len(path))
	pathEdges := make(map[pair]bool, len(path)-1)
	for i, id := range path {
		pathIndex[id] = i
		if i > 0 {
			a, b := path[i-1], id
			if b < a {
				a, b = b, a
			}
			pathEdges[pair{a: a, b: b}] = true
		}
	}

	ids := sortedSchemeIDs(schemes)
	nodes := make([]node, 0, len(ids))
	byID := make(map[string]*node, len(ids))
	for _, id := range ids {
		scheme := schemes[id]
		entry := node{
			ID:               id,
			Name:             shortID(id),
			Length:           len(scheme.terms),
			SupportHistogram: scheme.histogram,
		}
		if index, ok := pathIndex[id]; ok {
			entry.PathIndex = new(index)
		}
		nodes = append(nodes, entry)
		byID[id] = &nodes[len(nodes)-1]
	}

	edges := make([]edge, 0, len(pairs))
	neighbors := make(map[string]map[string]bool, len(nodes))
	for i, endpoints := range pairs {
		a, b := endpoints.a, endpoints.b
		from, to := a, b
		edgeType := "flip"
		if len(schemes[a].terms) != len(schemes[b].terms) {
			if difference := abs(len(schemes[a].terms) - len(schemes[b].terms)); difference != 1 {
				return nil, nil, fmt.Errorf("edge %s--%s changes presentation length by %d", a, b, difference)
			}
			edgeType = "reduction"
			if len(schemes[from].terms) < len(schemes[to].terms) {
				from, to = to, from
			}
		}
		entry := edge{
			ID:       fmt.Sprintf("e%d", i),
			From:     from,
			To:       to,
			Type:     edgeType,
			OnPath:   pathEdges[endpoints],
			SelfLoop: a == b,
		}
		edges = append(edges, entry)
		if a == b {
			byID[a].SelfLoops++
		} else {
			if neighbors[a] == nil {
				neighbors[a] = make(map[string]bool)
			}
			if neighbors[b] == nil {
				neighbors[b] = make(map[string]bool)
			}
			neighbors[a][b] = true
			neighbors[b][a] = true
		}
		if edgeType == "reduction" {
			byID[a].Reductions++
			if b != a {
				byID[b].Reductions++
			}
		} else {
			byID[a].FlipEdges++
			if b != a {
				byID[b].FlipEdges++
			}
		}
	}
	for id, adjacent := range neighbors {
		byID[id].Degree = len(adjacent)
	}
	return nodes, edges, nil
}

func summarize(nodes []node, edges []edge, pairs []pair) stats {
	result := stats{Vertices: len(nodes), Edges: len(edges), Diameter: diameter(nodes, pairs)}
	for _, edge := range edges {
		switch edge.Type {
		case "flip":
			result.Flips++
		case "reduction":
			result.Reductions++
		}
		if edge.SelfLoop {
			result.SelfLoops++
		}
	}
	return result
}

func diameter(nodes []node, pairs []pair) int {
	adjacency := adjacency(pairs)
	maximum := 0
	for _, source := range nodes {
		distance := map[string]int{source.ID: 0}
		queue := []string{source.ID}
		for len(queue) > 0 {
			current := queue[0]
			queue = queue[1:]
			for _, next := range adjacency[current] {
				if _, seen := distance[next]; seen {
					continue
				}
				distance[next] = distance[current] + 1
				maximum = max(maximum, distance[next])
				queue = append(queue, next)
			}
		}
	}
	return maximum
}

func layout(nodes []node, edges []edge, path []string, iterations int) map[string]point {
	positions := make(map[string]point, len(nodes))
	index := make(map[string]int, len(nodes))
	for i, node := range nodes {
		index[node.ID] = i
		angle := float64(i) * math.Pi * (3 - math.Sqrt(5))
		radius := 3 * math.Sqrt(float64(i)+1)
		jitter := float64(hash(node.ID)%1000)/1000 - 0.5
		positions[node.ID] = point{x: radius*math.Cos(angle) + jitter, y: radius*math.Sin(angle) - jitter}
	}
	pathIndex := make(map[string]int, len(path))
	for i, id := range path {
		pathIndex[id] = i
	}

	area := math.Max(100, float64(len(nodes))*100)
	ideal := math.Sqrt(area / float64(len(nodes)))
	temperature := math.Sqrt(area) / 7
	for iteration := 0; iteration < iterations; iteration++ {
		delta := make(map[string]point, len(nodes))
		for i := range nodes {
			for j := i + 1; j < len(nodes); j++ {
				a, b := nodes[i].ID, nodes[j].ID
				vector := subtract(positions[a], positions[b])
				distance := math.Max(0.05, magnitude(vector))
				force := ideal * ideal / distance
				movement := scale(vector, force/distance)
				delta[a] = add(delta[a], movement)
				delta[b] = subtract(delta[b], movement)
			}
		}
		for _, edge := range edges {
			if edge.SelfLoop {
				continue
			}
			vector := subtract(positions[edge.From], positions[edge.To])
			distance := math.Max(0.05, magnitude(vector))
			force := distance * distance / ideal
			movement := scale(vector, force/distance)
			delta[edge.From] = subtract(delta[edge.From], movement)
			delta[edge.To] = add(delta[edge.To], movement)
		}
		for id, at := range pathIndex {
			targetX := (float64(at) - float64(len(path)-1)/2) * ideal * 2.5
			anchor := point{x: targetX - positions[id].x, y: -positions[id].y}
			delta[id] = add(delta[id], scale(anchor, 0.35))
		}
		for _, node := range nodes {
			movement := delta[node.ID]
			length := magnitude(movement)
			if length > temperature {
				movement = scale(movement, temperature/length)
			}
			positions[node.ID] = add(positions[node.ID], movement)
		}
		temperature *= 0.992
	}
	return normalize(positions, 0.035, 0.965, 0.055, 0.945)
}

func normalize(positions map[string]point, left, right, top, bottom float64) map[string]point {
	minX, maxX := math.Inf(1), math.Inf(-1)
	minY, maxY := math.Inf(1), math.Inf(-1)
	for _, position := range positions {
		minX, maxX = math.Min(minX, position.x), math.Max(maxX, position.x)
		minY, maxY = math.Min(minY, position.y), math.Max(maxY, position.y)
	}
	width := math.Max(maxX-minX, 1)
	height := math.Max(maxY-minY, 1)
	for id, position := range positions {
		position.x = left + (position.x-minX)/width*(right-left)
		position.y = top + (position.y-minY)/height*(bottom-top)
		positions[id] = position
	}
	return positions
}

func add(a, b point) point                { return point{x: a.x + b.x, y: a.y + b.y} }
func subtract(a, b point) point           { return point{x: a.x - b.x, y: a.y - b.y} }
func scale(value point, by float64) point { return point{x: value.x * by, y: value.y * by} }
func magnitude(value point) float64       { return math.Hypot(value.x, value.y) }

func hash(value string) uint64 {
	h := fnv.New64a()
	_, _ = h.Write([]byte(value))
	return h.Sum64()
}

func abs(value int) int {
	if value < 0 {
		return -value
	}
	return value
}

func round(value float64, places int) float64 {
	power := math.Pow10(places)
	return math.Round(value*power) / power
}

func shortID(id string) string {
	if len(id) <= 8 {
		return id
	}
	return id[:8]
}

func sortedSchemeIDs(schemes map[string]*scheme) []string {
	ids := make([]string, 0, len(schemes))
	for id := range schemes {
		ids = append(ids, id)
	}
	slices.Sort(ids)
	return ids
}

func writeJSON(path string, graph graphFile) error {
	var output *os.File
	if path == "" || path == "-" {
		output = os.Stdout
	} else {
		file, err := os.Create(path)
		if err != nil {
			return err
		}
		defer file.Close()
		output = file
	}
	encoder := json.NewEncoder(output)
	encoder.SetEscapeHTML(false)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(graph); err != nil {
		return err
	}
	return nil
}
