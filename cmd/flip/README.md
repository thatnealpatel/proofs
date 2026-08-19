# Matrix-multiplication flip graphs

`cmd/flip` serves a dependency-free visualization of two exact flip-graph
datasets. Run it from the repository root:

```sh
go run ./cmd/flip
```

Then open <http://127.0.0.1:11111>. The default address is exactly `:11111`, so
it listens on every available network interface. The server has no
authentication; use `-addr` to choose another address when desired. Static
assets and graph data are embedded in the binary. Use the zoom controls or
mouse wheel/trackpad to spread graph positions while nodes and edge strokes
retain their display size, drag empty graph space to pan, and select **Fit** to
restore the complete frame.

## M2 over F2: a complete component

The default view is the component containing schoolbook multiplication in the
rank-at-most-8 flip graph for 2 by 2 matrix multiplication over `F2`. Vertices
are symmetry orbits of complete presentations, not individual multiplication
gates or raw schemes. The generated graph contains:

- 272 orbit vertices and 1,183 deduplicated orbit edges;
- 1,176 same-length flip edges, including 40 self-loops;
- seven length-decreasing edges from length 8 to length 7; and
- diameter 12.

The unique length-7 vertex is Strassen's orbit. The highlighted route is a
deterministically chosen shortest schoolbook-to-Strassen path of eight edges.
It is not geometry copied from the paper figure. One additional length-8 orbit
is isolated in the published dataset and is therefore outside the displayed
schoolbook component. The source does not claim that no further components
exist.

### Reproducible import

`generate` is a format-parameterized importer for the authors' `.exp`
representatives and `edges.txt`. It parses factor supports, canonicalizes
undirected endpoint pairs, retains self-loops, classifies edges from endpoint
presentation lengths, extracts the source component, computes graph statistics
and a shortest path, and emits deterministic `flip-graph/v1` JSON with a fresh
force-directed layout.

With the authors' repository checked out at `/tmp/flips-paper`, reproduce the
embedded M2 graph with:

```sh
go run ./cmd/flip/generate \
  -input /tmp/flips-paper/222flipgraph_rank8 \
  -output cmd/flip/static/graph-222.json \
  -format 2,2,2 \
  -field F2 \
  -title 'The complete small case' \
  -scope 'The schoolbook component of the rank-at-most-8 orbit flip graph for 2 by 2 matrix multiplication over F2.' \
  -revision e31a0a0f0d2577cee5da047ca7dcae0c61992e40 \
  -license GPL-3.0-or-later
```

The input data comes from Jakob Moosbauer and Michael Poole's
[`jakobmoosbauer/flips`](https://github.com/jakobmoosbauer/flips) repository,
which contains the graph data and a GPLv3-or-later program. The generated JSON
records that repository, revision, dataset, and license. Its attribution notice
and the source repository's license are embedded alongside the graph data. This
project does not copy the paper's figure geometry or the authors' C++
implementation.

The importer accepts other three-dimensional matrix-multiplication formats,
fields, source and target representative IDs, and layout iteration counts. It
is intended to consume compatible finite M3 or M4 datasets without changing
the graph schema or renderer.

## M3 over the rationals: a finite sample

The second tab displays a concrete exact path in a sampled neighborhood of the
3 by 3 matrix-multiplication flip graph over the rationals. Each vertex is a
complete presentation of the M3 tensor. The gold construction path contains:

1. the length-23 Laderman presentation;
2. an exact split that raises the presentation length to 24; and
3. eight invertible, same-length flips.

Reversing the path applies the eight inverse flips and then contracts the split
children to return to Laderman length 23. Here `length` means the number of
rank-one terms in a presentation; it is not a claim about tensor rank or
minimality. The eight flips are a finite checkpoint, not an optimum or terminal
state.

The visualization retains eight deterministic alternative neighbors at each
applicable path state and every sampled cross-link among those retained states.
It has 76 complete presentations and 141 transitions. Recorded path edges
include their removed and added rational factors; sampled cross-links retain
their exact endpoints, shared mode, and basis matrix.

The Branch K sample comes from the candidate and replay at historical checkpoint
`6b451d6`. During generation, every displayed state was expanded and compared
with all 729 rational coordinates of the M3 tensor. This is a finite curated
neighborhood, not an exhaustive component search, optimality proof, or
nonexistence result.

## Static checks

```sh
node --check cmd/flip/static/app.js
node --test cmd/flip/static/app.test.js
go test ./cmd/flip/...
```
