# Matrix-multiplication flip graphs

`cmd/flip` serves a dependency-free visualization of three exact flip-graph
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

The input data comes from Jakob Moosbauer's
[`jakobmoosbauer/flips`](https://github.com/jakobmoosbauer/flips) repository,
published with the Kauers–Moosbauer flip-graph paper,
which contains the graph data and a GPLv3-or-later program. The generated JSON
records that repository, revision, dataset, and license. Its attribution notice
and the source repository's license are embedded alongside the graph data. This
project does not copy the paper's figure geometry or the authors' C++
implementation.

The importer accepts other three-dimensional matrix-multiplication formats,
fields, source and target representative IDs, and layout iteration counts. It
is intended to consume compatible finite M3 or M4 datasets without changing
the graph schema or renderer.

## M3 over F2: a recorded walk

The second tab displays the milestones of a recorded flip walk from schoolbook
3 by 3 matrix multiplication over `F2` down to a 23-term presentation.
Vertices are raw schemes deduplicated up to term order; unlike the M2 view, no
symmetry quotient is applied. The displayed graph condenses the walk to nine
gold milestones, the schoolbook start plus each state just before and after a
length reduction, with their sampled flip neighborhoods: 85 schemes and 84
edges in total, of which 76 are same-length flips, 4 are length-reducing edges
(one per length level from 27 down to 23), and 4 are dashed segment
pseudo-edges that elide the recorded same-length runs between milestones (35,
37, 72, and 77 flips, the shortest routes inside the recorded sample; with the
reductions, a 225-step route). The milestone flip neighborhoods shrink
monotonically along the descent: 162, 48, 38, 36, 28, 24, 18, 10, and 4
one-flip neighbors. The full walk, not just its milestones, is archived in the
dataset tarball below, and every scheme in that dataset was checked against
all 729 `F2` coordinates of the M3 tensor by re-running the `expand` tool on
it. This is a finite recorded walk: not a component enumeration, an optimality
proof, or a claim of rank below 23, and `length` is a term count, not a
tensor-rank claim.

### Reproducible export

The data was produced by the authors' search program from their
`333-27-mod2.exp` schoolbook scheme, locally instrumented to record every
visited scheme and transition and to accept a fixed random seed. The
instrumentation patch, which also adds an `expand` tool that emits all one-flip
neighbors of a scheme (excluding degenerate factor-zeroing flips, each neighbor
checked against the tensor), is `generate/333walk-trace.patch`; it is GPLv3
like the program it modifies.

The walk was assembled one reduction stage at a time. For each of the four
stages, seeds were swept (1–500 with path cap 5000 for the first two stages,
1–4000 with path cap 2000 for the last two) and the seed reaching a reduction
in the fewest steps was retraced and chained: seeds 346, 78, 1679, and 1858,
taking 35, 37, 72, and 84 flips. Nine milestone states, the schoolbook start
plus each stage's pre- and post-reduction states, were expanded; up to the
first 8 new neighbors per milestone in canonical-name order were retained
(only 4 exist at the length-23 endpoint), together with every sampled edge
between retained states. Seeds fix the walk only for
the same binary and C++ standard library, because the search consults
hash-container iteration order; the exported dataset is therefore archived in
`generate/333walk-27-to-23.tar.gz`, from which the JSON regenerates
deterministically:

```sh
tar -C /tmp -xzf cmd/flip/generate/333walk-27-to-23.tar.gz
go run ./cmd/flip/generate \
  -input /tmp/333walk-27-to-23 \
  -output cmd/flip/static/graph-333.json \
  -format 3,3,3 \
  -field 'F₂' \
  -orbit-quotient=false \
  -condense \
  -target b14852bcb8af10e9 \
  -title 'A recorded descent from schoolbook to 23' \
  -scope 'Milestones of a recorded flip walk from schoolbook 3 by 3 matrix multiplication over F₂ down to a 23-term presentation, with sampled flip neighborhoods at each milestone; dashed segments elide recorded same-length flip runs. Vertices are raw schemes deduplicated up to term order, not symmetry orbits.' \
  -revision e31a0a0f0d2577cee5da047ca7dcae0c61992e40 \
  -license GPL-3.0-or-later
```

## M3 over the rationals: a finite sample

The third tab displays a concrete exact path in a sampled neighborhood of the
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
