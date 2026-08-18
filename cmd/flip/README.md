# Laderman split-and-flip neighborhood

`cmd/flip` serves a dependency-free visualization of a concrete exact path in
the flip graph of 3x3 matrix-multiplication decompositions. Run it from the
repository root:

```sh
go run ./cmd/flip
```

Then open <http://127.0.0.1:11111>. The default address is exactly `:11111`, so
it listens on every available network interface. The server has no
authentication; use `-addr` to choose another address when desired. Static
assets and graph data are embedded in the binary.

## Displayed sample

Each vertex represents a complete decomposition of the 3x3
matrix-multiplication tensor, rather than one multiplication gate. The gold
construction path contains ten states:

1. the length-23 Laderman decomposition;
2. an exact split that raises the presentation length to 24; and
3. eight invertible, same-length flips.

Reversing the path applies the eight inverse flips and then contracts the split
children to return to Laderman length 23. Here `length` is the number of
rank-one terms in a presentation; it is not a minimality claim.

The visualization also retains eight deterministic alternative neighbors at
each applicable path state and every sampled cross-link among those retained
states. The embedded sample therefore has 76 complete decompositions and 141
transitions. Node details report available movable pairs, their shared modes,
immediate reductions, and factor-incidence component sizes. Recorded path edges
include their removed and added rational factors; sampled cross-links retain
their exact endpoints, shared mode, and basis matrix.

A blue edge is an invertible same-length flip. The orange edge is the upward
split. The dashed green edge is its downward reduction. Use Previous and Next
to replay the construction, click nodes or edges to inspect them, and hide the
alternative neighbors to isolate the known path.

## Exactness and scope

The sample comes from the Branch K candidate and replay at historical checkpoint
`6b451d6`. During generation, every displayed state was expanded and compared
with all 729 rational coordinates of the 3x3 matrix-multiplication tensor. The
focused Go tests additionally check graph integrity and re-expand every local
identity on the recorded path using exact `big.Rat` arithmetic.

This is a finite curated neighborhood. It is not an exhaustive search of a
connected component, a proof of optimality, or a nonexistence argument for
shorter decompositions.

## Check

```sh
go test ./cmd/flip
```
