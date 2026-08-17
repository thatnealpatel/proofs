# Tensor Gate Lens

A dependency-free static visualizer for exact `<2,2,2>`, `<3,3,3>`, and
characteristic-zero rational `<4,4,4>` matrix-multiplication tensor
decompositions.

## Constructions and exactness

Selectors provide schoolbook rank 8 and Strassen rank 7 for 2×2;
schoolbook rank 27, Laderman rank 23, the exact rank-23 schemes printed in
[arXiv:2607.28676](https://arxiv.org/abs/2607.28676),
[arXiv:2601.05272](https://arxiv.org/abs/2601.05272), and
[arXiv:2508.03857v1](https://arxiv.org/abs/2508.03857v1), and two
Chokaev–Shumkin / Smirnov rank-25 certificates for 3×3; and schoolbook rank 64,
Strassen-squared rank 49,
and the Moran–Schwartz–Yuan rational rank-48 certificate for 4×4. Rank 48 is
not claimed to be optimal. The known rank-47 construction in characteristic
two is deliberately excluded: this workbench uses ordered rational arithmetic,
so its positive/negative cancellation and reinforcement semantics do not model
GF(2).

The generated 3×3 and 4×4 JSON assets come from exact sources in
`Programs/BilinearComplexity`; Go tests independently reconstruct each target.
The three arXiv rank-23 assets are generated directly from the locally obtained
paper TeX: the generator transposes the printed `U^T`, `V^T`, `W^T` tables in
2607.28676 and 2601.05272, and symbolically expands the printed executable
Python algorithm in 2508.03857v1. The related 2606.13408 catalog adds no new
3×3 construction and is intentionally not a picker entry. For the 4×4
appendix, the paper's convention maps to the visualizer as
`A = vec_row_major(O)`, `B = vec_row_major(P)`, and
`C = vec_row_major(transpose(Q))`. The generator establishes this mapping by
exact reconstruction over `QQ`, not by visual inspection.

All client-side coefficient arithmetic, tensor sums, proportionality checks,
and Gaussian-elimination flattening ranks use reduced `BigInt` rational
fractions. Floating point is used only to normalize colors, edge widths, and
SVG positions—not for mathematical decisions or exported values.

## Structure-discovery workbench

The workbench computes pairwise overlap only on unwanted ambient coordinates.
It offers:

- cancellation count, reinforcement count, cancellation-minus-reinforcement,
  binary adjacency, and exact coefficient-weighted interaction;
- all/cancellation-only/reinforcement-only filters, empty-cell hiding, an upper
  triangle, and matrix/graph/both views;
- original certificate order, connected-component order, deterministic label-
  propagation communities, repeated-neighborhood order, degree order, and a
  deterministic breadth-first clustered heuristic;
- a responsive SVG graph with green cancellation and red reinforcement edges,
  pure-target versus unwanted-support nodes, degree-based size, and synchronized
  gold basket selection;
- mechanically detected connected components, isolates, pure-target gates,
  statistical hubs, and exact/near-repeated open neighborhoods. Every structure
  exposes its definition and score and can be highlighted, added, used to
  replace the basket, or copied as JSON.

These graph structures are certificate diagnostics and search cues. Communities,
hubs, neighborhood similarity, and clustered ordering are explicitly heuristic;
the UI does not claim they are invariant or mathematically significant.

Single-click inspects a pair. Double-clicking a pair adds both gates, while
double-clicking a matrix label or graph node adds one. Keyboard focus highlights
associated labels and neighbors; Enter/Space on a focused label or node adds it.
Basket gates and internal edges are gold/prominent, crossing edges are muted,
and unrelated edges fade.

## Basket semantics and verdicts

The basket is the exact selected partial tensor `S`; unselected certificate
gates sum to `T-S`. It reports exact A/B/C flattening ranks, internal/crossing/
outside cancellation and reinforcement counts, unwanted coordinates canceled
inside `S`, and those whose cancellation depends on outside gates.

Verdicts deliberately distinguish:

1. **Proven impossible below k:** maximum flattening rank is at least the `k`
   selected gates, so tensor rank below `k` is impossible.
2. **Exact local rewrite found:** for exactly two gates, two factor modes are
   proven proportional over the rationals and the merged third factor is
   constructed exactly.
3. **Compression not ruled out:** the lower bound is below the selected count;
   this is explicitly not proof of a shorter decomposition.

## Machine-readable exports

Copy buttons emit pretty JSON under versioned schemas
`tensor-gate-lens/{construction,workbench,pair,basket,audit,structure}/v1`.
Exports use original zero-based indices and `P1` human IDs, document row-major
coordinate indexing, and serialize every rational as an ASCII string such as
`-1/3`—never a JSON float. The workbench export includes factors, supports,
exact shared coordinates, graph edges, structures, order, and controls. Basket
exports include `S`, `T-S` semantics, ranks, verdict, rewrite data when present,
and boundary statistics. The workbench button streams its potentially large
JSON export to the local Go server. The server writes into a private per-process
temporary directory and publishes each completed file with a same-directory
rename before reporting its exact path and byte count. Pending exports are size-
and count-limited, expire after inactivity, and are removed at shutdown;
completed exports are retained under bounded count and aggregate-size limits.
This avoids constructing one enormous pretty-printed string or placing it on
the clipboard. Other, smaller export buttons continue to copy pretty JSON to
the clipboard using the modern API with a hidden textarea fallback and visible
success/failure status.

The primary comparison canvas remains the output-routing factor `W`, padded to
schoolbook width. Collapsible views retain full `U`, `V`, `W` factors and the
complete 64-, 729-, or 4096-coordinate tensor audit.

## Regenerate the arXiv 3×3 certificates

With the three downloaded paper sources available, run:

```sh
timeout 300 python3 Programs/BilinearComplexity/export_visualize_arxiv_333.py \
  /path/to/arXiv-2607-28676/main.tex \
  /path/to/arXiv-2601-05272/main.tex \
  /path/to/arXiv-2508-03857-v1/main.tex \
  cmd/visualize/static
```

The extractor requires all printed dimensions, ternary coefficients, and 729
Brent coordinates to verify before writing deterministic compact JSON. It
preserves printed multiplication order and uses row-major A, B, and C factors.

## Regenerate the 4×4 certificates

From the repository root, run:

```sh
timeout 300 sage Programs/BilinearComplexity/export_visualize_444.sage cmd/visualize/static
```

The generator loads the authoritative `q2_strassen2.sage` factors and row
permutation, strictly parses all 48 `O_j`, `P_j`, `Q_j` triples from the local
reference appendix, rejects missing/duplicate/malformed entries, and verifies
all 4096 ambient coordinates over `QQ` before deterministically writing
`strassen-squared.json` and `rational-48.json`. Sage is not needed at visualizer
runtime.

## Run

```sh
go run ./cmd/visualize
```

Open <http://127.0.0.1:11111>. The server listens only on loopback by default,
rejects cross-origin mutation requests, and applies request and storage limits.
A non-loopback `-addr` is refused unless `-allow-remote` is also supplied.
Remote reachability then follows the host firewall and network policy, including
any tailnet policy; the server does not authenticate API clients. Assets and
certificates are embedded in the Go binary, so the server is independent of its
working directory. This remains a reading and exact-audit aid for known
decompositions, not a decomposition search engine or optimizer.
