- You **MUST** set `set_option autoImplicit false`; a typo under autoImplicit becomes a phantom
  implicit variable and the theorem quantifies over the wrong thing.
- You **MUST** exhibit satisfiability before committing a theorem: instantiate every hypothesis
  jointly at one concrete model (an `example` is enough). Contradictory hypotheses prove anything
  and no linter catches them.
- You **MUST** check that every quantified domain is nonempty at the intended parameters;
  `∀ x : Fin 0`, `∀ x ∈ (∅ : Set _)`, `Finset.range 0`, and `n = 0` degeneracies are vacuously true.
- You **MUST** guard totalized operators in statements — `Nat` subtraction, `/`, `Real.sqrt`,
  `Real.log`, `deriv`, `tsum`, `iInf`/`iSup` — with the hypothesis that keeps them off their junk
  value, or the statement is about the junk.
- You **MUST** cast before subtracting: `↑a - ↑b`, never `↑(a - b)` on `Nat`.
- You **MUST NOT** state `iInf x > k, f x`-style bounded extrema; the inner `iInf` over an empty
  `Prop` collapses to the default. Index by the subtype (`⨅ x : Set.Ioi k, f x`) instead.
- You **MUST** include distinctness and nontriviality side conditions the informal claim assumes:
  `∃ x y, x ≠ y ∧ f x = f y`, exclusion of `0`, `Nontrivial`, `1 < n`.
- You **MUST NOT** let the answer appear as a free parameter pinned by a hypothesis
  (`(answer : ℕ) (h : answer = 42) : answer = 42` asserts nothing).
- You **MUST NOT** use autoParam (`(h : P := by tac)`) in statements; obligations discharged
  silently are obligations the reader never sees.

- You **MUST** accompany every new `def` with ground-truth checks (`example : myDef 3 = 7 := rfl`,
  `#eval` at boundary inputs) or a proved equivalence to the Mathlib-standard notion; a correct
  proof of a wrong definition compiles clean.
- You **MUST** run `#check @thm` on any theorem stated inside a `variable` section and confirm the
  full signature is the intended claim; section variables silently join the statement.
- You **MUST** audit degeneracy of assumed instances: `[Subsingleton α]`, `[CharP R 1]`, and an
  instance argument on a concrete type (`[Ring ℤ]`) either trivialize the claim or split it from
  the canonical structure.
- You **MUST** use `<` and `≤` in statements, never `>` or `≥`; Mathlib's simp set and lemma
  grammar normalize to the former and the latter strands the statement outside the API.

- You **MUST** treat a proof as complete only when the file compiles with no `sorry`, no errors,
  and `#print axioms` reports a subset of `{propext, Classical.choice, Quot.sound}`.
- You **MUST NOT** declare `axiom`s.
- You **MUST NOT** use `@[implemented_by]`, `@[extern]`, or `@[csimp]` in proof-bearing code; with
  `native_decide` they enter the trusted base, and `@[csimp]` axiom-dependencies do not surface in
  downstream `#print axioms` (lean4#7463).
- You **MUST** prefer `decide` to `native_decide`; use `native_decide` only when kernel reduction
  is infeasible, and note the enlarged trust surface at the use site.
- You **MUST NOT** use `partial def` for anything a theorem mentions; it is opaque to the logic
  and theorems about it reduce to inhabitation.
- You **MUST NOT** define local notation overriding standard operators, instances that reverse
  standard semantics, or `open`s that shadow standard names; the kernel checks the elaborated
  statement, the reader reads the sugar, and drift between them is invisible in review.

- You **MUST NOT** leave a nonterminal bare `simp`; squeeze to `simp only [...]`. Terminal `simp`
  stays unsqueezed.
- You **MUST** bound `convert` with `using n`; unbounded congruence descends into goals like
  `HAdd.hAdd = HMul.hMul`.
- You **MUST NOT** use `erw`; it papers over a missing API lemma — state the lemma.
- You **MUST NOT** mix cardinality APIs (`Finset.card`, `Fintype.card`, `Nat.card`, `Set.ncard`)
  in one statement; each is `0` in a different degenerate case.
- You **MUST** use `let` (or `set`) for data and `have` only for proofs; `have` forgets the value.

- You SHOULD state at the weakest typeclass that supports the claim: `Type*` not `Type`,
  `[Finite α]` not `[Fintype α]` unless a `Finset` is computed, no `[DecidableEq α]` leaked from
  proof internals into the statement, `[CommRing]` before `[Field]`.
- You SHOULD spell concepts in Mathlib normal form (`s.Nonempty`, `x ≠ ⊥` in hypotheses,
  `⊥ < x` in conclusions) so coverage and redundancy stay auditable.
- You SHOULD treat `ENNReal`/`ENat` arithmetic as non-cancellative (`∞ - ∞ = 0`, `0 * ∞ = 0`) and
  carry the explicit `≠ 0` / `≠ ⊤` hypotheses the API lemmas demand.
- You SHOULD pass `generalizing` when the induction hypothesis must quantify over auxiliary
  variables, and pick the induction principle to match the recursion (structural vs
  `Nat.strong_rec_on` vs `Nat.le_induction` with base at `k`).
- You SHOULD use `simp_rw` or `conv` for rewrites under binders; `rw` cannot enter a lambda.

- You **MUST** write a docstring on every public theorem and definition stating the informal
  claim; the statement audit is the scarce resource and the docstring is its entry point.
- You **MUST** keep paper-theorem aliases stable (`thm_3_2`, `cor_3_4`) once a manuscript refers
  to them.
- You SHOULD follow the Mathlib naming grammar (`C_of_A_of_B`, `add_le_add_left`) so the name
  encodes the statement shape.
- You SHOULD structure proofs as named checkpoints — `have hcard : s.card = n`, `suffices`,
  `calc` for relation chains, `·` focus dots per subgoal — a reader verifies each checkpoint
  independently.
- You SHOULD NOT chain on `this`, close goals with `assumption` or `‹_›`, or build large
  structures with positional `⟨_, _, _⟩`; unnamed references force the reader to replay the
  context.
- You SHOULD confine magic closers (`omega`, `linarith`, `aesop`, `grind`) to leaves whose
  content the surrounding checkpoints already make evident; a closer at a load-bearing step
  hides the mathematics.

```lean
-- wrong: vacuous — no x satisfies both hypotheses
theorem bad (x : ℤ) (h1 : x < 0) (h2 : 0 < x) : P x := absurd (h1.trans h2) (lt_irrefl x)

-- wrong: trivially witnessed by y = x
theorem bad' : ∃ x y : α, f x = f y := ⟨a, a, rfl⟩

-- right: the side condition carries the content
theorem good (h : ¬Function.Injective f) : ∃ x y, x ≠ y ∧ f x = f y := ...
```

```lean
-- wrong: statement is about Nat truncation, not the intended difference
theorem bad (a b : ℕ) : (↑(a - b) : ℤ) ≤ a := ...

-- right: cast first, subtract in ℤ, and the claim needs no guard
theorem good (a b : ℕ) : (↑a - ↑b : ℤ) ≤ a := ...
```
