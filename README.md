# ohtoai-tree-proof

A Lean 4 / Mathlib formalization of the tree-folding theorem proved in [`REF.md`](REF.md).

## The theorem

Fix a finite tree `G`.  Choose a diameter `d₀ … d_D` of `G` and fold along it: identify the
mirror-image pairs `d_i ~ d_{D-i}`, take the quotient graph, and repeat with the tree that is
left, until a single vertex remains.  **The number of folding operations does not depend on the
diameters chosen.**

`REF.md` proves this by fixing one diameter endpoint `s`, showing that `s` stays a diameter
endpoint forever (Lemma 3), formalizing the "always fold towards `s`" process, and proving that
*every* folding operation decreases the number of operations of that process by exactly one
(Propositions 1–3).  The Lean development follows the same route.

The problem is ICPC 2026 Asia East Continent Online Contest (II), problem F
["Folding Game of Ohto Ai"](https://qoj.ac/problem/20241) (also Codeforces Gym 106701 F); see
[`research/WEB-RESEARCH.md`](research/WEB-RESEARCH.md) for the source, the official (Chinese)
tutorial, and an independent computational verification of the invariance statement.

## How the process is modelled

Every tree occurring in the process is represented as a graph on the *same* ambient vertex type
`V`, together with a finset `alive` of its vertices; vertices outside `alive` are isolated.  This
keeps the statement "all complete processes have the same length" expressible as a relation on a
fixed type.

* `TreeState V` — a tree with vertex set `alive` (`adj_alive`, `connected`, `acyclic`).
* `DiamPath S` — a diameter of `S`, listed as an injective path `p 0, …, p D` whose endpoints
  realize `S.diam`.
* `DiamPath.rep` — the canonical representative map of the folding: `p i ↦ p (min i (D - i))` on
  the diameter, the identity elsewhere.  It is idempotent (`rep_idem`), which is what lets the
  folded tree be written as a graph on the same type.
* `DiamPath.foldAlive`, `DiamPath.foldGraph`, `DiamPath.foldState` — the vertices, the graph and
  the state obtained by folding.  Two live representatives are adjacent when they are the images
  of the two ends of an edge of the current tree.
* `FoldStep S S'` — `S'` is obtained from `S` by folding along *some* diameter.
* `FoldSeq S S' n` — `S'` is obtained from `S` by `n` folding operations; no operation is taken
  from a state with at most one vertex, so a sequence stops exactly when a single vertex is left.
* `IsSingle S` — `S.alive.card ≤ 1`.

The fixed-endpoint process of `REF.md` is `FoldSeqAt s` (`FoldStepAt s` folds along a diameter
whose first vertex is `s`), and `LValue S s n` says that some complete process folding always
towards `s` uses exactly `n` operations.

## Main results

| Lean declaration | Statement | Status |
| --- | --- | --- |
| `OhtoaiTreeProof.fold_count_unique` | Any two complete folding processes of a state have the same number of operations. | **Proved** from `Phi_step` (the single gap in the assembly) |
| `OhtoaiTreeProof.fold_count_unique_of_isTree` | The same statement for a plain tree `G : SimpleGraph V` with `G.IsTree` (the form of `REF.md`). | **Proved** from the previous one |

The assembly is complete: `Phi` (the value of the process) is defined, `Phi` vanishes on
single-vertex states (`Phi_eq_zero_of_single`), and `Phi_eq_of_foldSeq` shows by induction on the
folding sequence that a process of length `n` satisfies `Phi S = Phi S' + n`; the main theorem
follows immediately.  What is *not* yet proved are the three mathematical statements that make
`Phi` well defined and make it decrease:

```lean
-- REF.md Proposition 1 (REF.md §8, proved there via the exchange Lemma 5 of §7):
theorem LValue_unique : IsDiamEnd S s → FoldSeqAt s S S₁ n → FoldSeqAt s S S₂ m →
    IsSingle S₁ → IsSingle S₂ → n = m

-- REF.md Proposition 2 (REF.md §10): the fixed-endpoint value does not depend on the endpoint
theorem LValue_endpoint_independent : IsDiamEnd S s → IsDiamEnd S t → LValue S s n → LValue S t n

-- REF.md Propositions 2 and 3 (REF.md §12): every operation decreases the value by exactly one
theorem Phi_step : FoldStep S S' → 2 ≤ S.alive.card → Phi S = Phi S' + 1

-- termination/existence of the fixed-endpoint process (uses REF.md Lemma 3)
theorem Phi_exists : ¬S.alive.card ≤ 1 → ∃ s, IsDiamEnd S s ∧ ∃ n, LValue S s n
```

## Status of the individual lemmas of `REF.md`

| `REF.md` | Content | Lean | Status |
| --- | --- | --- | --- |
| §1 | definitions of the folding operation | `DiamPath`, `foldAlive`, `foldGraph`, `foldState` | done |
| §2 | the folded graph is again a tree | `DiamPath.foldGraph_isAcyclic` | **gap** (connectivity `fold_reachable` is proved; acyclicity is the counting argument of §2) |
| §3 Lemma 1 | a branch hanging at `p i` has height `≤ min i (D-i)` | `dist_le_min_index` (in progress) | **gap** |
| §4 Lemma 2 | the cone tree lemma | — | not started |
| §5 Lemma 3 | an endpoint stays a diameter endpoint when folding towards it | — | not started (used by `Phi_exists` and `Phi_step`) |
| §6 Lemma 4 | `2r ≤ D` for two farthest vertices | `TreeState.dist_le_diam` | done (it is the definition of the diameter) |
| §7 Lemma 5 | the exchange (synchronisation) lemma | — | not started — this is the mathematical core |
| §8 Prop. 1 | the fixed-endpoint process has a choice-independent length | `LValue_unique` | **gap** (= Lemma 5) |
| §9 Lemma 6 | `ecc x = max (d x u) (d x v)` for a diameter `u v` | `dist_le_max_dist_ends` (in progress) | **gap** |
| §10 Lemma 7, Prop. 2 | all diameter endpoints give the same value | `LValue_endpoint_independent` | **gap** |
| §11–12 Prop. 3 | one operation decreases the value by exactly one | `Phi_step` | **gap** |
| §13 | conclusion | `fold_count_unique` | **proved from the above** |

Everything that is not listed as a gap is fully proved: there is no `sorry` anywhere else, and in
particular the definitions, the folding map and its properties, connectivity of the folded tree,
the value `Phi`, its behaviour along a folding sequence, and the main theorem's reduction to
`Phi_step` are complete.  A `sorry`-free proof of `Phi_step` (via Lemma 5 and Lemma 3) is the
remaining mathematical work; `research/WEB-RESEARCH.md` records that the official tutorial of the
contest only states the invariance in one sentence and gives no invariant, so the exchange lemma
route of `REF.md` is the only published argument.

## Building

The project uses `leanprover/lean4:v4.34.0` and Mathlib (already present in `.lake/packages`).

```sh
lake build                      # builds the library and the `ohtoai-tree-proof` executable
lake build OhtoaiTreeProof      # builds the library only
```

`Main.lean` prints a short description of the formalized statement.  The development was also
checked against the computational experiments in `research/verify_invariance.py` (exhaustive over
all labelled trees with at most 8 vertices, plus random trees up to 14 vertices): every complete
folding process has the same length, and every fold produces a tree.
