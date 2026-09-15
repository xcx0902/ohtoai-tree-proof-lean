# ohtoai-tree-proof

A Lean 4 / Mathlib formalization of the tree-folding theorem proved in [`REF.md`](REF.md).

The proof chain is complete: there are no admitted proofs or additional axioms. The default build
checks the axiom dependencies of the exchange lemma and the main results.

## The theorem

Fix a finite tree `G`.  Choose a diameter `d₀ … d_D` of `G` and fold along it: identify the
mirror-image pairs `d_i ~ d_{D-i}`, take the quotient graph, and repeat with the tree that is
left, until a single vertex remains.  **The number of folding operations does not depend on the
diameters chosen.**

`REF.md` proves this by fixing one diameter endpoint `s`, showing that `s` stays a diameter
endpoint forever (Lemma 3), formalizing the "always fold towards `s`" process, and proving that
*every* folding operation decreases the number of operations of that process by exactly one
(Propositions 1–3).  The Lean development follows the same route and reduces the theorem to a
small number of statements, listed below.

The problem is ICPC 2026 Asia East Continent Online Contest (II), problem F
["Folding Game of Ohto Ai"](https://qoj.ac/problem/20241) (also Codeforces Gym 106701 F); see
[`research/WEB-RESEARCH.md`](research/WEB-RESEARCH.md) for the source, the official (Chinese)
tutorial, and an independent computational verification of the invariance statement.  The official
tutorial states the invariance in one sentence and gives no invariant, so the exchange-lemma route
of `REF.md` is the only published argument.

## How the process is modelled

Every tree occurring in the process is represented as a graph on the *same* ambient vertex type
`V`, together with a finset `alive` of its vertices; vertices outside `alive` are isolated.  This
keeps the statement "all complete processes have the same length" expressible as a relation on a
fixed type.

| Declaration | Meaning |
| --- | --- |
| `TreeState V` | a tree with vertex set `alive` (`adj_alive`, `connected`, `acyclic`) |
| `DiamPath S` | a diameter of `S`, listed as an injective path `p 0, …, p D` whose endpoints realize `S.diam` |
| `DiamPath.rep` | the canonical representative map of the folding: `p i ↦ p (min i (D - i))` on the diameter, the identity elsewhere |
| `DiamPath.foldAlive`, `foldGraph`, `foldState` | the vertices, the graph and the state obtained by folding |
| `FoldStep S S'` | `S'` is obtained from `S` by folding along *some* diameter |
| `FoldSeq S S' n` | `S'` is obtained from `S` by `n` folding operations, no operation being taken from a state with at most one vertex |
| `IsDiamEnd S s` | `s` is a diameter endpoint of `S` |
| `FoldStepAt s`, `FoldSeqAt s`, `LValue S s n` | the fixed-endpoint process: fold along a diameter that starts at `s` |
| `IsSingle S` | `S.alive.card ≤ 1` |

`rep` is idempotent (`rep_idem`), which is what lets the folded tree be written as a graph on the
same vertex type — this is also the formal counterpart of "taking the quotient" in `REF.md` §1.

## Main results

| Lean declaration | Statement | Status |
| --- | --- | --- |
| `fold_count_unique` | Any two complete folding processes of a state have the same number of operations. | **Proved** from `Phi_step` |
| `fold_count_unique_of_isTree` | The same for a plain tree `G : SimpleGraph V` with `G.IsTree` (the form of `REF.md`). | **Proved** |

The assembly is complete and mirrors `REF.md` §11–13:

* `Phi S` — the value of the process (`Phi_eq_zero_of_single`, `Phi_eq_of_foldSeq`:
  a process of length `n` satisfies `Phi S = Phi S' + n`);
* `LValue_Phi` — the value is realised by the fixed-endpoint process towards *any* diameter
  endpoint of `S`;
* `Phi_step` (Proposition 3) — **proved** from Proposition 1, Proposition 2 and Lemma 3;
* `fold_count_unique` — **proved** from `Phi_step` by induction along the folding sequence.

## Status of the individual lemmas of `REF.md`

| `REF.md` | Content | Lean declaration | Status |
| --- | --- | --- | --- |
| §1 | the folding operation, the quotient | `DiamPath.rep`, `foldAlive`, `foldGraph`, `foldState` | **proved** |
| §2 | the folded graph is again a tree | `foldGraph_isAcyclic` | **proved** (the counting argument: `|alive| = |foldAlive| + ⌈D/2⌉` vertex-wise, `|E'| + ⌈D/2⌉ ≤ |E|` edge-wise, connectivity, and `|E| + 1 = |alive|`) |
| §3 Lemma 1 | a branch at `p i` has height `≤ min i (D-i)` | `dist_le_min_index` | **proved** |
| §4 Lemma 2 | the cone tree lemma | `Cone.dist_le_max`, `Cone.exists_dist_eq` | **proved** (for an arbitrary finite acyclic graph and a path) |
| §5 Lemma 3 | an endpoint stays a diameter endpoint when folding towards it | `isDiamEnd_foldState` (`Cone.lean`) | **proved** |
| §6 Lemma 4 | `2r ≤ D` for two farthest vertices | `TreeState.dist_le_diam` | **proved** |
| §7 Lemma 5 | the delayed exchange lemma | `exchange` | **proved** (synchronized phase and common endgame) |
| §8 Prop. 1 | the fixed-endpoint process has a choice-independent length | `LValue_unique` | **proved** from Lemma 3 and Lemma 5 |
| §9 Lemma 6 | `ecc x = max (d x u) (d x v)` for a diameter `u v` | `dist_le_max_dist_ends` | **proved** |
| §10 Lemma 7 | two diameter endpoints have a common opposite | `exists_common_opposite` | **proved** from Lemma 6 |
| §10 Prop. 2 | all diameter endpoints give the same value | `LValue_endpoint_independent` | **proved** (from Lemma 7; the case `d (s,t) = diam` folds along the common diameter in the two directions using `lValue_foldState_reverse` — the formal counterpart of "folding towards the two ends of a diameter gives the same quotient tree" — identifies the two lengths by Proposition 1, and the remaining case is reduced by Lemma 7) |
| §11–12 Prop. 3 | one operation decreases the value by exactly one | `Phi_step` | **proved** from Prop. 1, Prop. 2 and Lemma 3 |
| §13 | conclusion | `fold_count_unique` | **proved** |

Besides the numbers of `REF.md`, the development proves the supporting facts that the process
needs: every fold removes at least one vertex (`DiamPath.foldAlive_card_lt`,
`FoldStep.card_lt`), so folding sequences are finite (`FoldSeq.card_le`) and the fixed-endpoint
process terminates (`Phi_exists`); and from any diameter endpoint there is a diameter path starting
there (`exists_diamPath_at`).

## The Exchange Proof

`exchange` in `OhtoaiTreeProof/Exchange.lean` is proved by
`DiamPath.synchronized_exchange` in `OhtoaiTreeProof/SyncEndgame.lean`.
For two diameters from `s`, let `r` be the length of their tails after the last common vertex.

* The initial geometry and `SyncCtx` are established in `ExchangeLemma5.lean`, `Phase1.lean`,
  `Phase2.lean`, `CommonDist.lean`, and `Sync.lean`. The two folded states agree on the common
  part, their difference region lies within distance `2r` of `s`, and both retain a leg of
  length `2r`.
* `SyncStep.lean` proves `SyncCtx.step`: while the diameter exceeds `2r`, both states can fold
  along the same diameter in the common part. The entire invariant, including the explicit
  composite quotient map, is preserved. `SyncCtx.reach_scale` uses strong induction on the
  number of live vertices to reach diameter exactly `2r`.
* `SyncEndgame.lean` proves `legAt_rep_comp`: folding the surviving legs after the synchronized
  phase gives equal composite maps on the original vertices. `SyncCtx.commonEndgame` derives
  equality of both live sets and graphs, hence literal equality of the final states.
* The common state admits a terminating fixed-endpoint process, so both completions have equal
  length. When `r = 0`, the first-fold states are already equal; this also covers singleton
  results, where no further fold is legal.

The synchronized phase is not asserted to take `r` steps: its termination follows from strict
decrease of the live vertex count. The persistent legs prevent the diameter from dropping below
`2r` before the common endgame.

## Build and Audit

```sh
lake build
lake env lean OhtoaiTreeProof/AxiomAudit.lean
lake exe ohtoai-tree-proof
```

`AxiomAudit.lean` is imported by the library root and therefore checked by the default build.
Its `#guard_msgs` checks assert that `exchange`, `LValue_unique`, `Phi_step`,
`fold_count_unique`, and `fold_count_unique_of_isTree` depend only on `propext`,
`Classical.choice`, and `Quot.sound`. An unexpected axiom, including `sorryAx`, fails the build.
Every state of the process is also proved to be a tree (`DiamPath.foldGraph_isAcyclic`, `REF.md` §2).

The development was also checked
against the computational experiments in `research/verify_invariance.py` (exhaustive over all
labelled trees with at most 8 vertices, plus random trees up to 14 vertices): every complete
folding process has the same length, and every fold produces a tree.
