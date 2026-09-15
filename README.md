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
| §4 Lemma 2 | the cone tree lemma | — | **gap** — needed for Lemma 3 (the route of §5); not formalized yet |
| §5 Lemma 3 | an endpoint stays a diameter endpoint when folding towards it | `isDiamEnd_foldState` | **gap** |
| §6 Lemma 4 | `2r ≤ D` for two farthest vertices | `TreeState.dist_le_diam` | **proved** |
| §7 Lemma 5 | the delayed exchange lemma | `exchange` | **gap** — the mathematical core |
| §8 Prop. 1 | the fixed-endpoint process has a choice-independent length | `LValue_unique` | **proved** from Lemma 3 and Lemma 5 |
| §9 Lemma 6 | `ecc x = max (d x u) (d x v)` for a diameter `u v` | `dist_le_max_dist_ends` | **proved** |
| §10 Lemma 7 | two diameter endpoints have a common opposite | `exists_common_opposite` | **proved** from Lemma 6 |
| §10 Prop. 2 | all diameter endpoints give the same value | `LValue_endpoint_independent` | **gap** (needs Lemma 7 and Lemma 3) |
| §11–12 Prop. 3 | one operation decreases the value by exactly one | `Phi_step` | **proved** from Prop. 1, Prop. 2 and Lemma 3 |
| §13 | conclusion | `fold_count_unique` | **proved** |

Besides the numbers of `REF.md`, the development proves the supporting facts that the process
needs: every fold removes at least one vertex (`DiamPath.foldAlive_card_lt`,
`FoldStep.card_lt`), so folding sequences are finite (`FoldSeq.card_le`) and the fixed-endpoint
process terminates (`Phi_exists`); and from any diameter endpoint there is a diameter path starting
there (`exists_diamPath_at`).

## What is left, precisely

Three declarations still contain a `sorry`; they are exactly the mathematical content of `REF.md`
that is not yet formalized:

1. `isDiamEnd_foldState` (`OhtoaiTreeProof/Exchange.lean`) — Lemma 3: after folding, every branch
   hanging at the `j`-th vertex `q j` of the folded diameter has height at most `j` (the branches at
   `p j` and at `p (D-j)` both have height at most `min j (D-j) = j` by Lemma 1); `REF.md` §4's cone
   lemma (Lemma 2) then shows that `q 0` is still a diameter endpoint, since for vertices `x`, `y`
   hanging at `q i`, `q j` one has `d x y = h x + |i - j| + h y ≤ j + h y = d (q 0) y`.  The
   formalization needs the cone lemma for a general tree (a projection/height formula for the
   vertices of a tree relative to a path) on top of the triangle-type bounds already proved
   (`DiamPath.dist_eq_dist_add`, `DiamPath.fold_dist_le`).
2. `exchange` (`OhtoaiTreeProof/Exchange.lean`) — Lemma 5, the delayed exchange lemma: the two
   folds towards `s` along two different diameters differ only inside a ball around the branching
   point of the two diameters, and that ball is destroyed by the first few further folds.
3. `LValue_endpoint_independent` (`OhtoaiTreeProof/MainTheorem.lean`) — Proposition 2.  Here the
   formalization has to do slightly more than `REF.md`: `REF.md` says that folding along the same
   diameter `a`–`b` towards `a` and towards `b` gives "the same abstract quotient tree", which is
   true up to isomorphism — the two folded states differ by the permutation `p i ↦ p (D - i)`
   of the diameter.  Formalizing that step requires an isomorphism-invariance lemma for the
   process (a `StateIso` structure, transportation of `DiamPath`/`FoldStep`/`LValue` along a
   permutation, and the commutation of `rep` with it), which is not yet in the development.

Every state of the process is now *proved* to be a tree (`DiamPath.foldGraph_isAcyclic`, `REF.md`
§2), so the only assumptions left in the development are the three statements above.

## Building

The project uses `leanprover/lean4:v4.34.0` and Mathlib (already present in `.lake/packages`).

```sh
lake build                      # builds the library and the `ohtoai-tree-proof` executable
lake build OhtoaiTreeProof      # builds the library only
```

`Main.lean` prints a short description of the formalized statement.  The module layout follows the
proof: `Basic.lean` (states, diameters, folding, and the counting argument of §2), `Progress.lean` (folding decreases the number of
vertices), `PathExists.lean` (a diameter starting at a given endpoint), `Diameter.lean` (the metric
lemmas about a diameter: `REF.md` Lemmas 1, 6 and 7), `Exchange.lean` (`REF.md` Lemmas 3 and 5, and
the derivation of Proposition 1 and of `Phi_exists`), `MainTheorem.lean` (the value `Phi`, the
propositions, and the main theorem).

Everything except the three `sorry`s above is checked by Lean: `#print axioms
OhtoaiTreeProof.fold_count_unique` reports only `propext`, `Classical.choice` and `Quot.sound`
besides the `sorryAx` contributed by the three open statements, and
`#print axioms OhtoaiTreeProof.DiamPath.foldGraph_isAcyclic` reports no `sorryAx` at all.  The development was also checked
against the computational experiments in `research/verify_invariance.py` (exhaustive over all
labelled trees with at most 8 vertices, plus random trees up to 14 vertices): every complete
folding process has the same length, and every fold produces a tree.
