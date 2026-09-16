# Proof Audit

Date: 2026-09-16. Toolchain: Lean 4.34.0. Mathlib revision:
`a4c43ae1f99cb19aabfa62308b3ea75a340e470f` (from `lake-manifest.json`).

## Conclusion

No mathematical error or unsound dependency was found in the formal proof of
`fold_count_unique_of_isTree`. Its statement and the definitions it uses match the
finite, nonempty tree-folding theorem in `REF.md`, including arbitrary diameter
orientations and the prohibition on counted operations from a singleton.

The original project built successfully before any changes. The refactor preserves
the existing public theorem statements and the definitions of the folding process.

## Findings

### Incorrect historical proof comments

The old closing sketches in `Phase1.lean` and `ExchangeLemma5.lean` proposed induction
on diameter, even claiming that synchronized folds lower it by two. Diameter need
not strictly decrease: folding two leaves of a star with four leaves leaves diameter
two. The actual proof in `SyncCtx.reach_scale_aux` correctly uses the live vertex
count, with persistent legs establishing the lower bound on the stopping diameter.

The old sketches in `Phase1.lean` and `ExchangeProof.lean` also proposed an
unconditional common *further fold*. This is false when the initial tree is a single
edge, because its first fold leaves a singleton. The actual implementation handles
zero tail length by equality of the folded states, without another operation.
`Phase3.lean` contained an obsolete implementation roadmap, including references to
results not declared there. These comments have been corrected or replaced with
references to the completed proof.

Additional comment errors were corrected: `badIdx` has `D - D / 2` elements, not
`D / 2` for odd `D`; the walk through common attachment points need not be the
geodesic; and a set avoided by the diameter is disjoint from it, not containing it.
None of these errors affected the checked proof terms.

### Modeling conventions needed clarification

`TreeState` allows an empty live set, and `IsSingle` means cardinality at most one.
This does not weaken the theorem about actual trees: Mathlib's `IsTree` includes
nonemptiness through `Connected`, and every fold retains its first endpoint. Added
`FoldSeq.alive_nonempty` and `FoldSeq.card_eq_one` make the correspondence explicit.

`FoldStep` includes the singleton identity image; legality is imposed by the
cardinality premise of `FoldSeq.step`. `FoldSeqAt` allows unfinished prefixes, despite
its old comment calling every sequence maximal. Completeness additionally requires
`IsSingle` at the end. The comments and README now distinguish these notions.

Added `FoldSeqAt.toFoldSeq`, `exists_complete_foldSeq`, and
`exists_complete_foldSeq_of_isTree` explicitly connect fixed-endpoint existence to
unrestricted legal completions ending at exactly one vertex. Thus the main
uniqueness theorem is not vacuous.

### Auxiliary declarations were outside the original axiom guards

The original guarded axiom checks covered the main dependency chain, but not every
auxiliary result. `AxiomAudit.lean` now checks declarations by their owning project
module, including helpers unused by the main result. The only permitted axioms are
`propext`, `Classical.choice`, and `Quot.sound`. Boundary examples also check that
prefixes are permitted, positive-length sequences cannot start at a singleton,
and a sequence from a nonempty state has fewer steps than initial live vertices.

## Semantic Checks

| Area | Checked correspondence |
| --- | --- |
| `TreeState`, `diam` | Acyclicity and connectivity on live vertices; maximum distance taken only over live vertices. |
| `DiamPath` | Injective adjacent sequence of live vertices; endpoints realize the diameter; path length equals diameter. |
| `rep`, `foldAlive` | Mirror-index formula, off-path identity, idempotence, and surviving fixed points equal to image representatives. |
| `foldGraph` | Edges are original edge images with unequal representatives; loops are discarded and adjacency is a proposition. |
| `foldState` | Connectivity and acyclicity are proved, not assumed; positive-length folds strictly reduce live vertex count. |
| Endpoint preservation | The cone lemma and branch-height bounds establish that the retained endpoint remains a diameter endpoint. |
| Delayed exchange | Common geodesics establish common distances; the invariant preserves legs and equal diameters; termination uses vertex count. |
| Endgame | Pointwise equality of composite maps on every original vertex gives equality of both vertex sets and edge relations. |
| Reversal | Opposite representative choices are compared by a rooted isomorphism, not equality of retained labels. |
| Final assembly | Existence precedes uniqueness; exchange implies fixed-endpoint uniqueness; endpoint independence yields the one-step potential decrease. |

## Refactoring

- Reused `LValue_exists_aux` instead of maintaining a second identical induction.
- Moved `GeodAvoid.dist_eq` to `Sync.lean` and reused it for common-distance proofs.
- Added `DiamPath.two_le_card`, replacing repeated endpoint/cardinality arguments
  in `CommonEndgame.card_le` and the synchronized induction.
- Reused the existing image-walk lemmas in the cone proof.
- Simplified the opposite-endpoint argument by equating the original completion
  length directly with a constructed completion, avoiding subtraction and successor
  decomposition.
- Strengthened the sequence bound to `S'.alive.card + n <= S.alive.card` and derived
  the existing weaker bound from it.

## Verification

The following checks passed:

```sh
lake build
lake env lean -t 0 OhtoaiTreeProof/AxiomAudit.lean
lake env leanchecker --fresh OhtoaiTreeProof
lake exe ohtoai-tree-proof
python3 research/verify_model.py --max-n 7
python3 research/check_lemma5_strategy.py
git diff --check
```

All 18 files in `OhtoaiTreeProof/` are included transitively in the library build.
The fresh checker replays the project and imported declarations into a fresh kernel
environment. No admitted proof, custom axiom, native-decision dependency, or unsafe
proof shortcut was found in the project proof sources.

The new independent regression checker passed all **18,249 labelled trees with
1-7 vertices**, exploring all oriented diameter folds recursively. It also checks
tree preservation, the exact vertex-count decrease, distance contraction, and
retained-endpoint preservation. Separate cases cover singletons, paths through 12
vertices, unchanged diameter on a star, and Appendix A's 14-vertex example. The
Appendix A degree sequences and delayed equality of the full composite maps passed.
The existing randomized strategy checker reported **1,228 applicable trials, all
passing**, from 4,000 generated trees.

## Limits

Kernel replay uses Lean's own kernel, not an independently implemented verifier.
The usual trust in Lean, the standard axioms, and the local toolchain remains.
Computational checks are bounded regression tests and are not part of the proof.
The older exhaustive 8-vertex experiment cited in README was not rerun in this audit.
No independent verification of the contest provenance or publication claims in
README was performed.
