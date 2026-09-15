/-
# The folding process makes progress

Every folding operation strictly decreases the number of vertices, and no operation can be
performed on a state with a single vertex.  Consequently the length of a folding sequence is
bounded by the number of vertices of the initial state: the process always terminates, and the
"stop as soon as a single vertex is left" convention of `FoldSeq` is the natural one.

The precise number of vertices removed by one operation is computed in `REF.md` §2 (it is
`⌈D/2⌉`, where `D` is the length of the diameter folded along); here we only need that at least
one vertex disappears.
-/
import OhtoaiTreeProof.Basic

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DiamPath

variable {S : TreeState V} (P : DiamPath S)

/-- The first vertex of the diameter survives the folding. -/
theorem zero_mem_foldAlive : P.p 0 ∈ P.foldAlive := by
  rw [P.path_mem_foldAlive]
  simp

/-- A diameter of positive length has at least two vertices, so the last one is not fixed by the
folding map. -/
theorem last_not_mem_foldAlive (hD : 1 ≤ P.D) : P.p P.last ∉ P.foldAlive := by
  intro h
  have := (P.path_mem_foldAlive (i := P.last)).mp h
  simp only [last_val] at this
  omega

theorem foldAlive_ssubset (hD : 1 ≤ P.D) : P.foldAlive ⊂ S.alive := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨P.foldAlive_subset, fun h => ?_⟩
  have hmem : P.p P.last ∈ P.foldAlive := by rw [h]; exact P.mem P.last
  exact P.last_not_mem_foldAlive hD hmem

/-- Folding strictly decreases the number of vertices, as soon as the diameter is nonempty. -/
theorem foldAlive_card_lt (hD : 1 ≤ P.D) : P.foldAlive.card < S.alive.card :=
  Finset.card_lt_card (P.foldAlive_ssubset hD)

theorem foldState_card_lt (hD : 1 ≤ P.D) : P.foldState.alive.card < S.alive.card :=
  P.foldAlive_card_lt hD

/-- In a state with at least two vertices the diameter is nonempty. -/
theorem one_le_D (hcard : 2 ≤ S.alive.card) : 1 ≤ P.D := by
  by_contra hD
  have hD0 : P.D = 0 := by omega
  have hdiam : S.diam = 0 := by
    rw [← P.isDiam]
    have hlast : (⟨P.D, Nat.lt_succ_self P.D⟩ : Fin (P.D + 1)) = 0 := by
      ext
      simpa using hD0
    rw [hlast, SimpleGraph.dist_self]
  have hall : ∀ u ∈ S.alive, ∀ v ∈ S.alive, u = v := by
    intro u hu v hv
    have h1 : S.graph.dist u v ≤ S.diam := S.dist_le_diam hu hv
    rw [hdiam] at h1
    exact (S.dist_eq_zero_iff hu hv).mp (Nat.eq_zero_of_le_zero h1)
  have : S.alive.card ≤ 1 := Finset.card_le_one.mpr fun u hu v hv => hall u hu v hv
  omega

end DiamPath

/-! ## Folding steps decrease the number of vertices -/

theorem FoldStep.card_lt {S S' : TreeState V} (h : FoldStep S S') (hcard : 2 ≤ S.alive.card) :
    S'.alive.card < S.alive.card := by
  obtain ⟨P, rfl⟩ := h
  exact P.foldState_card_lt (P.one_le_D hcard)

/-- A folding sequence of length `n` starts from a state with at least `n` vertices. -/
theorem FoldSeq.card_le {S S' : TreeState V} {n : ℕ} (h : FoldSeq S S' n) :
    n ≤ S.alive.card := by
  induction h with
  | refl S => simp
  | step hpos hstep _ ih => have := hstep.card_lt hpos; omega

end OhtoaiTreeProof
