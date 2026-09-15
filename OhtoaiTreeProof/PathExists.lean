/-
# Constructing a diameter from a vertex

The fixed-endpoint process of `REF.md` folds along a diameter *starting* at the fixed endpoint
`s`.  This file provides that diameter as a `DiamPath`: for a live vertex `x` at distance `diam`
from the live vertex `s`, the vertices of a shortest `s`–`x` walk, listed in order, form a
`DiamPath` whose first vertex is `s`.
-/
import OhtoaiTreeProof.Basic

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every vertex of a walk between two live vertices is live. -/
theorem TreeState.support_subset_alive {S : TreeState V} {u : V} (hu : u ∈ S.alive) :
    ∀ {v : V} (w : S.graph.Walk u v), ∀ x ∈ w.support, x ∈ S.alive := by
  intro v w
  induction w with
  | nil =>
      intro x hx
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      rw [hx]
      exact hu
  | cons hadj rest ih =>
      intro x hx
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with h | h
      · rw [h]; exact (S.adj_alive hadj).1
      · exact ih (S.adj_alive hadj).2 x h

/-- A shortest walk from `s` to `x`, read as a diameter path. -/
noncomputable def TreeState.diamPathOf (S : TreeState V) {s x : V} (hs : s ∈ S.alive)
    (hx : x ∈ S.alive) (hd : S.graph.dist s x = S.diam) : DiamPath S := by
  classical
  have hex := (S.connected s hs x hx).exists_path_of_dist
  let w : S.graph.Walk s x := Classical.choose hex
  have hwpath : w.IsPath := (Classical.choose_spec hex).1
  have hwlen : w.length = S.graph.dist s x := (Classical.choose_spec hex).2
  refine ⟨w.length, fun i => w.getVert (i : ℕ), ?_, ?_, ?_, ?_⟩
  · intro i
    exact S.support_subset_alive hs w _ (SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
      ⟨(i : ℕ), rfl, by have := i.isLt; omega⟩)
  · intro i j hij
    have h1 : (i : ℕ) ≤ w.length := by have := i.isLt; omega
    have h2 : (j : ℕ) ≤ w.length := by have := j.isLt; omega
    exact Fin.ext (hwpath.getVert_injOn h1 h2 hij)
  · intro i
    have hi : (i : ℕ) < w.length := i.isLt
    simpa only [Fin.val_castSucc, Fin.val_succ] using w.adj_getVert_succ hi
  · show S.graph.dist (w.getVert 0) (w.getVert w.length) = S.diam
    rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length, hd]

/-- From any diameter endpoint `s` there is a diameter path starting at `s`. -/
theorem exists_diamPath_at (S : TreeState V) {s : V} (hs : IsDiamEnd S s) :
    ∃ P : DiamPath S, P.p 0 = s := by
  obtain ⟨x, hx, hd⟩ := hs.2
  refine ⟨S.diamPathOf hs.1 hx hd, ?_⟩
  show (S.diamPathOf hs.1 hx hd).p 0 = s
  unfold TreeState.diamPathOf
  simp only [Fin.val_zero]
  rw [SimpleGraph.Walk.getVert_zero]

end OhtoaiTreeProof
