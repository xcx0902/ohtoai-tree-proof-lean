/-
# The value of the folding process

This file contains the assembly of the main theorem of `REF.md`: the number of folding
operations needed to reduce a tree to a single vertex does not depend on the diameters chosen.

The proof follows `REF.md` §11–13.  Fix a diameter endpoint `s` of the initial tree and always
fold *towards* `s` (that is, along a diameter whose first vertex is `s`); by the key lemma of
`REF.md` (Lemma 3, `OhtoaiTreeProof.isDiamEnd_foldState`) the vertex `s` remains a diameter
endpoint of every intermediate tree, so the process can be repeated until a single vertex is
left (`OhtoaiTreeProof.Phi_exists`).  The number of operations of that process is independent of
the choices made (`OhtoaiTreeProof.LValue_unique`, REF Proposition 1, proved in
`OhtoaiTreeProof.Exchange` from the exchange Lemma 5).  Its value `Phi S` is therefore well
defined, and every single folding operation, along *any* diameter, decreases `Phi` by exactly
one (`Phi_step`, REF Propositions 2 and 3, which uses `LValue_endpoint_independent`).  Hence any
complete folding process has length `Phi S`: all complete processes have the same length
(`fold_count_unique`).
-/
import OhtoaiTreeProof.Exchange

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The value of the process -/

/-- The value of a state: the number of operations of a complete folding process.  The choice
made here (a diameter endpoint together with a complete process towards it) is irrelevant by
`LValue_unique` and `LValue_endpoint_independent`. -/
noncomputable def Phi (S : TreeState V) : ℕ :=
  if h : S.alive.card ≤ 1 then 0
  else Classical.choose (Classical.choose_spec (Phi_exists S h)).2

/-- A state with a single vertex needs no operation. -/
theorem Phi_eq_zero_of_single {S : TreeState V} (h : IsSingle S) : Phi S = 0 := by
  have h' : S.alive.card ≤ 1 := h
  rw [Phi, dite_eq_left h']

/-! ## The propositions of `REF.md` that make up the mathematical core -/

/-- REF.md Proposition 2 (§10): the number of operations of the fixed-endpoint process does not
depend on which diameter endpoint was fixed.  (`REF.md` proves this from Lemma 7: two diameter
endpoints `a`, `b` either are at distance `diam` from each other, or have a common "opposite"
diameter endpoint `c`; in both cases the fixed-endpoint process from `a` can be compared with the
one from `b`.) -/
theorem LValue_endpoint_independent {S : TreeState V} {s t : V} {n : ℕ}
    (hs : IsDiamEnd S s) (ht : IsDiamEnd S t) (h : LValue S s n) : LValue S t n := by
  sorry

/-- REF.md Lemma 7 (§10): two diameter endpoints of a tree either are antipodal, or have a common
diameter endpoint opposite to both of them. -/
theorem exists_common_opposite {S : TreeState V} {a b : V} (ha : IsDiamEnd S a)
    (hb : IsDiamEnd S b) :
    S.graph.dist a b = S.diam ∨
      ∃ c : V, IsDiamEnd S c ∧ S.graph.dist a c = S.diam ∧ S.graph.dist b c = S.diam := by
  sorry

/-- REF.md Propositions 2 and 3 (§12): every single folding operation, along an arbitrary
diameter, decreases the value of the process by exactly one.

`REF.md` proves this by taking the diameter `a`–`b` along which the operation folds: `a` is a
diameter endpoint, `Phi S = L(S,a)`, the first operation of the fixed-endpoint process from `a`
is exactly this fold, and the merged vertex `q` of `a` and `b` is a diameter endpoint of `S'`
(Lemma 3), so that `L(S,a) = 1 + L(S',q) = 1 + Phi S'`. -/
theorem Phi_step {S S' : TreeState V} (h : FoldStep S S') (hcard : 2 ≤ S.alive.card) :
    Phi S = Phi S' + 1 := by
  sorry

/-! ## The value is realised by the fixed-endpoint process -/

/-- The value of a state is realised by a complete process towards any of its diameter
endpoints: this is where `LValue_unique` is used. -/
theorem LValue_Phi {S : TreeState V} {s : V} (hs : IsDiamEnd S s) : LValue S s (Phi S) := by
  by_cases h : S.alive.card ≤ 1
  · rw [Phi_eq_zero_of_single h]
    exact ⟨S, FoldSeqAt.refl S, h⟩
  · have hd : Phi S = Classical.choose (Classical.choose_spec (Phi_exists S h)).2 := by
      rw [Phi, dite_eq_right h]
    have hEnd : IsDiamEnd S (Classical.choose (Phi_exists S h)) :=
      (Classical.choose_spec (Phi_exists S h)).1
    have hL : LValue S (Classical.choose (Phi_exists S h))
        (Classical.choose (Classical.choose_spec (Phi_exists S h)).2) :=
      Classical.choose_spec (Classical.choose_spec (Phi_exists S h)).2
    rw [hd]
    exact LValue_endpoint_independent hEnd hs hL

/-! ## The main theorem -/

/-- The value decreases by exactly one at every step of any complete folding process. -/
theorem Phi_eq_of_foldSeq {S S' : TreeState V} {n : ℕ} (h : FoldSeq S S' n) :
    Phi S = Phi S' + n := by
  induction h with
  | refl S => simp
  | step hpos hstep _ ih =>
      rw [Phi_step hstep hpos, ih]
      omega

/-- **Main theorem.**  For a tree `S`, any two complete folding processes — each of them folding
along an arbitrary diameter at every step, until a single vertex is left — have the same number
of operations.  This is the assertion of `REF.md` (Theorem 1). -/
theorem fold_count_unique {S S₁ S₂ : TreeState V} {n m : ℕ}
    (h₁ : FoldSeq S S₁ n) (h₂ : FoldSeq S S₂ m) (hs₁ : IsSingle S₁) (hs₂ : IsSingle S₂) :
    n = m := by
  have e₁ := Phi_eq_of_foldSeq h₁
  have e₂ := Phi_eq_of_foldSeq h₂
  rw [Phi_eq_zero_of_single hs₁] at e₁
  rw [Phi_eq_zero_of_single hs₂] at e₂
  omega

/-- A tree, viewed as a state of the folding process: all vertices are alive. -/
def TreeState.ofIsTree {G : SimpleGraph V} (hG : G.IsTree) : TreeState V where
  alive := Finset.univ
  graph := G
  adj_alive := fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  connected := fun u _ v _ => hG.connected u v
  acyclic := hG.isAcyclic

/-- **Main theorem, in the form of `REF.md`.**  Let `G` be a tree.  Fold it along an arbitrary
diameter (identifying mirror-image vertices `d i ~ d (D - i)` of that diameter), and repeat until
a single vertex is left.  The number of operations does not depend on the diameters chosen. -/
theorem fold_count_unique_of_isTree {G : SimpleGraph V} (hG : G.IsTree) {S₁ S₂ : TreeState V}
    {n m : ℕ} (h₁ : FoldSeq (TreeState.ofIsTree hG) S₁ n) (h₂ : FoldSeq (TreeState.ofIsTree hG) S₂ m)
    (hs₁ : IsSingle S₁) (hs₂ : IsSingle S₂) : n = m :=
  fold_count_unique h₁ h₂ hs₁ hs₂

end OhtoaiTreeProof
