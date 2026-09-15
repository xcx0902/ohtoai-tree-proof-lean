/-
# The value of the folding process

This file contains the assembly of the main theorem of `REF.md`: the number of folding
operations needed to reduce a tree to a single vertex does not depend on the diameters chosen.

The proof follows `REF.md` §11–13.  Fix a diameter endpoint `s` of the initial tree and always
fold *towards* `s` (that is, along a diameter whose first vertex is `s`); by the key lemma of
`REF.md` (Lemma 3, formalized in `OhtoaiTreeProof.Endpoint`) the vertex `s` remains a diameter
endpoint of every intermediate tree, so the process can be repeated until a single vertex is
left.  The number of operations of that process is independent of the choices made
(`LValue_unique`, REF Proposition 1); averaging over all diameter endpoints shows that the
resulting number `Phi S` does not depend on the endpoint chosen (`LValue_endpoint_independent`,
REF Proposition 2); and every single folding operation, along *any* diameter, decreases `Phi`
by exactly one (`Phi_step`, REF Propositions 2 and 3).  Hence any complete folding process has
length `Phi S`, and in particular all complete processes have the same length
(`fold_count_unique`).
-/
import OhtoaiTreeProof.Basic

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Diameter endpoints -/

/-- `s` is a diameter endpoint of the state `S` if it is a live vertex at distance `diam`
from some other live vertex. -/
def IsDiamEnd (S : TreeState V) (s : V) : Prop :=
  s ∈ S.alive ∧ ∃ y ∈ S.alive, S.graph.dist s y = S.diam

theorem IsDiamEnd.mem {S : TreeState V} {s : V} (h : IsDiamEnd S s) : s ∈ S.alive := h.1

theorem IsDiamEnd.ecc {S : TreeState V} {s : V} (h : IsDiamEnd S s) :
    ∃ y ∈ S.alive, S.graph.dist s y = S.diam := h.2

/-- The endpoints of a diameter path are diameter endpoints of the state. -/
theorem DiamPath.isDiamEnd_zero {S : TreeState V} (P : DiamPath S) :
    IsDiamEnd S (P.p 0) :=
  ⟨P.mem 0, P.p P.last, P.mem P.last, P.isDiam⟩

theorem DiamPath.isDiamEnd_last {S : TreeState V} (P : DiamPath S) :
    IsDiamEnd S (P.p P.last) :=
  ⟨P.mem P.last, P.p 0, P.mem 0, by rw [SimpleGraph.dist_comm]; exact P.isDiam⟩

/-- A nonempty state has a diameter endpoint. -/
theorem exists_isDiamEnd {S : TreeState V} (h : S.alive.Nonempty) : ∃ s, IsDiamEnd S s := by
  obtain ⟨u, hu, v, hv, hd⟩ := S.exists_dist_eq_diam h
  exact ⟨u, hu, v, hv, hd⟩

/-! ## Folding towards a fixed endpoint -/

/-- One folding step in which the fold is performed towards the fixed vertex `s`: the diameter
along which we fold starts at `s`, so that `s` is one of the two vertices being identified. -/
def FoldStepAt (s : V) (S S' : TreeState V) : Prop :=
  ∃ P : DiamPath S, P.p 0 = s ∧ S' = P.foldState

/-- `FoldSeqAt s S S' n`: `S'` is obtained from `S` by `n` folding steps, each of them performed
towards the fixed vertex `s`.  No step is taken from a state with at most one vertex, so the
sequence is *maximal*: it stops as soon as a single vertex is left. -/
inductive FoldSeqAt (s : V) : TreeState V → TreeState V → ℕ → Prop
  | refl (S : TreeState V) : FoldSeqAt s S S 0
  | step {S S' S'' : TreeState V} {n : ℕ} (hpos : 2 ≤ S.alive.card) :
      FoldStepAt s S S' → FoldSeqAt s S' S'' n → FoldSeqAt s S S'' (n + 1)

/-- `LValue S s n`: there is a complete folding process of `S` that always folds towards `s`,
performs exactly `n` operations, and ends with a single vertex. -/
def LValue (S : TreeState V) (s : V) (n : ℕ) : Prop :=
  ∃ S' : TreeState V, FoldSeqAt s S S' n ∧ IsSingle S'

/-! ## The value of the process -/

/-- A state with more than one vertex admits a complete folding process towards some diameter
endpoint (REF.md Lemma 3 and Proposition 2: the process always makes progress). -/
theorem Phi_exists (S : TreeState V) (h : ¬S.alive.card ≤ 1) :
    ∃ s : V, IsDiamEnd S s ∧ ∃ n : ℕ, LValue S s n := by
  sorry

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

/-! ## The three propositions of `REF.md` that make up the mathematical core -/

/-- REF.md Proposition 1 (the statement of §8): when one always folds towards a fixed diameter
endpoint `s`, the number of operations is independent of the choices made.  This is the
mathematical core of the whole proof; `REF.md` proves it through the exchange Lemma 5 (§7). -/
theorem LValue_unique {S S₁ S₂ : TreeState V} {s : V} {n m : ℕ}
    (hs : IsDiamEnd S s) (h₁ : FoldSeqAt s S S₁ n) (h₂ : FoldSeqAt s S S₂ m)
    (hs₁ : IsSingle S₁) (hs₂ : IsSingle S₂) : n = m := by
  sorry

/-- REF.md Proposition 2 (§10): the number of operations of the fixed-endpoint process does not
depend on which diameter endpoint was fixed. -/
theorem LValue_endpoint_independent {S : TreeState V} {s t : V} {n : ℕ}
    (hs : IsDiamEnd S s) (ht : IsDiamEnd S t) (h : LValue S s n) : LValue S t n := by
  sorry

/-- REF.md Propositions 2 and 3 (§12): every single folding operation, along an arbitrary
diameter, decreases the value of the process by exactly one. -/
theorem Phi_step {S S' : TreeState V} (h : FoldStep S S') (hcard : 2 ≤ S.alive.card) :
    Phi S = Phi S' + 1 := by
  sorry

/-- The value decreases by exactly one at every step of any complete folding process. -/
theorem Phi_eq_of_foldSeq {S S' : TreeState V} {n : ℕ} (h : FoldSeq S S' n) :
    Phi S = Phi S' + n := by
  induction h with
  | refl S => simp
  | step hpos hstep _ ih =>
      rw [Phi_step hstep hpos, ih]
      omega

/-! ## The main theorem -/

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
