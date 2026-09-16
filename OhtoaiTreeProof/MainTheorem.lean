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
import OhtoaiTreeProof.Iso
import OhtoaiTreeProof.Diameter

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open _root_.SimpleGraph

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

/-! ## Auxiliary facts about the fixed-endpoint process -/

/-- A folding sequence of length zero is the identity sequence. -/
theorem FoldSeqAt.eq_of_zero : ∀ {S S' : TreeState V} {s : V} {n : ℕ},
    FoldSeqAt s S S' n → n = 0 → S' = S := by
  intro S S' s n h
  induction h with
  | refl => intro _; rfl
  | step hpos hstep htail ih => intro hn; exact absurd hn (by omega)

/-- No operation can be performed from a state with at most one vertex, so a sequence of length
`n` from such a state has `n = 0`. -/
theorem FoldSeqAt.eq_zero_of_card_le_one : ∀ {S S' : TreeState V} {s : V} {n : ℕ},
    FoldSeqAt s S S' n → S.alive.card ≤ 1 → n = 0 := by
  intro S S' s n h
  induction h with
  | refl => intro _; rfl
  | step hpos hstep htail ih => intro hc; exact absurd hpos (by omega)

/-- A nonempty folding sequence can only start from a state with at least two vertices. -/
theorem FoldSeqAt.two_le_card_of_pos : ∀ {S S' : TreeState V} {s : V} {n : ℕ},
    FoldSeqAt s S S' n → 1 ≤ n → 2 ≤ S.alive.card := by
  intro S S' s n h
  induction h with
  | refl => intro hn; exact absurd hn (by omega)
  | step hpos hstep htail ih => intro _; exact hpos

/-- A diameter path joining two diameter endpoints that are at distance `diam` from each other,
with both endpoints prescribed. -/
theorem exists_diamPath_between (S : TreeState V) {s t : V} (hs : IsDiamEnd S s)
    (ht : IsDiamEnd S t) (hd : S.graph.dist s t = S.diam) :
    ∃ P : DiamPath S, P.p 0 = s ∧ P.p P.last = t := by
  classical
  refine ⟨S.diamPathOf hs.1 ht.1 hd, ?_, ?_⟩
  · show (S.diamPathOf hs.1 ht.1 hd).p 0 = s
    unfold TreeState.diamPathOf
    simp only [Fin.val_zero]
    rw [SimpleGraph.Walk.getVert_zero]
  · show (S.diamPathOf hs.1 ht.1 hd).p (S.diamPathOf hs.1 ht.1 hd).last = t
    unfold TreeState.diamPathOf
    simp only [DiamPath.last, Fin.val_mk, SimpleGraph.Walk.getVert_length]

/-- The case `d (s,t) = diam` of `REF.md` Proposition 2: the two endpoints are joined by a common
diameter, so the first fold can be taken along that diameter, and by `lValue_foldState_reverse`
folding towards `s` and towards `t` along it lead to the same value. -/
theorem LValue_of_dist_eq_diam {S : TreeState V} {s t : V} (hs : IsDiamEnd S s)
    (ht : IsDiamEnd S t) (hd : S.graph.dist s t = S.diam) {n : ℕ}
    (h : LValue S s n) : LValue S t n := by
  by_cases hcard : S.alive.card ≤ 1
  · obtain ⟨S₁, h₁, -⟩ := h
    rw [FoldSeqAt.eq_zero_of_card_le_one h₁ hcard]
    exact ⟨S, FoldSeqAt.refl S, hcard⟩
  · have hcard2 : 2 ≤ S.alive.card := by omega
    obtain ⟨P, hP0, hPlast⟩ := exists_diamPath_between S hs ht hd
    -- a complete process from the folded state, towards `s`
    obtain ⟨m, hm⟩ := LValue_exists_of_isDiamEnd P.foldState.alive.card P.foldState (P.p 0)
      le_rfl (isDiamEnd_foldState P)
    obtain ⟨T, hT, hT1⟩ := hm
    have hT' : FoldSeqAt s P.foldState T m := by rw [← hP0]; exact hT
    have hstep : FoldStepAt s S P.foldState := ⟨P, hP0, rfl⟩
    -- Proposition 1 identifies the two lengths
    obtain ⟨S₁, hS₁, hs₁⟩ := h
    have hlength : n = m + 1 :=
      LValue_unique S.alive.card S S₁ T s n (m + 1) le_rfl hs hS₁
        (FoldSeqAt.step hcard2 hstep hT') hs₁ hT1
    rw [hlength]
    -- fold the other way round along the same diameter
    have hrev : LValue P.reverse.foldState (P.p P.last) m :=
      (lValue_foldState_reverse P m).mp ⟨T, hT, hT1⟩
    obtain ⟨T₂, hT₂, hT₂1⟩ := hrev
    have hT₂' : FoldSeqAt t P.reverse.foldState T₂ m := by rw [← hPlast]; exact hT₂
    have hrevStep : FoldStepAt t S P.reverse.foldState :=
      ⟨P.reverse, by rw [DiamPath.reverse_p_zero, hPlast], rfl⟩
    exact ⟨T₂, FoldSeqAt.step hcard2 hrevStep hT₂', hT₂1⟩

/-- REF.md Proposition 2 (§10): the number of operations of the fixed-endpoint process does not
depend on which diameter endpoint was fixed.  (`REF.md` proves this from Lemma 7: two diameter
endpoints `a`, `b` either are at distance `diam` from each other, or have a common "opposite"
diameter endpoint `c`; in both cases the fixed-endpoint process from `a` can be compared with the
one from `b`.) -/
theorem LValue_endpoint_independent {S : TreeState V} {s t : V} {n : ℕ}
    (hs : IsDiamEnd S s) (ht : IsDiamEnd S t) (h : LValue S s n) : LValue S t n := by
  rcases exists_common_opposite hs ht with hd | ⟨c, hc, hac, hbc⟩
  · exact LValue_of_dist_eq_diam hs ht hd h
  · exact LValue_of_dist_eq_diam hc ht (by rw [SimpleGraph.dist_comm]; exact hbc)
      (LValue_of_dist_eq_diam hs hc hac h)

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

/-- REF.md Proposition 3 (§12): every single folding operation, along an arbitrary diameter,
decreases the value of the process by exactly one.

`REF.md` proves this by looking at the diameter `a`–`b` along which the operation folds: `a` is a
diameter endpoint, and by Lemma 3 the merged vertex `q` of `a` and `b` is a diameter endpoint of
the folded tree `S'`.  Hence a complete process from `S'` towards `q` (`LValue_Phi`), preceded by
this very operation, is a complete process from `S` towards `a`; by Proposition 1 its length is
`Phi S`, and the length of the rest is `Phi S'`. -/
theorem Phi_step {S S' : TreeState V} (h : FoldStep S S') (hcard : 2 ≤ S.alive.card) :
    Phi S = Phi S' + 1 := by
  obtain ⟨Q, rfl⟩ := h
  have hEndS : IsDiamEnd S (Q.p 0) := Q.isDiamEnd_zero
  have hEndS' : IsDiamEnd Q.foldState (Q.p 0) := isDiamEnd_foldState Q
  obtain ⟨T, hseq, hsingle⟩ := LValue_Phi hEndS'
  have hstep : FoldStepAt (Q.p 0) S Q.foldState := ⟨Q, rfl, rfl⟩
  have hseqAll : FoldSeqAt (Q.p 0) S T (Phi Q.foldState + 1) :=
    FoldSeqAt.step hcard hstep hseq
  obtain ⟨T', hseq', hsingle'⟩ := LValue_Phi hEndS
  have := LValue_unique S.alive.card S T T' (Q.p 0) (Phi Q.foldState + 1) (Phi S) le_rfl hEndS
    hseqAll hseq' hsingle hsingle'
  omega

/-! ## The main theorem -/

/-- Every nonempty state has a legal completion ending at exactly one live vertex. -/
theorem exists_complete_foldSeq (S : TreeState V) (hne : S.alive.Nonempty) :
    ∃ S' n, FoldSeq S S' n ∧ S'.alive.card = 1 := by
  obtain ⟨s, hs⟩ := exists_isDiamEnd hne
  obtain ⟨n, S', hseq, hsingle⟩ :=
    LValue_exists_of_isDiamEnd S.alive.card S s le_rfl hs
  exact ⟨S', n, hseq.toFoldSeq, hseq.toFoldSeq.card_eq_one hne hsingle⟩

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

/-- The complete processes quantified over in the main theorem exist for every finite tree. -/
theorem exists_complete_foldSeq_of_isTree {G : SimpleGraph V} (hG : G.IsTree) :
    ∃ S' n, FoldSeq (TreeState.ofIsTree hG) S' n ∧ S'.alive.card = 1 := by
  obtain ⟨v⟩ := hG.connected.nonempty
  exact exists_complete_foldSeq (TreeState.ofIsTree hG) ⟨v, Finset.mem_univ v⟩

/-- **Main theorem, in the form of `REF.md`.**  Let `G` be a tree.  Fold it along an arbitrary
diameter (identifying mirror-image vertices `d i ~ d (D - i)` of that diameter), and repeat until
a single vertex is left.  The number of operations does not depend on the diameters chosen. -/
theorem fold_count_unique_of_isTree {G : SimpleGraph V} (hG : G.IsTree) {S₁ S₂ : TreeState V}
    {n m : ℕ} (h₁ : FoldSeq (TreeState.ofIsTree hG) S₁ n) (h₂ : FoldSeq (TreeState.ofIsTree hG) S₂ m)
    (hs₁ : IsSingle S₁) (hs₂ : IsSingle S₂) : n = m :=
  fold_count_unique h₁ h₂ hs₁ hs₂

end OhtoaiTreeProof
