/-
# The common endgame and the delayed exchange lemma

At diameter `2r`, the two surviving legs are diameters. Their folds have the same composite map
on the original tree, even after an arbitrary synchronized phase satisfying `SyncCtx`.
Equality of these maps gives equality of the resulting states. The final assembly also handles
coincident initial diameters separately, without requiring an illegal fold of a singleton.
-/
import OhtoaiTreeProof.SyncStep

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open _root_.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A path whose length is the diameter, packaged as a diameter path. -/
abbrev SeqPath.toDiamPath {T : TreeState V} {q : ℕ → V} {L : ℕ}
    (h : SeqPath T q L) (hd : T.diam = L) : DiamPath T where
  D := L
  p i := q i
  mem i := h.1 i (by have := i.isLt; omega)
  inj := by
    intro i j hij
    exact Fin.ext (h.2.2 i (by omega) j (by omega) hij)
  adj i := h.2.1 i i.isLt
  isDiam := (h.dist_eq le_rfl).trans hd.symm

theorem SeqPath.toDiamPath_rep {T : TreeState V} {q : ℕ → V} {L : ℕ}
    (h : SeqPath T q L) (hd : T.diam = L) {k : ℕ} (hk : k ≤ L) :
    (h.toDiamPath hd).rep (q k) = q (min k (L - k)) :=
  (h.toDiamPath hd).rep_path ⟨k, by change k < L + 1; omega⟩

namespace DiamPath

variable {S T : TreeState V} {P Q : DiamPath S} {s : V}

/-- At the stopping scale the surviving leg folds its tail onto the common spine. -/
theorem legAt_rep_tail (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hl : SeqPath T (P.legSeq Q) (2 * (P.D - P.meetIdx Q)))
    (hd : T.diam = 2 * (P.D - P.meetIdx Q)) {j : ℕ}
    (hj : P.meetIdx Q < j) (hjD : j ≤ P.D) :
    (hl.toDiamPath hd).rep (Q.seq j) = P.seq (P.D - j) := by
  have hr := P.tail_le_meetIdx Q hP hQ
  have heq : P.legSeq Q (P.D - P.meetIdx Q + (j - P.meetIdx Q)) = Q.seq j := by
    rw [P.legSeq_of_lt Q (by omega)]
    congr 1
    omega
  rw [← heq, hl.toDiamPath_rep hd (by omega)]
  rw [show min (P.D - P.meetIdx Q + (j - P.meetIdx Q))
    (2 * (P.D - P.meetIdx Q) - (P.D - P.meetIdx Q + (j - P.meetIdx Q))) =
      P.D - j by omega, P.legSeq_of_le Q (by omega)]

/-- Off the surviving tail, the endgame fold is the identity. -/
theorem legAt_rep_fixed
    (hl : SeqPath T (P.legSeq Q) (2 * (P.D - P.meetIdx Q)))
    (hd : T.diam = 2 * (P.D - P.meetIdx Q)) {v : V}
    (hv : ∀ j, P.meetIdx Q < j → j ≤ P.D → Q.seq j ≠ v) :
    (hl.toDiamPath hd).rep v = v := by
  let Z := hl.toDiamPath hd
  rcases hi : Z.index v with _ | i
  · exact Z.rep_of_index_none hi
  · have hiv : P.legSeq Q (i : ℕ) = v := Z.eq_of_index_eq_some hi
    have hiL : (i : ℕ) ≤ 2 * (P.D - P.meetIdx Q) := by
      have hii : (i : ℕ) < 2 * (P.D - P.meetIdx Q) + 1 := i.isLt
      omega
    by_cases hir : (i : ℕ) ≤ P.D - P.meetIdx Q
    · rw [← hiv, hl.toDiamPath_rep hd hiL,
        show min (i : ℕ) (2 * (P.D - P.meetIdx Q) - (i : ℕ)) = (i : ℕ) by omega]
    · rw [P.legSeq_of_lt Q (by omega)] at hiv
      exact (hv _ (by omega) (by omega) hiv).elim

theorem legAt_rep_common (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hl : SeqPath T (P.legSeq Q) (2 * (P.D - P.meetIdx Q)))
    (hd : T.diam = 2 * (P.D - P.meetIdx Q)) {v : V}
    (hv : v ∉ P.Delta Q s) : (hl.toDiamPath hd).rep v = v := by
  apply legAt_rep_fixed hl hd
  intro j hj hjD heq
  exact hv (heq ▸ (P.seq_mem_Delta_iff_Q Q hP hQ hjD).mpr hj)

/-- The endgame fixes every spine vertex. -/
theorem legAt_rep_spine
    (hl : SeqPath T (P.legSeq Q) (2 * (P.D - P.meetIdx Q)))
    (hd : T.diam = 2 * (P.D - P.meetIdx Q)) {k : ℕ}
    (hk : k ≤ P.D - P.meetIdx Q) : (hl.toDiamPath hd).rep (P.seq k) = P.seq k := by
  rw [← P.legSeq_of_le Q hk, hl.toDiamPath_rep hd (by omega),
    show min k (2 * (P.D - P.meetIdx Q) - k) = k by omega]

/-- The two endgame maps agree after any synchronized quotient map.

Only tail vertices distinguish the initial representatives. Their images are fixed by the
synchronized map; elsewhere the representatives coincide and stay outside the two tails.
-/
theorem legAt_rep_comp {T₁ T₂ : TreeState V} {σ : V → V}
    (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hl₁ : SeqPath T₁ (P.legSeq Q) (2 * (P.D - P.meetIdx Q)))
    (hl₂ : SeqPath T₂ (Q.legSeq P) (2 * (Q.D - Q.meetIdx P)))
    (hd₁ : T₁.diam = 2 * (P.D - P.meetIdx Q))
    (hd₂ : T₂.diam = 2 * (Q.D - Q.meetIdx P))
    (hσD : ∀ v ∈ P.Delta Q s, σ v = v)
    (hσC : ∀ v, v ∉ P.Delta Q s → σ v ∉ P.Delta Q s)
    (hσsp : ∀ k ≤ P.D - P.meetIdx Q, σ (P.seq k) = P.seq k)
    (v : V) :
    (hl₁.toDiamPath hd₁).rep (σ (P.rep v)) =
      (hl₂.toDiamPath hd₂).rep (σ (Q.rep v)) := by
  have hmeet := P.meetIdx_comm Q (hP.trans hQ.symm)
  have hD := P.D_eq Q
  have hr := P.tail_le_meetIdx Q hP hQ
  have hcomm := P.Delta_comm Q s (hP.trans hQ.symm)
  by_cases hv : v ∈ P.tailSet Q
  · rcases P.mem_tailSet.mp hv with ⟨j, hj, hjD, rfl⟩ | ⟨j, hj, hjD, rfl⟩
    · have hrep : P.rep (P.seq j) = P.seq (P.D - j) := by
        rw [P.rep_seq hjD, min_eq_right (by omega)]
      have hQrep := P.rep_off_path' Q hP hQ hj hjD
      have hvD := (P.seq_mem_Delta_iff Q hP hQ hjD).mpr hj
      rw [hrep, hQrep, hσsp _ (by omega), hσD _ hvD,
        legAt_rep_spine hl₁ hd₁ (by omega),
        legAt_rep_tail hQ hP hl₂ hd₂ (by omega) (by omega)]
      rw [← hD]
      exact P.seq_eq_of_le_meetIdx Q hP hQ (by omega)
    · have hrep : Q.rep (Q.seq j) = P.seq (P.D - j) := by
        rw [Q.rep_seq (by omega), min_eq_right (by omega), ← hD]
        exact (P.seq_eq_of_le_meetIdx Q hP hQ (by omega)).symm
      have hPrep := P.rep_off_path Q hP hQ hj hjD
      have hvD := (P.seq_mem_Delta_iff_Q Q hP hQ hjD).mpr hj
      rw [hPrep, hrep, hσD _ hvD, hσsp _ (by omega),
        legAt_rep_tail hP hQ hl₁ hd₁ hj hjD]
      have heq : P.seq (P.D - j) = Q.seq (P.D - j) :=
        P.seq_eq_of_le_meetIdx Q hP hQ (by omega)
      rw [heq, legAt_rep_spine hl₂ hd₂ (by omega)]
  · have hrep := P.rep_eq_of_not_mem_tailSet Q hP hQ hv
    by_cases hvD : v ∈ P.Delta Q s
    · have hnoP : ∀ i : Fin (P.D + 1), P.p i ≠ v := by
        intro i hi
        have hiD : (i : ℕ) ≤ P.D := by have := i.isLt; omega
        have hseq : P.seq (i : ℕ) = v := (P.seq_val i).trans hi
        have htail := (P.seq_mem_Delta_iff Q hP hQ hiD).mp (hseq ▸ hvD)
        exact hv (P.mem_tailSet.mpr (.inl ⟨i, htail, hiD, hseq.symm⟩))
      have hnoQ : ∀ i : Fin (Q.D + 1), Q.p i ≠ v := by
        intro i hi
        have hiD : (i : ℕ) ≤ P.D := by have := i.isLt; omega
        have hseq : Q.seq (i : ℕ) = v := (Q.seq_val i).trans hi
        have htail := (P.seq_mem_Delta_iff_Q Q hP hQ hiD).mp (hseq ▸ hvD)
        exact hv (P.mem_tailSet.mpr (.inr ⟨i, htail, hiD, hseq.symm⟩))
      rw [P.rep_eq_self hnoP, Q.rep_eq_self hnoQ, hσD _ hvD]
      rw [legAt_rep_fixed hl₁ hd₁ (fun j hj hjD heq =>
        hv (P.mem_tailSet.mpr (.inr ⟨j, hj, hjD, heq.symm⟩))),
        legAt_rep_fixed hl₂ hd₂ (fun j hj hjD heq =>
          hv (P.mem_tailSet.mpr (.inl ⟨j, by omega, by omega, heq.symm⟩)))]
    · have himage := hσC _ (P.rep_notMem_Delta Q hP hQ hvD)
      rw [legAt_rep_common hP hQ hl₁ hd₁ himage, ← hrep]
      rw [legAt_rep_common hQ hP hl₂ hd₂ (by rwa [← hcomm])]

/-- Express an image of a folded state directly as an image of the original tree. -/
theorem image_from_fold (P : DiamPath S) (U : TreeState V) (f : V → V)
    (hm : ∀ w, w ∈ U.alive ↔ ∃ v ∈ P.foldState.alive, f v = w)
    (ha : ∀ u v, U.graph.Adj u v ↔ u ≠ v ∧ u ∈ U.alive ∧ v ∈ U.alive ∧
      ∃ a b, P.foldState.graph.Adj a b ∧ f a = u ∧ f b = v) :
    (∀ w, w ∈ U.alive ↔ ∃ v ∈ S.alive, f (P.rep v) = w) ∧
    (∀ u v, U.graph.Adj u v ↔ u ≠ v ∧ u ∈ U.alive ∧ v ∈ U.alive ∧
      ∃ a b, S.graph.Adj a b ∧ f (P.rep a) = u ∧ f (P.rep b) = v) := by
  constructor
  · intro w
    rw [hm]
    constructor
    · rintro ⟨v, hv, hfv⟩
      obtain ⟨hvS, hfix⟩ := P.mem_foldAlive.mp hv
      exact ⟨v, hvS, by rw [hfix, hfv]⟩
    · rintro ⟨v, hv, hfv⟩
      exact ⟨P.rep v, P.rep_mem_foldAlive hv, hfv⟩
  · intro u v
    rw [ha]
    constructor
    · rintro ⟨hne, hu, hv, x, y, hxy, hxu, hyv⟩
      obtain ⟨-, -, -, a, b, hab, hax, hby⟩ := P.foldGraph_adj.mp hxy
      exact ⟨hne, hu, hv, a, b, hab, by rw [hax, hxu], by rw [hby, hyv]⟩
    · rintro ⟨hne, hu, hv, a, b, hab, hau, hbv⟩
      have hrep : P.rep a ≠ P.rep b := by
        intro heq
        exact hne (hau.symm.trans ((congrArg f heq).trans hbv))
      have hadj : P.foldState.graph.Adj (P.rep a) (P.rep b) :=
        ⟨hrep, P.rep_mem_foldAlive (S.adj_alive hab).1,
          P.rep_mem_foldAlive (S.adj_alive hab).2, a, b, hab, rfl, rfl⟩
      exact ⟨hne, hu, hv, P.rep a, P.rep b, hadj, hau, hbv⟩

namespace SyncCtx

variable {T₁ T₂ : TreeState V} {σ : V → V}

/-- At the stopping scale, the two legs fold onto exactly the same state. -/
theorem commonEndgame (h : SyncCtx P Q s T₁ T₂ σ) (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hd : T₁.diam = 2 * (P.D - P.meetIdx Q)) :
    CommonEndgame T₁ T₂ s := by
  have hmeet := P.meetIdx_comm Q (hP.trans hQ.symm)
  have hD := P.D_eq Q
  have hscale : 2 * (P.D - P.meetIdx Q) = 2 * (Q.D - Q.meetIdx P) := by omega
  have hl₂ : SeqPath T₂ (Q.legSeq P) (2 * (Q.D - Q.meetIdx P)) := by
    rw [← hscale]
    exact h.leg₂
  have hd₂ : T₂.diam = 2 * (Q.D - Q.meetIdx P) := by rw [← h.diam_eq, hd, hscale]
  let L₁ := h.leg₁.toDiamPath hd
  let L₂ := hl₂.toDiamPath hd₂
  have hcomp : ∀ v, L₁.rep (σ (P.rep v)) = L₂.rep (σ (Q.rep v)) :=
    legAt_rep_comp hP hQ h.leg₁ hl₂ hd hd₂ h.sigma_delta h.sigma_common h.sigma_spine
  obtain ⟨hm₁, ha₁⟩ := fold_image P.foldState L₁ σ h.alive₁ h.adjdesc₁
  obtain ⟨hm₂, ha₂⟩ := fold_image Q.foldState L₂ σ h.alive₂ h.adjdesc₂
  obtain ⟨hm₁', ha₁'⟩ := image_from_fold P L₁.foldState (L₁.rep ∘ σ) hm₁ ha₁
  obtain ⟨hm₂', ha₂'⟩ := image_from_fold Q L₂.foldState (L₂.rep ∘ σ) hm₂ ha₂
  have halive : L₁.foldState.alive = L₂.foldState.alive := by
    ext w
    simp only [hm₁', hm₂', Function.comp_apply, hcomp]
  have hgraph : L₁.foldState.graph = L₂.foldState.graph := by
    apply SimpleGraph.eq_of_adj_iff
    intro u v
    simp only [ha₁', ha₂', halive, Function.comp_apply, hcomp]
  refine ⟨L₁, L₂, ?_, ?_, ?_, ?_, TreeState.ext halive hgraph⟩
  · change 1 ≤ 2 * (P.D - P.meetIdx Q)
    omega
  · change 1 ≤ 2 * (Q.D - Q.meetIdx P)
    omega
  · change P.legSeq Q 0 = s
    rw [P.legSeq_zero Q, P.seq_zero, hP]
  · change Q.legSeq P 0 = s
    rw [Q.legSeq_zero P, Q.seq_zero, hQ]

end SyncCtx

/-- Distinct diameters from the same endpoint have a delayed common endgame. -/
theorem exists_commonEndgame_of_pos_tail (P Q : DiamPath S) (hs : IsDiamEnd S s)
    (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) :
    ∃ m T₁ T₂, FoldSeqAt s P.foldState T₁ m ∧ FoldSeqAt s Q.foldState T₂ m ∧
      CommonEndgame T₁ T₂ s := by
  have hinit := SyncCtx.init hP hQ hs hr
  obtain ⟨m, T₁, T₂, σ, h₁, h₂, hctx, hd⟩ := hinit.reach_scale hP hQ
  exact ⟨m, T₁, T₂, h₁, h₂, hctx.commonEndgame hP hQ hr hd⟩

/-- The delayed exchange lemma, including coincident diameters and singleton folds. -/
theorem synchronized_exchange (P Q : DiamPath S) (hs : IsDiamEnd S s)
    (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    ∃ n : ℕ, LValue P.foldState s n ∧ LValue Q.foldState s n := by
  by_cases hr : P.D - P.meetIdx Q = 0
  · have heq := P.foldState_eq_of_tail_eq_zero Q hP hQ hr
    have hs : IsDiamEnd P.foldState s := by rw [← hP]; exact isDiamEnd_foldState P
    obtain ⟨n, hn⟩ := LValue_exists_aux P.foldState.alive.card P.foldState s le_rfl hs
    exact ⟨n, hn, heq ▸ hn⟩
  · obtain ⟨m, T₁, T₂, h₁, h₂, hend⟩ :=
      P.exists_commonEndgame_of_pos_tail Q hs hP hQ (by omega)
    exact exchange_of_commonEndgame P Q hP h₁ h₂ hend

end DiamPath
end OhtoaiTreeProof
