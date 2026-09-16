/-
# The synchronized phase of REF.md §7

`SyncCtx.step` preserves the common part, the two legs, the distance bounds, and the composite
quotient map when both states fold along the same long diameter. `SyncCtx.reach_scale` iterates
this step by strong induction on the number of live vertices until the diameter is exactly the
length of a leg. The endgame is proved in `SyncEndgame.lean`.
-/
import OhtoaiTreeProof.Sync

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open _root_.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DiamPath

variable {S T U : TreeState V}

/-- A diameter can be constructed from a specified geodesic. -/
abbrev ofGeodesic {s x : V} (hs : s ∈ T.alive) (p : T.graph.Walk s x)
    (hp : p.IsPath) (hd : T.graph.dist s x = T.diam) : DiamPath T where
  D := p.length
  p i := p.getVert i
  mem i := T.support_subset_alive hs p _ (SimpleGraph.Walk.getVert_mem_support _ _)
  inj := by
    intro i j hij
    exact Fin.ext (hp.getVert_injOn (show (i : ℕ) ≤ p.length by omega)
      (show (j : ℕ) ≤ p.length by omega) hij)
  adj i := p.adj_getVert_succ i.isLt
  isDiam := by simpa using hd

/-- Copy a diameter's vertex sequence to a state with the same relevant edges and distance. -/
abbrev copyPath (Z : DiamPath T) (hm : ∀ i, Z.p i ∈ U.alive)
    (ha : ∀ i : Fin Z.D, U.graph.Adj (Z.p i.castSucc) (Z.p i.succ))
    (hd : U.graph.dist (Z.p 0) (Z.p Z.last) = U.diam) : DiamPath U :=
  ⟨Z.D, Z.p, hm, Z.inj, ha, hd⟩

theorem copyPath_rep (Z : DiamPath T) (hm ha hd) (v : V) :
    (Z.copyPath (U := U) hm ha hd).rep v = Z.rep v := by
  rcases hi : Z.index v with _ | i
  · rw [Z.rep_of_index_none hi]
    exact DiamPath.rep_eq_self _ (Z.index_eq_none_iff.mp hi)
  · rw [← Z.eq_of_index_eq_some hi]
    change (Z.copyPath hm ha hd).rep ((Z.copyPath hm ha hd).p i) = Z.rep (Z.p i)
    rw [(Z.copyPath hm ha hd).rep_path, Z.rep_path]

/-- A fold fixes every vertex at distance at most half its length from its first endpoint. -/
theorem rep_eq_self_of_two_mul_dist_le (Z : DiamPath T) {s x : V} (hs : Z.p 0 = s)
    (hx : 2 * T.graph.dist s x ≤ Z.D) : Z.rep x = x := by
  rcases hi : Z.index x with _ | i
  · exact Z.rep_of_index_none hi
  · have hix := Z.eq_of_index_eq_some hi
    have hiD : (i : ℕ) ≤ Z.D := by have := i.isLt; omega
    have hd := Z.dist_seq_zero hs hiD
    rw [Z.seq_val, hix] at hd
    rw [← hix, ← Z.seq_val]
    exact Z.rep_seq_eq_self (by omega)

/-- A fold disjoint from a set fixes that set pointwise. -/
theorem rep_eq_self_of_mem_avoided (Z : DiamPath T) {D : Set V}
    (hZ : ∀ i, Z.p i ∉ D) {x : V} (hx : x ∈ D) : Z.rep x = x :=
  Z.rep_eq_self fun i hi => hZ i (hi ▸ hx)

/-- A path all of whose vertices are fixed survives a fold. -/
theorem seqPath_fold (Z : DiamPath T) {q : ℕ → V} {L : ℕ}
    (h : SeqPath T q L) (hfix : ∀ k ≤ L, Z.rep (q k) = q k) :
    SeqPath Z.foldState q L := by
  refine ⟨fun k hk => Z.mem_foldAlive.mpr ⟨h.1 k hk, hfix k hk⟩, ?_, h.2.2⟩
  intro k hk
  refine ⟨?_, Z.mem_foldAlive.mpr ⟨h.1 k (by omega), hfix k (by omega)⟩,
    Z.mem_foldAlive.mpr ⟨h.1 (k + 1) (by omega), hfix (k + 1) (by omega)⟩,
    q k, q (k + 1), h.2.1 k hk, hfix k (by omega), hfix (k + 1) (by omega)⟩
  intro heq
  have := h.2.2 k (by omega) (k + 1) (by omega) heq
  omega

/-- Composing an image description with one fold preserves its witness form. -/
theorem fold_image (A : TreeState V) (Z : DiamPath T) (f : V → V)
    (hm : ∀ w, w ∈ T.alive ↔ ∃ v ∈ A.alive, f v = w)
    (ha : ∀ u v, T.graph.Adj u v ↔ u ≠ v ∧ u ∈ T.alive ∧ v ∈ T.alive ∧
      ∃ a b, A.graph.Adj a b ∧ f a = u ∧ f b = v) :
    (∀ w, w ∈ Z.foldState.alive ↔ ∃ v ∈ A.alive, Z.rep (f v) = w) ∧
    (∀ u v, Z.foldState.graph.Adj u v ↔
      u ≠ v ∧ u ∈ Z.foldState.alive ∧ v ∈ Z.foldState.alive ∧
        ∃ a b, A.graph.Adj a b ∧ Z.rep (f a) = u ∧ Z.rep (f b) = v) := by
  constructor
  · intro w
    constructor
    · intro hw
      obtain ⟨hwT, hfix⟩ := Z.mem_foldAlive.mp hw
      obtain ⟨v, hv, hfv⟩ := (hm w).mp hwT
      exact ⟨v, hv, by rw [hfv, hfix]⟩
    · rintro ⟨v, hv, rfl⟩
      exact Z.rep_mem_foldAlive ((hm _).mpr ⟨v, hv, rfl⟩)
  · intro u v
    rw [Z.foldState_graph, Z.foldGraph_adj]
    constructor
    · rintro ⟨hne, hu, hv, x, y, hxy, hxu, hyv⟩
      obtain ⟨-, -, -, a, b, hab, hax, hby⟩ := (ha x y).mp hxy
      exact ⟨hne, hu, hv, a, b, hab, by rw [hax, hxu], by rw [hby, hyv]⟩
    · rintro ⟨hne, hu, hv, a, b, hab, hau, hbv⟩
      have hfa : f a ∈ T.alive := (hm _).mpr ⟨a, (A.adj_alive hab).1, rfl⟩
      have hfb : f b ∈ T.alive := (hm _).mpr ⟨b, (A.adj_alive hab).2, rfl⟩
      have hne' : f a ≠ f b := fun heq => hne (hau.symm.trans ((congrArg Z.rep heq).trans hbv))
      exact ⟨hne, hu, hv, f a, f b, (ha _ _).mpr ⟨hne', hfa, hfb, a, b, hab, rfl, rfl⟩,
        hau, hbv⟩

namespace SyncCtx

variable {P Q : DiamPath S} {T₁ T₂ : TreeState V} {s : V} {σ : V → V}

/-- The leg supplies the stopping scale throughout the synchronized phase. -/
theorem lower_diam (h : SyncCtx P Q s T₁ T₂ σ) :
    2 * (P.D - P.meetIdx Q) ≤ T₁.diam ∧
      2 * (P.D - P.meetIdx Q) ≤ T₂.diam := by
  constructor
  · have hd := h.leg₁.dist_eq (k := 2 * (P.D - P.meetIdx Q)) le_rfl
    have := T₁.dist_le_diam (h.leg₁.1 0 (by omega)) (h.leg₁.1 _ le_rfl)
    omega
  · have hd := h.leg₂.dist_eq (k := 2 * (P.D - P.meetIdx Q)) le_rfl
    have := T₂.dist_le_diam (h.leg₂.1 0 (by omega)) (h.leg₂.1 _ le_rfl)
    omega

/-- Choose the long diameter inside the common part using its avoiding geodesic. -/
theorem exists_avoiding_diamPath (h : SyncCtx P Q s T₁ T₂ σ)
    (hH : 2 * (P.D - P.meetIdx Q) < T₁.diam) :
    ∃ Z : DiamPath T₁, Z.p 0 = s ∧ ∀ i, Z.p i ∉ P.Delta Q s := by
  obtain ⟨x, hx, hdist⟩ := h.end₁.2
  have hxD := h.notMem_delta_of_lt_dist hH hx hdist
  obtain ⟨p, hp, -, havoid⟩ := h.geod₁ x hx hxD
  refine ⟨ofGeodesic h.end₁.1 p hp hdist, ?_, ?_⟩
  · exact SimpleGraph.Walk.getVert_zero p
  · intro i
    exact havoid i (show (i : ℕ) ≤ p.length by have hi : (i : ℕ) < p.length + 1 := i.isLt; omega)

/-- One simultaneous fold preserves the full synchronization invariant. -/
theorem step (h : SyncCtx P Q s T₁ T₂ σ) (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hH : 2 * (P.D - P.meetIdx Q) < T₁.diam) :
    ∃ (Z : DiamPath T₁) (Z₂ : DiamPath T₂),
      Z.p 0 = s ∧ Z₂.p 0 = s ∧
        SyncCtx P Q s Z.foldState Z₂.foldState (Z.rep ∘ σ) := by
  obtain ⟨Z, hZs, hZD⟩ := h.exists_avoiding_diamPath hH
  have hm : ∀ i, Z.p i ∈ T₂.alive :=
    fun i => (h.mem_iff _ (hZD i)).mp (Z.mem i)
  have ha : ∀ i : Fin Z.D, T₂.graph.Adj (Z.p i.castSucc) (Z.p i.succ) :=
    fun i => (h.adj_iff _ _ (hZD _) (hZD _)).mp (Z.adj i)
  have hd : T₂.graph.dist (Z.p 0) (Z.p Z.last) = T₂.diam := by
    rw [hZs, ← h.dist_eq_on_common (Z.mem Z.last) (hZD _), ← hZs]
    exact Z.isDiam.trans h.diam_eq
  let Z₂ := Z.copyPath hm ha hd
  have hrep : ∀ v, Z₂.rep v = Z.rep v := Z.copyPath_rep hm ha hd
  have hZ₂s : Z₂.p 0 = s := hZs
  have hZ₂D : ∀ i, Z₂.p i ∉ P.Delta Q s := hZD
  have hlen : Z.D = T₁.diam := Z.diam_eq_D.symm
  have hfixD : ∀ v ∈ P.Delta Q s, Z.rep v = v :=
    fun _ hv => Z.rep_eq_self_of_mem_avoided hZD hv
  have hcommon : ∀ v, v ∉ P.Delta Q s → Z.rep v ∉ P.Delta Q s :=
    fun _ hv => Z.rep_notMem_of_path_notMem hZD hv
  have hpre : ∀ v, Z.rep v ∉ P.Delta Q s → v ∉ P.Delta Q s := by
    intro v hv hvD
    exact hv ((hfixD v hvD).symm ▸ hvD)
  have hfixs : Z.rep s = s := by
    rw [← hZs, Z.rep_path]
    exact congrArg Z.p (Fin.ext (by simp))
  have hfixsp : ∀ k ≤ P.D - P.meetIdx Q, Z.rep (P.seq k) = P.seq k := by
    intro k hk
    have hdist := h.leg₁.dist_eq (k := k) (by omega)
    rw [P.legSeq_zero Q, P.seq_zero, hP, P.legSeq_of_le Q hk] at hdist
    exact Z.rep_eq_self_of_two_mul_dist_le hZs (by omega)
  have hmeet := P.meetIdx_comm Q (hP.trans hQ.symm)
  have hD := P.D_eq Q
  have hfixleg₁ : ∀ k ≤ 2 * (P.D - P.meetIdx Q), Z.rep (P.legSeq Q k) = P.legSeq Q k := by
    intro k hk
    by_cases hkr : k ≤ P.D - P.meetIdx Q
    · rw [P.legSeq_of_le Q hkr]
      exact hfixsp k hkr
    · apply hfixD
      rw [P.legSeq_of_lt Q (by omega)]
      exact (P.seq_mem_Delta_iff_Q Q hP hQ (by omega)).mpr (by omega)
  have hfixleg₂ : ∀ k ≤ 2 * (P.D - P.meetIdx Q), Z₂.rep (Q.legSeq P k) = Q.legSeq P k := by
    intro k hk
    rw [hrep]
    by_cases hkr : k ≤ P.D - P.meetIdx Q
    · rw [← P.legSeq_eq_legSeq Q (hP.trans hQ.symm) hkr]
      exact hfixleg₁ k hk
    · apply hfixD
      rw [Q.legSeq_of_lt P (by omega)]
      exact (P.seq_mem_Delta_iff Q hP hQ (by omega)).mpr (by omega)
  have hleg₁ := Z.seqPath_fold h.leg₁ hfixleg₁
  have hleg₂ := Z₂.seqPath_fold h.leg₂ hfixleg₂
  have hgeod₁ := h.geod₁.fold Z hZD hcommon hZs
  have hgeod₂ := h.geod₂.fold Z₂ hZ₂D
    (fun v hv => by rw [hrep]; exact hcommon v hv) hZ₂s
  have hmem : ∀ v, v ∉ P.Delta Q s →
      (v ∈ Z.foldState.alive ↔ v ∈ Z₂.foldState.alive) := by
    intro v hv
    change v ∈ Z.foldAlive ↔ v ∈ Z₂.foldAlive
    rw [Z.mem_foldAlive, Z₂.mem_foldAlive, hrep, h.mem_iff v hv]
  have hadj : ∀ u v, u ∉ P.Delta Q s → v ∉ P.Delta Q s →
      (Z.foldState.graph.Adj u v ↔ Z₂.foldState.graph.Adj u v) := by
    intro u v hu hv
    change Z.foldGraph.Adj u v ↔ Z₂.foldGraph.Adj u v
    rw [Z.foldGraph_adj, Z₂.foldGraph_adj]
    constructor
    · rintro ⟨hne, huA, hvA, a, b, hab, hau, hbv⟩
      have haD := hpre a (hau ▸ hu)
      have hbD := hpre b (hbv ▸ hv)
      exact ⟨hne, (hmem u hu).mp huA, (hmem v hv).mp hvA, a, b,
        (h.adj_iff a b haD hbD).mp hab, by rw [hrep, hau], by rw [hrep, hbv]⟩
    · rintro ⟨hne, huA, hvA, a, b, hab, hau, hbv⟩
      rw [hrep] at hau hbv
      have haD := hpre a (hau ▸ hu)
      have hbD := hpre b (hbv ▸ hv)
      exact ⟨hne, (hmem u hu).mpr huA, (hmem v hv).mpr hvA, a, b,
        (h.adj_iff a b haD hbD).mpr hab, hau, hbv⟩
  have hbound₁ : ∀ v, v ∈ P.Delta Q s → v ∈ Z.foldState.alive →
      Z.foldState.graph.dist s v ≤ 2 * (P.D - P.meetIdx Q) := by
    intro v hvD hv
    have hle := Z.fold_dist_le h.end₁.1 (Z.foldAlive_subset hv)
    rw [hfixs, hfixD v hvD] at hle
    exact hle.trans (h.delta_bound₁ v hvD (Z.foldAlive_subset hv))
  have hbound₂ : ∀ v, v ∈ P.Delta Q s → v ∈ Z₂.foldState.alive →
      Z₂.foldState.graph.dist s v ≤ 2 * (P.D - P.meetIdx Q) := by
    intro v hvD hv
    have hle := Z₂.fold_dist_le h.end₂.1 (Z₂.foldAlive_subset hv)
    rw [hrep, hrep, hfixs, hfixD v hvD] at hle
    exact hle.trans (h.delta_bound₂ v hvD (Z₂.foldAlive_subset hv))
  have hend₁ : IsDiamEnd Z.foldState s := by rw [← hZs]; exact isDiamEnd_foldState Z
  have hend₂ : IsDiamEnd Z₂.foldState s := by rw [← hZ₂s]; exact isDiamEnd_foldState Z₂
  have hlo₁ : 2 * (P.D - P.meetIdx Q) ≤ Z.foldState.diam := by
    have hh := hleg₁.dist_eq (k := 2 * (P.D - P.meetIdx Q)) le_rfl
    have := Z.foldState.dist_le_diam (hleg₁.1 0 (by omega)) (hleg₁.1 _ le_rfl)
    omega
  have hlo₂ : 2 * (P.D - P.meetIdx Q) ≤ Z₂.foldState.diam := by
    have hh := hleg₂.dist_eq (k := 2 * (P.D - P.meetIdx Q)) le_rfl
    have := Z₂.foldState.dist_le_diam (hleg₂.1 0 (by omega)) (hleg₂.1 _ le_rfl)
    omega
  have hdiam : Z.foldState.diam = Z₂.foldState.diam := by
    apply le_antisymm
    · obtain ⟨x, hx, hxd⟩ := hend₁.2
      rw [← hxd]
      by_cases hxD : x ∈ P.Delta Q s
      · exact (hbound₁ x hxD hx).trans hlo₂
      · rw [hgeod₁.dist_eq hadj hx hxD]
        exact Z₂.foldState.dist_le_diam hend₂.1 ((hmem x hxD).mp hx)
    · obtain ⟨x, hx, hxd⟩ := hend₂.2
      rw [← hxd]
      by_cases hxD : x ∈ P.Delta Q s
      · exact (hbound₂ x hxD hx).trans hlo₁
      · rw [hgeod₂.dist_eq (fun u v hu hv => (hadj u v hu hv).symm) hx hxD]
        exact Z.foldState.dist_le_diam hend₁.1 ((hmem x hxD).mpr hx)
  obtain ⟨hm₁, ha₁⟩ := fold_image P.foldState Z σ h.alive₁ h.adjdesc₁
  obtain ⟨hm₂, ha₂⟩ := fold_image Q.foldState Z₂ σ h.alive₂ h.adjdesc₂
  refine ⟨Z, Z₂, hZs, hZ₂s, {
    end₁ := hend₁
    end₂ := hend₂
    diam_eq := hdiam
    mem_iff := hmem
    adj_iff := hadj
    delta_bound₁ := hbound₁
    delta_bound₂ := hbound₂
    geod₁ := hgeod₁
    geod₂ := hgeod₂
    leg₁ := hleg₁
    leg₂ := hleg₂
    alive₁ := hm₁
    alive₂ := ?_
    adjdesc₁ := ha₁
    adjdesc₂ := ?_
    sigma_idem := ?_
    sigma_delta := ?_
    sigma_common := ?_
    sigma_spine := ?_ }⟩
  · simpa only [Function.comp_apply, hrep] using hm₂
  · simpa only [Function.comp_apply, hrep] using ha₂
  · intro v
    simp only [Function.comp_apply]
    rcases hi : Z.index (σ v) with _ | i
    · rw [Z.rep_of_index_none hi, h.sigma_idem, Z.rep_of_index_none hi]
    · rw [Z.rep_of_index_some hi]
      rw [h.sigma_fix₁ (Z.mem _)]
      simpa only [Z.rep_path i] using Z.rep_idem (Z.p i)
  · intro v hv
    simp only [Function.comp_apply, h.sigma_delta v hv, hfixD v hv]
  · intro v hv
    exact hcommon _ (h.sigma_common v hv)
  · intro k hk
    simp only [Function.comp_apply, h.sigma_spine k hk, hfixsp k hk]

/-- Synchronized folds stop exactly when the persistent leg becomes a diameter. -/
theorem reach_scale_aux (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    ∀ N (T₁ T₂ : TreeState V) (σ : V → V),
      T₁.alive.card ≤ N → SyncCtx P Q s T₁ T₂ σ →
      ∃ m U₁ U₂ τ, FoldSeqAt s T₁ U₁ m ∧ FoldSeqAt s T₂ U₂ m ∧
        SyncCtx P Q s U₁ U₂ τ ∧ U₁.diam = 2 * (P.D - P.meetIdx Q) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro T₁ T₂ σ hcard h
    by_cases heq : T₁.diam = 2 * (P.D - P.meetIdx Q)
    · exact ⟨0, T₁, T₂, σ, .refl _, .refl _, h, heq⟩
    · have hH : 2 * (P.D - P.meetIdx Q) < T₁.diam := by
        have := h.lower_diam.1
        omega
      obtain ⟨Z, Z₂, hZ, hZ₂, hnext⟩ := h.step hP hQ hH
      have hpos₁ : 2 ≤ T₁.alive.card :=
        Z.two_le_card (by rw [← Z.diam_eq_D]; omega)
      have hpos₂ : 2 ≤ T₂.alive.card :=
        Z₂.two_le_card (by rw [← Z₂.diam_eq_D, ← h.diam_eq]; omega)
      have hlt := FoldStep.card_lt (S := T₁) ⟨Z, rfl⟩ hpos₁
      obtain ⟨m, U₁, U₂, τ, h₁, h₂, hctx, hdiam⟩ :=
        ih Z.foldState.alive.card (by omega) Z.foldState Z₂.foldState _ le_rfl hnext
      exact ⟨m + 1, U₁, U₂, τ,
        .step hpos₁ ⟨Z, hZ, rfl⟩ h₁, .step hpos₂ ⟨Z₂, hZ₂, rfl⟩ h₂, hctx, hdiam⟩

theorem reach_scale (h : SyncCtx P Q s T₁ T₂ σ) (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    ∃ m U₁ U₂ τ, FoldSeqAt s T₁ U₁ m ∧ FoldSeqAt s T₂ U₂ m ∧
      SyncCtx P Q s U₁ U₂ τ ∧ U₁.diam = 2 * (P.D - P.meetIdx Q) :=
  reach_scale_aux hP hQ T₁.alive.card T₁ T₂ σ le_rfl h

end SyncCtx
end DiamPath
end OhtoaiTreeProof
