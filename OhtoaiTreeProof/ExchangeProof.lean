/-
# REF.md Lemma 5 (§7): the endgame and the assembly

`OhtoaiTreeProof/ExchangeLemma5.lean` proves the two ends of the `REF.md` §7 argument (the
combinatorics of the two diameters and the structure of the two folded states, in particular
`dist_leg`/`dist_leg'`: the *leg* of `P.foldState` — the surviving half of the `P`-diameter
followed by the surviving `Q`-tail — has length exactly `2r`).  This file proves the **endgame**
and the **assembly**:

* **The endgame (§1–§3).**  When the two states `P.foldState` and `Q.foldState` have diameter
  `2r`, the leg of each of them is a diameter path starting at `s`.  Folding `P.foldState` along
  its leg lays the surviving `Q`-tail onto the spine `p 0, …, p r` and moves every subtree hanging
  off it to `p (r - t)`; folding `Q.foldState` along *its* leg does the same thing to the `P`-tail.
  Both operations are therefore the *same* collapse of the original tree `S`, and the two results
  are literally the same state.  The formal statement is `legPath_foldState_eq` and its packaged
  form `endgame`.

  The proof goes through the composite maps `σ₁ = ρ₁ ∘ P.rep` and `σ₂ = ρ₂ ∘ Q.rep` (`ρ₁`, `ρ₂`
  being the folding maps of the two legs): one checks vertex by vertex that `σ₁ = σ₂`
  (`legPath_rep_rep`).  Both folded states are then the "image" of `S` under that single map, which
  makes their vertex sets (`legPath_foldAlive_eq`) and their edge relations
  (`legPath_foldGraph_adj`) equal.

* **The assembly (§4).**  A synchronised phase followed by the endgame gives, for the two states
  `P.foldState`, `Q.foldState`, complete folding processes of the same length: `exchange_of_endgame`
  reduces `exchange` to the single remaining input, namely that the synchronised phase can be run
  until the diameter is `2r` and that the endgame then applies to the pair it produces
  (obligations (a)/(b) of `ExchangeLemma5.lean` §4).
-/
import OhtoaiTreeProof.ExchangeLemma5
import OhtoaiTreeProof.Cone
import OhtoaiTreeProof.Iso
import OhtoaiTreeProof.Progress

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 0. Two states with the same data are equal -/

/-- Two states with the same live vertices and the same graph are equal: the remaining fields are
proofs of propositions. -/
theorem TreeState.ext {S S' : TreeState V} (ha : S.alive = S'.alive) (hg : S.graph = S'.graph) :
    S = S' := by
  obtain ⟨a, g, p1, p2, p3⟩ := S
  obtain ⟨a', g', p1', p2', p3'⟩ := S'
  dsimp only at ha hg
  subst ha
  subst hg
  congr 1

/-- Two graphs with the same adjacency relation are equal. -/
theorem SimpleGraph.eq_of_adj_iff {G H : SimpleGraph V} (h : ∀ u v, G.Adj u v ↔ H.Adj u v) :
    G = H :=
  SimpleGraph.ext (funext fun u => funext fun v => propext (h u v))

namespace DiamPath

variable {S : TreeState V}

/-! ## 1. The leg as a diameter path

`legPath` is the leg `legSeq` of `ExchangeLemma5.lean`, packaged as a `DiamPath` of the folded
state.  It starts at `s` and has length `2r`; it is a diameter of `P.foldState` exactly when the
diameter of `P.foldState` is `2r`. -/

/-- **The leg of `P.foldState` as a diameter path.**  The vertices are `P.seq 0, …, P.seq r`
followed by the surviving `Q`-tail `Q.seq (ℓ+1), …, Q.seq D`. -/
noncomputable abbrev legPath (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q)) :
    DiamPath P.foldState where
  D := 2 * (P.D - P.meetIdx Q)
  p := fun i => P.legSeq Q (i : ℕ)
  mem := fun i => P.legSeq_mem Q hP hQ hr (by have := i.isLt; omega)
  inj := fun i j hij =>
    Fin.ext (P.legSeq_inj Q hP hQ hr (i : ℕ) (by have := i.isLt; omega) (j : ℕ)
      (by have := j.isLt; omega) hij)
  adj := fun i => by
    have h := P.legSeq_adj Q hP hQ hr (i : ℕ) (by have := i.isLt; omega)
    show P.foldGraph.Adj (P.legSeq Q (i : ℕ)) (P.legSeq Q ((i : ℕ) + 1))
    simpa only [Fin.val_castSucc, Fin.val_succ] using h
  isDiam := by
    show P.foldGraph.dist (P.legSeq Q 0) (P.legSeq Q (2 * (P.D - P.meetIdx Q))) = P.foldState.diam
    rw [P.legSeq_zero Q, P.legSeq_two_mul Q hr, P.dist_leg Q hP hQ hr, hdiam]

theorem legPath_D (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q)) :
    (P.legPath Q hP hQ hr hdiam).D = 2 * (P.D - P.meetIdx Q) := rfl

/-- The `k`-th vertex of the leg, in `ℕ`-indexed form. -/
theorem legPath_p_val (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    (k : ℕ) (hk : k ≤ 2 * (P.D - P.meetIdx Q)) :
    (P.legPath Q hP hQ hr hdiam).p ⟨k, by show k < 2 * (P.D - P.meetIdx Q) + 1; omega⟩ =
      P.legSeq Q k := rfl

/-- The leg starts at `s`. -/
theorem legPath_p_zero (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q)) :
    (P.legPath Q hP hQ hr hdiam).p 0 = s := by
  show P.legSeq Q ((0 : Fin (2 * (P.D - P.meetIdx Q) + 1)) : ℕ) = s
  rw [Fin.val_zero, P.legSeq_zero Q, P.seq_zero, hP]

/-- **The folding map of the leg, on the leg.**  The `k`-th vertex of the leg is sent to the
mirror vertex `min k (2r - k)`. -/
theorem legPath_rep_legSeq_fin (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    (i : Fin (2 * (P.D - P.meetIdx Q) + 1)) :
    (P.legPath Q hP hQ hr hdiam).rep ((P.legPath Q hP hQ hr hdiam).p i) =
      P.legSeq Q (min (i : ℕ) (2 * (P.D - P.meetIdx Q) - (i : ℕ))) := by
  rw [DiamPath.rep_path]

/-- **The folding map of the leg, on the leg** (`ℕ`-indexed form). -/
theorem legPath_rep_legSeq (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    {k : ℕ} (hk : k ≤ 2 * (P.D - P.meetIdx Q)) :
    (P.legPath Q hP hQ hr hdiam).rep (P.legSeq Q k) =
      P.legSeq Q (min k (2 * (P.D - P.meetIdx Q) - k)) := by
  have hp : (P.legPath Q hP hQ hr hdiam).p ⟨k, by show k < 2 * (P.D - P.meetIdx Q) + 1; omega⟩ =
      P.legSeq Q k := rfl
  rw [← hp, P.legPath_rep_legSeq_fin Q hP hQ hr hdiam]

/-- The folding map of the leg is the identity away from the leg. -/
theorem legPath_rep_eq_self (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    {v : V} (h : ∀ k ≤ 2 * (P.D - P.meetIdx Q), P.legSeq Q k ≠ v) :
    (P.legPath Q hP hQ hr hdiam).rep v = v := by
  rw [DiamPath.rep_eq_self]
  intro i hi
  have hD := P.legPath_D Q hP hQ hr hdiam
  exact h (i : ℕ) (by have := i.isLt; omega) hi

/-- A vertex of the leg is a vertex of one of the two diameters; hence a vertex lying on neither
diameter is not on the leg. -/
theorem legSeq_ne_of_index_none (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {v : V} (hPv : ∀ i : Fin (P.D + 1), P.p i ≠ v) (hQv : ∀ i : Fin (Q.D + 1), Q.p i ≠ v) :
    ∀ k ≤ 2 * (P.D - P.meetIdx Q), P.legSeq Q k ≠ v := by
  intro k hk hc
  have htw := P.two_mul_tail_le Q hP hQ
  by_cases h : k ≤ P.D - P.meetIdx Q
  · rw [P.legSeq_of_le Q h] at hc
    exact hPv ⟨k, by omega⟩ (by rw [← P.seq_val, ← hc])
  · rw [P.legSeq_of_lt Q (by omega)] at hc
    refine hQv ⟨P.meetIdx Q + (k - (P.D - P.meetIdx Q)), ?_⟩ ?_
    · have hdi := P.D_eq Q; omega
    · rw [← Q.seq_val, ← hc]

/-- A vertex `P.seq m` with `r < m ≤ ℓ` is not a vertex of the leg. -/
theorem legSeq_ne_seq_of_lt (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {m : ℕ} (hm1 : P.D - P.meetIdx Q < m) (hm2 : m ≤ P.meetIdx Q) :
    ∀ k ≤ 2 * (P.D - P.meetIdx Q), P.legSeq Q k ≠ P.seq m := by
  intro k hk hc
  have htw := P.two_mul_tail_le Q hP hQ
  have hmD : m ≤ P.D := le_trans hm2 (P.meetIdx_le Q)
  by_cases h : k ≤ P.D - P.meetIdx Q
  · rw [P.legSeq_of_le Q h] at hc
    have := P.seq_inj k (by omega) m hmD hc
    omega
  · rw [P.legSeq_of_lt Q (by omega)] at hc
    have hj : P.meetIdx Q + (k - (P.D - P.meetIdx Q)) ≤ Q.D := by
      have hdi := P.D_eq Q
      omega
    have h1 := Q.dist_seq_zero hQ hj
    have h2 := P.dist_seq_zero hP hmD
    rw [hc] at h1
    omega

/-- **The leg of `P.foldState` fixes the common prefix `p 0, …, p ℓ` of the two diameters.** -/
theorem legPath_rep_le (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    {m : ℕ} (hm : m ≤ P.meetIdx Q) :
    (P.legPath Q hP hQ hr hdiam).rep (P.seq m) = P.seq m := by
  have htw := P.two_mul_tail_le Q hP hQ
  by_cases h : m ≤ P.D - P.meetIdx Q
  · rw [← P.legSeq_of_le Q h, P.legPath_rep_legSeq Q hP hQ hr hdiam (by omega),
      show min m (2 * (P.D - P.meetIdx Q) - m) = m by omega]
  · rw [P.legPath_rep_eq_self Q hP hQ hr hdiam (P.legSeq_ne_seq_of_lt Q hP hQ (by omega) hm)]

/-- **The leg of `P.foldState` maps the `t`-th vertex of the surviving `Q`-tail to `P.seq (r-t)`.**
This is `REF.md` §7: after folding `P.foldState` along its leg, the `Q`-tail lies on the spine. -/
theorem legPath_rep_tail (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    {t : ℕ} (ht : 1 ≤ t) (htr : t ≤ P.D - P.meetIdx Q) :
    (P.legPath Q hP hQ hr hdiam).rep (Q.seq (P.meetIdx Q + t)) =
      P.seq (P.D - P.meetIdx Q - t) := by
  have htw := P.two_mul_tail_le Q hP hQ
  have hleg : P.legSeq Q (P.D - P.meetIdx Q + t) = Q.seq (P.meetIdx Q + t) := by
    rw [P.legSeq_of_lt Q (by omega)]
    congr 1
    omega
  rw [← hleg, P.legPath_rep_legSeq Q hP hQ hr hdiam (by omega),
    show min (P.D - P.meetIdx Q + t) (2 * (P.D - P.meetIdx Q) - (P.D - P.meetIdx Q + t))
      = P.D - P.meetIdx Q - t by omega]
  exact P.legSeq_of_le Q (by omega)

/-! ## 2. The two folds are the same map

`P.seq i = Q.seq j` with `i, j ≤ D` forces `i = j ≤ ℓ`: the two diameters can only meet on the
common prefix.  Consequently a vertex of `S` either lies on the `P`-diameter, or on the
`Q`-diameter, or on neither, and in each case the two composites `ρ₁ ∘ P.rep` and `ρ₂ ∘ Q.rep`
agree. -/

/-- **Two vertices of the two diameters that coincide have the same index, on the common prefix.** -/
theorem seq_eq_seq_iff (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {i j : ℕ} (hi : i ≤ P.D) (hj : j ≤ Q.D) (h : P.seq i = Q.seq j) :
    i = j ∧ i ≤ P.meetIdx Q := by
  have h1 : S.graph.dist s (P.seq i) = i := P.dist_seq_zero hP hi
  have h2 : S.graph.dist s (Q.seq j) = j := Q.dist_seq_zero hQ hj
  have hij : i = j := by rw [← h1, h, h2]
  subst hij
  refine ⟨rfl, ?_⟩
  by_contra hcon
  exact absurd (P.meetIdx_max Q (i := i) hi h) (by omega)

/-- **The two folds are the same map.**  The composite of the folding map of the `P`-diameter with
the folding map of the leg of `P.foldState` equals the analogous composite for `Q`: both send a
vertex of `S` to its image in the common final state. -/
theorem legPath_rep_rep (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    (hmeet : Q.meetIdx P = P.meetIdx Q) (hD : Q.D = P.D)
    (hdiam₂ : Q.foldState.diam = 2 * (Q.D - Q.meetIdx P)) (v : V) :
    (P.legPath Q hP hQ hr hdiam).rep (P.rep v) =
      (Q.legPath P hQ hP (by omega) hdiam₂).rep (Q.rep v) := by
  have htw := P.two_mul_tail_le Q hP hQ
  have hℓr := P.meetIdx_add_tail Q
  have htail := P.tail_le_meetIdx Q hP hQ
  have hDp : P.D = Q.D := P.D_eq Q
  rcases hv : P.index v with _ | i
  · rcases hw : Q.index v with _ | j
    · -- `v` lies on neither diameter: both folds fix it
      have hv' := P.index_eq_none_iff.mp hv
      have hw' := Q.index_eq_none_iff.mp hw
      rw [P.rep_of_index_none hv, Q.rep_of_index_none hw,
        P.legPath_rep_eq_self Q hP hQ hr hdiam (P.legSeq_ne_of_index_none Q hP hQ hv' hw'),
        Q.legPath_rep_eq_self P hQ hP (by omega) hdiam₂ (Q.legSeq_ne_of_index_none P hQ hP hw' hv')]
    · -- `v = Q.seq j` with `ℓ < j`
      have hqv : Q.p j = v := Q.eq_of_index_eq_some hw
      have hPv : ∀ i : Fin (P.D + 1), P.p i ≠ v := P.index_eq_none_iff.mp hv
      have hjD : (j : ℕ) ≤ Q.D := by have := j.isLt; omega
      have hjℓ : P.meetIdx Q < (j : ℕ) := by
        by_contra hcon
        have hseq : Q.seq (j : ℕ) = P.seq (j : ℕ) :=
          (P.seq_eq_of_le_meetIdx Q hP hQ (by omega)).symm
        exact hPv ⟨(j : ℕ), by omega⟩ (by rw [← P.seq_val, ← hseq, Q.seq_val, hqv])
      have ht1 : 1 ≤ (j : ℕ) - P.meetIdx Q := by omega
      have htr : (j : ℕ) - P.meetIdx Q ≤ P.D - P.meetIdx Q := by omega
      have h₁ : (P.legPath Q hP hQ hr hdiam).rep (P.rep v) =
          P.seq (P.D - P.meetIdx Q - ((j : ℕ) - P.meetIdx Q)) := by
        have hvq : v = Q.seq (P.meetIdx Q + ((j : ℕ) - P.meetIdx Q)) := by
          rw [← hqv, ← Q.seq_val]
          congr 1
          omega
        rw [P.rep_of_index_none hv, hvq]
        exact P.legPath_rep_tail Q hP hQ hr hdiam ht1 htr
      have h₂ : (Q.legPath P hQ hP (by omega) hdiam₂).rep (Q.rep v) =
          P.seq (P.D - P.meetIdx Q - ((j : ℕ) - P.meetIdx Q)) := by
        have hqj : Q.rep v = Q.seq (Q.D - (j : ℕ)) := by
          rw [← hqv, ← Q.seq_val, Q.rep_seq hjD]
          congr 1
          omega
        have hvq : Q.D - (j : ℕ) =
            Q.D - Q.meetIdx P - ((j : ℕ) - P.meetIdx Q) := by omega
        have hfix : (Q.legPath P hQ hP (by omega) hdiam₂).rep
            (Q.seq (Q.D - Q.meetIdx P - ((j : ℕ) - P.meetIdx Q))) =
            Q.seq (Q.D - Q.meetIdx P - ((j : ℕ) - P.meetIdx Q)) :=
          Q.legPath_rep_le P hQ hP (by omega) hdiam₂ (by omega)
        have hcommon : Q.seq (Q.D - Q.meetIdx P - ((j : ℕ) - P.meetIdx Q)) =
            P.seq (P.D - P.meetIdx Q - ((j : ℕ) - P.meetIdx Q)) := by
          have h1 : Q.D - Q.meetIdx P - ((j : ℕ) - P.meetIdx Q) =
              P.D - P.meetIdx Q - ((j : ℕ) - P.meetIdx Q) := by omega
          rw [h1]
          exact (P.seq_eq_of_le_meetIdx Q hP hQ (by omega)).symm
        rw [hqj, hvq, hfix, hcommon]
      rw [h₁, h₂]
  · -- `v = P.seq i` with `i ≤ D`
    have hpv : P.p i = v := P.eq_of_index_eq_some hv
    have hiD : (i : ℕ) ≤ P.D := by have := i.isLt; omega
    rcases hw : Q.index v with _ | j
    · -- `v = P.seq i` with `ℓ < i`
      have hQv : ∀ j : Fin (Q.D + 1), Q.p j ≠ v := Q.index_eq_none_iff.mp hw
      have hiℓ : P.meetIdx Q < (i : ℕ) := by
        by_contra hcon
        have hseq : P.seq (i : ℕ) = Q.seq (i : ℕ) := P.seq_eq_of_le_meetIdx Q hP hQ (by omega)
        exact hQv ⟨(i : ℕ), by omega⟩ (by rw [← Q.seq_val, ← hseq, P.seq_val, hpv])
      have h₁ : (P.legPath Q hP hQ hr hdiam).rep (P.rep v) =
          P.seq (P.D - P.meetIdx Q - ((i : ℕ) - P.meetIdx Q)) := by
        have hm : min (i : ℕ) (P.D - (i : ℕ)) = P.D - (i : ℕ) := by omega
        rw [← hpv, ← P.seq_val, P.rep_seq hiD, hm]
        have hfix : (P.legPath Q hP hQ hr hdiam).rep (P.seq (P.D - (i : ℕ))) =
            P.seq (P.D - (i : ℕ)) :=
          P.legPath_rep_le Q hP hQ hr hdiam (by omega)
        rw [hfix]
        congr 1
        omega
      have h₂ : (Q.legPath P hQ hP (by omega) hdiam₂).rep (Q.rep v) =
          P.seq (P.D - P.meetIdx Q - ((i : ℕ) - P.meetIdx Q)) := by
        have hvq : v = P.seq (P.meetIdx Q + ((i : ℕ) - P.meetIdx Q)) := by
          rw [← hpv, ← P.seq_val]
          congr 1
          omega
        have hleg : Q.legSeq P (Q.D - Q.meetIdx P + ((i : ℕ) - P.meetIdx Q)) =
            P.seq (P.meetIdx Q + ((i : ℕ) - P.meetIdx Q)) := by
          rw [Q.legSeq_of_lt P (by omega)]
          congr 1
          omega
        rw [Q.rep_of_index_none hw, hvq, ← hleg,
          Q.legPath_rep_legSeq P hQ hP (by omega) hdiam₂ (k := Q.D - Q.meetIdx P +
            ((i : ℕ) - P.meetIdx Q)) (by omega),
          show min (Q.D - Q.meetIdx P + ((i : ℕ) - P.meetIdx Q))
              (2 * (Q.D - Q.meetIdx P) - (Q.D - Q.meetIdx P + ((i : ℕ) - P.meetIdx Q)))
            = Q.D - Q.meetIdx P - ((i : ℕ) - P.meetIdx Q) by omega,
          Q.legSeq_of_le P (by omega)]
        have hcommon : Q.seq (Q.D - Q.meetIdx P - ((i : ℕ) - P.meetIdx Q)) =
            P.seq (P.D - P.meetIdx Q - ((i : ℕ) - P.meetIdx Q)) := by
          have h1 : Q.D - Q.meetIdx P - ((i : ℕ) - P.meetIdx Q) =
              P.D - P.meetIdx Q - ((i : ℕ) - P.meetIdx Q) := by omega
          rw [h1]
          exact (P.seq_eq_of_le_meetIdx Q hP hQ (by omega)).symm
        rw [hcommon]
      rw [h₁, h₂]
    · -- `v = P.seq i = Q.seq j` with `i = j ≤ ℓ`
      have hqv : Q.p j = v := Q.eq_of_index_eq_some hw
      have hjD : (j : ℕ) ≤ Q.D := by have := j.isLt; omega
      have hseqij : P.seq (i : ℕ) = Q.seq (j : ℕ) := by
        rw [P.seq_val, Q.seq_val, hpv, hqv]
      obtain ⟨hij, hiℓ⟩ := P.seq_eq_seq_iff Q hP hQ hiD hjD hseqij
      have h₁ : (P.legPath Q hP hQ hr hdiam).rep (P.rep v) =
          P.seq (min (i : ℕ) (P.D - (i : ℕ))) := by
        rw [← hpv, ← P.seq_val, P.rep_seq hiD]
        exact P.legPath_rep_le Q hP hQ hr hdiam (by omega)
      have h₂ : (Q.legPath P hQ hP (by omega) hdiam₂).rep (Q.rep v) =
          Q.seq (min (j : ℕ) (Q.D - (j : ℕ))) := by
        rw [← hqv, ← Q.seq_val, Q.rep_seq hjD]
        exact Q.legPath_rep_le P hQ hP (by omega) hdiam₂ (by omega)
      have hval : P.seq (min (i : ℕ) (P.D - (i : ℕ))) =
          Q.seq (min (j : ℕ) (Q.D - (j : ℕ))) := by
        have hmin : min (i : ℕ) (P.D - (i : ℕ)) = min (j : ℕ) (Q.D - (j : ℕ)) := by omega
        rw [hmin]
        exact P.seq_eq_of_le_meetIdx Q hP hQ (by omega)
      rw [h₁, h₂, hval]

/-! ## 3. The two folded states are the same state

The two composites of §2 both collapse `S` onto the same set of representatives, so the two
folded states have the same vertices and the same edges. -/

/-- The vertex set of the folded state is `foldAlive`. -/
theorem foldState_alive (P : DiamPath S) : P.foldState.alive = P.foldAlive := rfl

/-- The graph of the folded state is `foldGraph`. -/
theorem foldState_graph (P : DiamPath S) : P.foldState.graph = P.foldGraph := rfl

/-- **Generic form.**  Let `T₁`, `T₂` be the states obtained from `S` by folding along the
diameters `P`, `Q`, and let `Z₁`, `Z₂` be diameter paths of `T₁`, `T₂` whose folding maps satisfy
`ρ₁ ∘ P.rep = ρ₂ ∘ Q.rep` (they induce the *same* collapse of `S`).  Then the two folds agree.

The two vertex sets are both `σ '' S.alive` for the common composite `σ`, and the edge relations
are read off from the witness description `foldGraph_adj` of the folded graphs. -/
theorem foldState_eq_of_rep_comp (P Q : DiamPath S) (Z₁ : DiamPath P.foldState)
    (Z₂ : DiamPath Q.foldState) (hσ : ∀ v : V, Z₁.rep (P.rep v) = Z₂.rep (Q.rep v)) :
    Z₁.foldState = Z₂.foldState := by
  have key₁ : ∀ w : V, w ∈ Z₁.foldAlive ↔ ∃ v ∈ S.alive, Z₁.rep (P.rep v) = w := by
    intro w
    constructor
    · intro hw
      obtain ⟨hw', hfix⟩ := Z₁.mem_foldAlive.mp hw
      rw [P.foldState_alive] at hw'
      obtain ⟨hw'', hrep⟩ := P.mem_foldAlive.mp hw'
      exact ⟨w, hw'', by rw [hrep]; exact hfix⟩
    · rintro ⟨v, hv, rfl⟩
      exact Z₁.rep_mem_foldAlive (by rw [P.foldState_alive]; exact P.rep_mem_foldAlive hv)
  have key₂ : ∀ w : V, w ∈ Z₂.foldAlive ↔ ∃ v ∈ S.alive, Z₂.rep (Q.rep v) = w := by
    intro w
    constructor
    · intro hw
      obtain ⟨hw', hfix⟩ := Z₂.mem_foldAlive.mp hw
      rw [Q.foldState_alive] at hw'
      obtain ⟨hw'', hrep⟩ := Q.mem_foldAlive.mp hw'
      exact ⟨w, hw'', by rw [hrep]; exact hfix⟩
    · rintro ⟨v, hv, rfl⟩
      exact Z₂.rep_mem_foldAlive (by rw [Q.foldState_alive]; exact Q.rep_mem_foldAlive hv)
  have hAlive : Z₁.foldAlive = Z₂.foldAlive := by
    refine Finset.ext fun w => ?_
    rw [key₁ w, key₂ w]
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by rw [← hσ v]; exact h⟩
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by rw [hσ v]; exact h⟩
  -- the adjacency relation of each folded graph, in terms of the composite map on `S`
  have mid₁ : ∀ u v : V, Z₁.foldGraph.Adj u v ↔ u ≠ v ∧ u ∈ Z₁.foldAlive ∧ v ∈ Z₁.foldAlive ∧
      ∃ a b, S.graph.Adj a b ∧ Z₁.rep (P.rep a) = u ∧ Z₁.rep (P.rep b) = v := by
    intro u v
    rw [Z₁.foldGraph_adj]
    constructor
    · rintro ⟨hne, hu, hv, x, y, hxy, hxu, hyv⟩
      rw [P.foldState_graph] at hxy
      obtain ⟨-, -, -, a, b, hab, ha, hb⟩ := P.foldGraph_adj.mp hxy
      exact ⟨hne, hu, hv, a, b, hab, by rw [ha]; exact hxu, by rw [hb]; exact hyv⟩
    · rintro ⟨hne, hu, hv, a, b, hab, hau, hbv⟩
      obtain ⟨ha, hb⟩ := S.adj_alive hab
      have hrep : P.rep a ≠ P.rep b := by
        intro heq
        exact hne (by rw [← hau, ← hbv, heq])
      have hadj : P.foldGraph.Adj (P.rep a) (P.rep b) := by
        rw [P.foldGraph_adj]
        exact ⟨hrep, P.rep_mem_foldAlive ha, P.rep_mem_foldAlive hb, a, b, hab, rfl, rfl⟩
      exact ⟨hne, hu, hv, P.rep a, P.rep b, hadj, hau, hbv⟩
  have mid₂ : ∀ u v : V, Z₂.foldGraph.Adj u v ↔ u ≠ v ∧ u ∈ Z₂.foldAlive ∧ v ∈ Z₂.foldAlive ∧
      ∃ a b, S.graph.Adj a b ∧ Z₂.rep (Q.rep a) = u ∧ Z₂.rep (Q.rep b) = v := by
    intro u v
    rw [Z₂.foldGraph_adj]
    constructor
    · rintro ⟨hne, hu, hv, x, y, hxy, hxu, hyv⟩
      rw [Q.foldState_graph] at hxy
      obtain ⟨-, -, -, a, b, hab, ha, hb⟩ := Q.foldGraph_adj.mp hxy
      exact ⟨hne, hu, hv, a, b, hab, by rw [ha]; exact hxu, by rw [hb]; exact hyv⟩
    · rintro ⟨hne, hu, hv, a, b, hab, hau, hbv⟩
      obtain ⟨ha, hb⟩ := S.adj_alive hab
      have hrep : Q.rep a ≠ Q.rep b := by
        intro heq
        exact hne (by rw [← hau, ← hbv, heq])
      have hadj : Q.foldGraph.Adj (Q.rep a) (Q.rep b) := by
        rw [Q.foldGraph_adj]
        exact ⟨hrep, Q.rep_mem_foldAlive ha, Q.rep_mem_foldAlive hb, a, b, hab, rfl, rfl⟩
      exact ⟨hne, hu, hv, Q.rep a, Q.rep b, hadj, hau, hbv⟩
  refine TreeState.ext ?_ ?_
  · show Z₁.foldAlive = Z₂.foldAlive
    exact hAlive
  · refine SimpleGraph.eq_of_adj_iff fun u v => ?_
    show Z₁.foldGraph.Adj u v ↔ Z₂.foldGraph.Adj u v
    rw [mid₁ u v, mid₂ u v, hAlive]
    constructor
    · rintro ⟨hne, hu, hv, a, b, hab, hau, hbv⟩
      exact ⟨hne, hu, hv, a, b, hab, by rw [← hσ a]; exact hau, by rw [← hσ b]; exact hbv⟩
    · rintro ⟨hne, hu, hv, a, b, hab, hau, hbv⟩
      exact ⟨hne, hu, hv, a, b, hab, by rw [hσ a]; exact hau, by rw [hσ b]; exact hbv⟩

/-- **The endgame.**  When the two folded states have diameter `2r`, folding each of them along its
leg gives the *same* state: both agree with the common collapse of `S` computed in §2. -/
theorem legPath_foldState_eq (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    (hr₂ : 1 ≤ Q.D - Q.meetIdx P) (hdiam₂ : Q.foldState.diam = 2 * (Q.D - Q.meetIdx P))
    (hmeet : Q.meetIdx P = P.meetIdx Q) (hD : Q.D = P.D) :
    (P.legPath Q hP hQ hr hdiam).foldState =
      (Q.legPath P hQ hP hr₂ hdiam₂).foldState :=
  foldState_eq_of_rep_comp P Q _ _ (fun v => P.legPath_rep_rep Q hP hQ hr hdiam hmeet hD hdiam₂ v)

/-- **Both folded states contain the leg**, so both diameters are at least `2 r`.  This is the easy
half of the missing equality `P.foldState.diam = Q.foldState.diam`. -/
theorem two_mul_tail_le_diam (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) : 2 * (P.D - P.meetIdx Q) ≤ P.foldState.diam := by
  have hmem₁ : P.seq 0 ∈ P.foldState.alive := by
    rw [P.foldState_alive, ← P.legSeq_zero Q]
    exact P.legSeq_mem Q hP hQ hr (k := 0) (by omega)
  have hmem₂ : Q.seq Q.D ∈ P.foldState.alive := by
    rw [P.foldState_alive, ← P.legSeq_two_mul Q hr]
    exact P.legSeq_mem Q hP hQ hr (k := 2 * (P.D - P.meetIdx Q)) (by omega)
  have hdist : P.foldState.graph.dist (P.seq 0) (Q.seq Q.D) = 2 * (P.D - P.meetIdx Q) :=
    P.dist_leg Q hP hQ hr
  have h := TreeState.dist_le_diam (S := P.foldState) hmem₁ hmem₂
  rwa [hdist] at h

/-- The same lower bound on the `Q`-side. -/
theorem two_mul_tail_le_diam' (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hr₂ : 1 ≤ Q.D - Q.meetIdx P) :
    2 * (P.D - P.meetIdx Q) ≤ Q.foldState.diam := by
  have hmem₁ : P.seq 0 ∈ Q.foldState.alive := by
    rw [Q.foldState_alive, show P.seq 0 = Q.p 0 by rw [P.seq_zero, hP, hQ]]
    exact (Q.path_mem_foldAlive (i := 0)).mpr (by simp)
  have hmem₂ : P.seq P.D ∈ Q.foldState.alive := by
    rw [Q.foldState_alive, ← Q.legSeq_two_mul P hr₂]
    exact Q.legSeq_mem P hQ hP hr₂ (k := 2 * (Q.D - Q.meetIdx P)) (by omega)
  have hdist : Q.foldState.graph.dist (P.seq 0) (P.seq P.D) = 2 * (P.D - P.meetIdx Q) :=
    P.dist_leg' Q hP hQ hr
  have h := TreeState.dist_le_diam (S := Q.foldState) hmem₁ hmem₂
  rwa [hdist] at h

end DiamPath

/-! ## 4. The assembly -/

/-- **The two states admit one further common fold.**  This is the output of the endgame: diameter
paths of the two states, starting at `s`, with the same folded state. -/
def CommonEndgame (T₁ T₂ : TreeState V) (s : V) : Prop :=
  ∃ (Z₁ : DiamPath T₁) (Z₂ : DiamPath T₂), 1 ≤ Z₁.D ∧ 1 ≤ Z₂.D ∧ Z₁.p 0 = s ∧ Z₂.p 0 = s ∧
    Z₁.foldState = Z₂.foldState

/-- Two states that admit a common fold have at least two vertices each. -/
theorem CommonEndgame.card_le {T₁ T₂ : TreeState V} {s : V} (h : CommonEndgame T₁ T₂ s) :
    2 ≤ T₁.alive.card ∧ 2 ≤ T₂.alive.card := by
  obtain ⟨Z₁, Z₂, hD₁, hD₂, h₁, h₂, -⟩ := h
  have hne₁ : Z₁.p 0 ≠ Z₁.p Z₁.last := by
    intro heq
    have hv : (0 : ℕ) = Z₁.D := by
      have := congrArg Fin.val (Z₁.inj heq)
      simpa using this
    omega
  have hne₂ : Z₂.p 0 ≠ Z₂.p Z₂.last := by
    intro heq
    have hv : (0 : ℕ) = Z₂.D := by
      have := congrArg Fin.val (Z₂.inj heq)
      simpa using this
    omega
  refine ⟨?_, ?_⟩
  · have h2 : ({Z₁.p 0, Z₁.p Z₁.last} : Finset V).card = 2 := Finset.card_pair hne₁
    have hsub : ({Z₁.p 0, Z₁.p Z₁.last} : Finset V) ⊆ T₁.alive := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Z₁.mem 0
      · exact Z₁.mem Z₁.last
    have := Finset.card_le_card hsub
    omega
  · have h2 : ({Z₂.p 0, Z₂.p Z₂.last} : Finset V).card = 2 := Finset.card_pair hne₂
    have hsub : ({Z₂.p 0, Z₂.p Z₂.last} : Finset V) ⊆ T₂.alive := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Z₂.mem 0
      · exact Z₂.mem Z₂.last
    have := Finset.card_le_card hsub
    omega

/-- A common endgame gives one common folding step. -/
theorem exists_foldStepAt_common {T₁ T₂ : TreeState V} {s : V} (h : CommonEndgame T₁ T₂ s) :
    ∃ U : TreeState V, FoldStepAt s T₁ U ∧ FoldStepAt s T₂ U := by
  obtain ⟨Z₁, Z₂, -, -, h₁, h₂, heq⟩ := h
  exact ⟨Z₁.foldState, ⟨Z₁, h₁, rfl⟩, ⟨Z₂, h₂, heq⟩⟩

/-- A folding sequence of length `n` followed by one of length `k` is a folding sequence of length
`n + k`. -/
theorem FoldSeqAt.trans {s : V} {S S' S'' : TreeState V} {n k : ℕ} (h₁ : FoldSeqAt s S S' n)
    (h₂ : FoldSeqAt s S' S'' k) : FoldSeqAt s S S'' (n + k) := by
  induction h₁ generalizing S'' k with
  | refl _ => simpa using h₂
  | step hpos hstep hrest ih =>
      rw [Nat.add_right_comm]
      exact FoldSeqAt.step hpos hstep (ih h₂)

/-- Folding towards a diameter endpoint keeps the endpoint a diameter endpoint (Lemma 3, iterated
along a whole folding sequence). -/
theorem FoldSeqAt.isDiamEnd {s : V} {S S' : TreeState V} {n : ℕ} (h : FoldSeqAt s S S' n)
    (hs : IsDiamEnd S s) : IsDiamEnd S' s := by
  induction h with
  | refl _ => exact hs
  | step _ hstep _ ih =>
      obtain ⟨P, hP, rfl⟩ := hstep
      exact ih (by rw [← hP]; exact isDiamEnd_foldState P)

/-- A state whose diameter is at least two has at least two vertices. -/
theorem two_le_card_of_two_le_diam (T : TreeState V) (h : 2 ≤ T.diam) : 2 ≤ T.alive.card := by
  have hne : T.alive.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : T.diam = 0 := by simp [TreeState.diam, hemp]
    omega
  by_contra hc
  have hc1 : T.alive.card ≤ 1 := by omega
  have hall : ∀ u ∈ T.alive, ∀ v ∈ T.alive, u = v := by
    intro u hu v hv
    by_contra hne'
    have h2 : ({u, v} : Finset V).card = 2 := Finset.card_pair hne'
    have hsub : ({u, v} : Finset V) ⊆ T.alive := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
    have := Finset.card_le_card hsub
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := T.exists_dist_eq_diam hne
  rw [hall u hu v hv, SimpleGraph.dist_self] at huv
  omega

/-- The fixed-endpoint process always terminates (local copy of
`LValue_exists_of_isDiamEnd` of `Exchange.lean`, which this file does not import). -/
theorem LValue_exists_aux : ∀ (N : ℕ) (S : TreeState V) (s : V),
    S.alive.card ≤ N → IsDiamEnd S s → ∃ n : ℕ, LValue S s n := by
  intro N
  induction N with
  | zero =>
      intro S s hcard hs
      exact absurd (Finset.card_pos.mpr ⟨s, hs.1⟩) (by omega)
  | succ N ih =>
      intro S s hcard hs
      by_cases hsingle : S.alive.card ≤ 1
      · exact ⟨0, S, FoldSeqAt.refl S, hsingle⟩
      · have hpos : 2 ≤ S.alive.card := by omega
        obtain ⟨P, hP⟩ := exists_diamPath_at S hs
        have hlt : P.foldState.alive.card ≤ N := by
          have := FoldStep.card_lt (S := S) (S' := P.foldState) ⟨P, rfl⟩ hpos
          omega
        have hEnd : IsDiamEnd P.foldState s := by
          rw [← hP]; exact isDiamEnd_foldState P
        obtain ⟨n', S'', hseq, hsingle'⟩ := ih P.foldState s hlt hEnd
        exact ⟨n' + 1, S'', FoldSeqAt.step hpos ⟨P, hP, rfl⟩ hseq, hsingle'⟩

/-- **Assembly (obligation (d)).**  If the synchronised phase brings `P.foldState` and
`Q.foldState` to two states after the same number `m` of folds towards `s`, and those two states
admit one further *common* fold towards `s`, then `exchange` holds: the remaining process is
carried out from the common state.

The hypothesis `CommonEndgame T₁ T₂ s` is what the endgame of §3 provides for `m = 0` (see
`endgame`, `endgame_of_diam`, and the corollary `exchange_of_diam_eq`) and what the synchronised
phase must supply for `m > 0`. -/
theorem exchange_of_commonEndgame {S : TreeState V} {s : V} (P Q : DiamPath S)
    (hP : P.p 0 = s) {m : ℕ} {T₁ T₂ : TreeState V}
    (h₁ : FoldSeqAt s P.foldState T₁ m) (h₂ : FoldSeqAt s Q.foldState T₂ m)
    (hend : CommonEndgame T₁ T₂ s) :
    ∃ n : ℕ, LValue P.foldState s n ∧ LValue Q.foldState s n := by
  obtain ⟨hc₁, hc₂⟩ := hend.card_le
  obtain ⟨U, hstep₁, hstep₂⟩ := exists_foldStepAt_common hend
  have hEndP : IsDiamEnd P.foldState s := by rw [← hP]; exact isDiamEnd_foldState P
  have hEndT₁ : IsDiamEnd T₁ s := FoldSeqAt.isDiamEnd h₁ hEndP
  have hEndU : IsDiamEnd U s := by
    obtain ⟨Z, hZ, rfl⟩ := hstep₁
    rw [← hZ]; exact isDiamEnd_foldState Z
  obtain ⟨k, S'', hseq, hsingle⟩ := LValue_exists_aux U.alive.card U s le_rfl hEndU
  exact ⟨m + (k + 1), ⟨S'', FoldSeqAt.trans h₁ (FoldSeqAt.step hc₁ hstep₁ hseq), hsingle⟩,
    ⟨S'', FoldSeqAt.trans h₂ (FoldSeqAt.step hc₂ hstep₂ hseq), hsingle⟩⟩

/-- **The endgame, packaged (obligation (c)).**  Under the hypotheses of the delayed exchange
lemma's endgame, the two folded states admit one further common fold towards `s`. -/
theorem endgame (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    (hr₂ : 1 ≤ Q.D - Q.meetIdx P) (hdiam₂ : Q.foldState.diam = 2 * (Q.D - Q.meetIdx P))
    (hmeet : Q.meetIdx P = P.meetIdx Q) (hD : Q.D = P.D) :
    CommonEndgame P.foldState Q.foldState s :=
  ⟨P.legPath Q hP hQ hr hdiam, Q.legPath P hQ hP hr₂ hdiam₂,
    by show 1 ≤ 2 * (P.D - P.meetIdx Q); omega,
    by show 1 ≤ 2 * (Q.D - Q.meetIdx P); omega,
    P.legPath_p_zero Q hP hQ hr hdiam, Q.legPath_p_zero P hQ hP hr₂ hdiam₂,
    P.legPath_foldState_eq Q hP hQ hr hdiam hr₂ hdiam₂ hmeet hD⟩

/-- Same as `endgame`, with both diameter hypotheses written in terms of the common tail length
`r = P.D - P.meetIdx Q`; the two facts `meetIdx`-symmetry and `D`-symmetry are those proved for a
pair of diameters of the *same* endpoint `s`. -/
theorem endgame_of_diam (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    (hdiam₂ : Q.foldState.diam = 2 * (P.D - P.meetIdx Q))
    (hmeet : P.meetIdx Q = Q.meetIdx P) (hD : P.D = Q.D) :
    CommonEndgame P.foldState Q.foldState s :=
  endgame P Q hP hQ hr hdiam (by omega) (by omega) hmeet.symm hD.symm

/-- **`exchange` in the case `H = 2 r`** (the synchronised phase is empty).  Both folded states
then fold directly onto the same state, and the fixed-endpoint process finishes at the same time
from both sides.  This is the `m = 0` instance of the assembly; the remaining case requires the
`synchronised phase` of the proof sketch. -/
theorem exchange_of_diam_eq {S : TreeState V} {s : V} (P Q : DiamPath S) (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) (hr : 1 ≤ P.D - P.meetIdx Q)
    (hdiam : P.foldState.diam = 2 * (P.D - P.meetIdx Q))
    (hdiam₂ : Q.foldState.diam = 2 * (P.D - P.meetIdx Q)) :
    ∃ n : ℕ, LValue P.foldState s n ∧ LValue Q.foldState s n :=
  exchange_of_commonEndgame P Q hP (m := 0) (FoldSeqAt.refl P.foldState)
    (FoldSeqAt.refl Q.foldState)
    (endgame_of_diam P Q hP hQ hr hdiam hdiam₂ (P.meetIdx_comm Q (hP.trans hQ.symm)) (P.D_eq Q))

/-! ## 5. What remains for the unconditional `exchange`

Everything below the synchronised phase is now proved: `exchange_of_commonEndgame` reduces
`exchange` to the single statement

```
theorem exists_commonEndgame (P Q : DiamPath S) {s : V} (hs : IsDiamEnd S s)
    (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    ∃ m T₁ T₂, FoldSeqAt s P.foldState T₁ m ∧ FoldSeqAt s Q.foldState T₂ m ∧
      CommonEndgame T₁ T₂ s
```

(the same shape that `OhtoaiTreeProof/Phase1.lean` documents at the end of its file).  The lockstep
induction that produces it has three inputs:

* `P.foldState.diam = Q.foldState.diam` — the two folded states have the same diameter.  Both
  bounds `2 * (P.D - P.meetIdx Q) ≤ P.foldState.diam` and `≤ Q.foldState.diam` are proved here
  (`two_mul_tail_le_diam`, `two_mul_tail_le_diam'`); the reverse inequality is the open point.
* while `T₁.diam > 2 * r`, the prescribed folds act inside the common part `C`, so they can be
  performed simultaneously by one `DiamPath` of `T₁` that is also a `DiamPath` of `T₂`
  (`Phase1.mem_foldAlive_iff_of_not_mem_Delta`, `Phase1.foldGraph_adj_iff_of_not_mem_Delta`);
* the endgame: when `T₁.diam = T₂.diam = 2 * r`, the legs of the two states coincide
  (`legPath_foldState_eq` above, together with `endgame_of_diam`), which is exactly
  `CommonEndgame T₁ T₂ s`.

Given `exists_commonEndgame`, the target theorem is

```
theorem exchange {S : TreeState V} {s : V} (hs : IsDiamEnd S s) (P Q : DiamPath S)
    (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    ∃ n : ℕ, LValue P.foldState s n ∧ LValue Q.foldState s n :=
  let ⟨m, T₁, T₂, h₁, h₂, hend⟩ := exists_commonEndgame P Q hs hP hQ
  exchange_of_commonEndgame P Q hP h₁ h₂ hend
```

(no `sorry`, no extra axiom is used anywhere in this file). -/

end OhtoaiTreeProof
