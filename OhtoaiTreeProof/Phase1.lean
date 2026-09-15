/-
# REF.md §7, phase 1: the common part `C` and the `Δ`-bounds

`REF.md` Lemma 5 (the *delayed exchange lemma*) says that for a diameter endpoint `s` of a state `S`
and two diameters `P`, `Q` of `S` starting at `s`, the two folded trees `P.foldState` and
`Q.foldState` admit complete folding processes towards `s` of the same length.  The proof runs in two
phases: while the diameter `H` of the (suitably equal) two states is larger than `2r` — where
`r = D - ℓ`, `D` the common diameter length and `ℓ = P.meetIdx Q` the last common index — both states
are folded *along the same path*, and once `H = 2r` the two surviving tails are laid onto the common
prefix.

This file supplies the part of `REF.md` §7 on which the synchronised phase rests: the description of
the region where the two folded states *differ*, and the fact that this region is small.

* `P.tailSet Q` is the union of the two tails `p_{ℓ+1},…,p_D`, `q_{ℓ+1},…,q_D` of the two diameters.
* `P.Delta Q s` is the *difference region*: the two tails together with everything hanging below
  them, i.e. every vertex `v` whose path to `s` passes through a vertex of a tail.  `C = Δᶜ` is the
  common part.  (§1, §2)
* The two folding maps agree off the tails (`rep_eq_of_not_mem_tailSet`), which gives the two
  agreement statements on `C`: membership in the folded vertex set, and adjacency of the folded
  graphs.  (§3, §4)
* Every vertex of `Δ` that survives in `P.foldState` is at distance at most `2r` from `s` in
  `P.foldState` (and symmetrically for `Q`).  (§5)

The last section records, as a comment, the exact statement of the remaining obligation (the
*lockstep invariant* of `REF.md` §7, obligation (b) of the comment block of `ExchangeLemma5.lean`)
in the form in which the assembly of the delayed exchange lemma will need it.
-/
import OhtoaiTreeProof.ExchangeLemma5
import OhtoaiTreeProof.Cone
import OhtoaiTreeProof.Iso
import OhtoaiTreeProof.Progress

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DiamPath

variable {S : TreeState V}

/-! ## 1. The two tails of two diameters starting at the same vertex

Write `D = P.D`, `ℓ = P.meetIdx Q` (the last common index) and `r = D - ℓ`.  The two diameters have
the common prefix `p 0, …, p ℓ` and then split into the *tails* `p_{ℓ+1},…,p_D` and
`q_{ℓ+1},…,q_D`.  Folding `P` fixes the `Q`-tail (which survives in `P.foldState`) and reflects the
`P`-tail onto the prefix; folding `Q` does the mirror image.  The tails are therefore exactly the
region on which the two folds differ. -/

/-- The union of the two tails `p_{ℓ+1},…,p_D` and `q_{ℓ+1},…,q_D` of the two diameters `P` and `Q`
(where `ℓ = P.meetIdx Q` is their last common index). -/
def tailSet (P Q : DiamPath S) : Set V :=
  {v | (∃ i, P.meetIdx Q < i ∧ i ≤ P.D ∧ v = P.seq i) ∨
       (∃ j, P.meetIdx Q < j ∧ j ≤ P.D ∧ v = Q.seq j)}

theorem mem_tailSet {P Q : DiamPath S} {v : V} :
    v ∈ P.tailSet Q ↔ (∃ i, P.meetIdx Q < i ∧ i ≤ P.D ∧ v = P.seq i) ∨
       (∃ j, P.meetIdx Q < j ∧ j ≤ P.D ∧ v = Q.seq j) := Iff.rfl

/-- The `P`-tail, in terms of the `P`-path. -/
theorem seq_mem_tailSet_iff (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {i : ℕ} (hi : i ≤ P.D) : P.seq i ∈ P.tailSet Q ↔ P.meetIdx Q < i := by
  constructor
  · rintro (⟨i', hi', hi'D, hii⟩ | ⟨j, hj, hjD, hij⟩)
    · rw [P.seq_inj i hi i' hi'D hii]; exact hi'
    · have hjQ : j ≤ Q.D := by have := P.D_eq Q; omega
      have h1 : S.graph.dist s (P.seq i) = i := P.dist_seq_zero hP hi
      have h2 : S.graph.dist s (Q.seq j) = j := Q.dist_seq_zero hQ hjQ
      rw [hij] at h1
      omega
  · intro h
    exact Or.inl ⟨i, h, hi, rfl⟩

/-- The `Q`-tail, in terms of the `Q`-path. -/
theorem seq_mem_tailSet_iff_Q (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {j : ℕ} (hj : j ≤ P.D) : Q.seq j ∈ P.tailSet Q ↔ P.meetIdx Q < j := by
  have hjQ : j ≤ Q.D := by have := P.D_eq Q; omega
  constructor
  · rintro (⟨i, hi, hiD, hji⟩ | ⟨j', hj', hj'D, hjj⟩)
    · have h1 : S.graph.dist s (P.seq i) = i := P.dist_seq_zero hP hiD
      have h2 : S.graph.dist s (Q.seq j) = j := Q.dist_seq_zero hQ hjQ
      rw [← hji] at h1
      omega
    · rw [Q.seq_inj j hjQ j' (by have := P.D_eq Q; omega) hjj]; exact hj'
  · intro h
    exact Or.inr ⟨j, h, hj, rfl⟩

/-- A vertex of the `Q`-tail is not on the `P`-diameter. -/
theorem seq_notMem_pathSet (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {j : ℕ} (hj : P.meetIdx Q < j) (hjD : j ≤ P.D) : Q.seq j ∉ P.pathSet := by
  intro hmem
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  have hiD : (i : ℕ) ≤ P.D := by have := i.isLt; omega
  have hji : j = (i : ℕ) := by
    have h1 : S.graph.dist s (P.p i) = (i : ℕ) := by
      rw [← P.seq_val i]; exact P.dist_seq_zero hP hiD
    have h2 : S.graph.dist s (Q.seq j) = j := Q.dist_seq_zero hQ (by have := P.D_eq Q; omega)
    rw [hi] at h1
    omega
  have hmeet : P.seq j = Q.seq j := by
    have h1 : P.seq j = P.p i := by rw [hji, P.seq_val i]
    rw [h1, hi]
  exact absurd (P.meetIdx_max Q hjD hmeet) (by omega)

/-- The tail set is symmetric in the two diameters. -/
theorem tailSet_comm (P Q : DiamPath S) (h0 : P.p 0 = Q.p 0) : P.tailSet Q = Q.tailSet P := by
  have hc := P.meetIdx_comm Q h0
  have hD := P.D_eq Q
  ext v
  constructor
  · rintro (⟨i, hi, hiD, rfl⟩ | ⟨j, hj, hjD, rfl⟩)
    · exact Or.inr ⟨i, by omega, by omega, rfl⟩
    · exact Or.inl ⟨j, by omega, by omega, rfl⟩
  · rintro (⟨i, hi, hiD, rfl⟩ | ⟨j, hj, hjD, rfl⟩)
    · exact Or.inr ⟨i, by omega, by omega, rfl⟩
    · exact Or.inl ⟨j, by omega, by omega, rfl⟩

/-- **The two folding maps agree off the two tails.**  On the common prefix `p 0, …, p ℓ` both act by
the same mirror map, and off both diameters they are the identity. -/
theorem rep_eq_of_not_mem_tailSet (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {x : V} (hx : x ∉ P.tailSet Q) : P.rep x = Q.rep x := by
  have h0 : P.p 0 = Q.p 0 := hP.trans hQ.symm
  have hDi : P.D = Q.D := P.D_eq Q
  have hc : P.meetIdx Q = Q.meetIdx P := P.meetIdx_comm Q h0
  rcases h : P.index x with _ | i
  · rw [P.rep_of_index_none h]
    have hnone : ∀ i, P.p i ≠ x := by
      intro i hi
      have hsome : P.index x = some i := P.index_eq_some hi
      rw [hsome] at h
      exact absurd h (by simp)
    rcases h' : Q.index x with _ | j
    · rw [Q.rep_of_index_none h']
    · exfalso
      have hjD : (j : ℕ) ≤ P.D := by have := j.isLt; omega
      have hxj : Q.seq (j : ℕ) = x := by rw [Q.seq_val j]; exact Q.eq_of_index_eq_some h'
      have hjle : (j : ℕ) ≤ P.meetIdx Q := by
        by_contra hcon
        have hlt : Q.meetIdx P < (j : ℕ) := by rw [← hc]; exact Nat.lt_of_not_le hcon
        have hjQ : (j : ℕ) ≤ Q.D := by omega
        refine hx ?_
        rw [← hxj, tailSet_comm P Q h0]
        exact (Q.seq_mem_tailSet_iff P hQ hP hjQ).mpr hlt
      have hPj : P.seq (j : ℕ) = Q.seq (j : ℕ) := P.seq_eq_of_le_meetIdx Q hP hQ hjle
      exact hnone ⟨(j : ℕ), by omega⟩ (by rw [← P.seq_eq hjD, hPj, hxj])
  · have hxs : x = P.seq (i : ℕ) := by rw [P.seq_val i]; exact (P.eq_of_index_eq_some h).symm
    have hiD : (i : ℕ) ≤ P.D := by have := i.isLt; omega
    have hiℓ : (i : ℕ) ≤ P.meetIdx Q := by
      by_contra hcon
      exact hx (by rw [hxs]; exact (P.seq_mem_tailSet_iff Q hP hQ hiD).mpr (Nat.lt_of_not_le hcon))
    have hiQ : (i : ℕ) ≤ Q.D := by omega
    have hix : P.seq (i : ℕ) = Q.seq (i : ℕ) := P.seq_eq_of_le_meetIdx Q hP hQ hiℓ
    rw [hxs, P.rep_seq hiD, hix, Q.rep_seq hiQ]
    have hmin : min (i : ℕ) (P.D - (i : ℕ)) = min (i : ℕ) (Q.D - (i : ℕ)) := by omega
    rw [hmin]
    exact P.seq_eq_of_le_meetIdx Q hP hQ (by omega)


/-! ## 2. The difference region `Δ` and the common part `C`

Folding along `P` reflects the far half of the diameter onto the near half
(`P.rep (P.seq k) = P.seq (min k (D - k))` for `k ≤ D`), carrying the subtrees that hang below the
far half along with it.  On the *common prefix* `s = p 0, …, p ℓ = q 0, …, q ℓ` the two folds act in
exactly the same way (both reflect it by `k ↦ min k (D - k)`, using `P.D = Q.D`), so the two folds
can differ only on the two tails beyond `ℓ` and below them.  The *difference region* `Δ` is
therefore the set of vertices that hang below one of the two tails, i.e. the vertices `v` whose path
to `s` passes through a vertex of one of the tails; on its complement `C` the two folds agree (§3,
§4).  The region is small in the folded states: every surviving vertex of `Δ` is within distance
`2r` of `s` in either folded state (§5), where `r = D - ℓ`. -/

/-- **The difference region `Δ`** of the two folds: a vertex belongs to `Δ` when its path to `s`
passes through a vertex of one of the two tails.  Equivalently, `Δ` is the union of the two tails and
of the subtrees hanging below them. -/
def Delta (P Q : DiamPath S) (s : V) : Set V :=
  {v | ∃ t ∈ P.tailSet Q, S.graph.dist s v = S.graph.dist s t + S.graph.dist t v}

/-- **The common part `C`** of the two folds: the complement of the difference region. -/
def Common (P Q : DiamPath S) (s : V) : Set V := (P.Delta Q s)ᶜ

theorem mem_Common {P Q : DiamPath S} {s v : V} : v ∈ P.Common Q s ↔ v ∉ P.Delta Q s := Iff.rfl

/-- Every vertex of a tail belongs to `Δ`. -/
theorem tailSet_subset_Delta (P Q : DiamPath S) (s : V) : P.tailSet Q ⊆ P.Delta Q s :=
  fun _ ht => ⟨_, ht, by rw [SimpleGraph.dist_self, add_zero]⟩

theorem notMem_tailSet_of_notMem_Delta (P Q : DiamPath S) {s v : V} (h : v ∉ P.Delta Q s) :
    v ∉ P.tailSet Q :=
  fun ht => h (P.tailSet_subset_Delta Q s ht)

/-- **The `P`-diameter meets `Δ` exactly in the `P`-tail.** -/
theorem seq_mem_Delta_iff (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {k : ℕ} (hk : k ≤ P.D) : P.seq k ∈ P.Delta Q s ↔ P.meetIdx Q < k := by
  constructor
  · rintro ⟨t, ht, hdist⟩
    have hdt : S.graph.dist s (P.seq k) = k := P.dist_seq_zero hP hk
    have htle : S.graph.dist s t ≤ k := by omega
    rcases ht with ⟨i, hi, hiD, rfl⟩ | ⟨j, hj, hjD, rfl⟩
    · have hti : S.graph.dist s (P.seq i) = i := P.dist_seq_zero hP hiD
      omega
    · have hjQ : j ≤ Q.D := by have := P.D_eq Q; omega
      have htj' : S.graph.dist s (Q.seq j) = j := Q.dist_seq_zero hQ hjQ
      omega
  · intro hk'
    exact ⟨P.seq k, (P.seq_mem_tailSet_iff Q hP hQ hk).mpr hk', by simp⟩

/-- **The `Q`-diameter meets `Δ` exactly in the `Q`-tail.** -/
theorem seq_mem_Delta_iff_Q (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {k : ℕ} (hk : k ≤ P.D) : Q.seq k ∈ P.Delta Q s ↔ P.meetIdx Q < k := by
  constructor
  · rintro ⟨t, ht, hdist⟩
    have hdt : S.graph.dist s (Q.seq k) = k := Q.dist_seq_zero hQ (by have := P.D_eq Q; omega)
    have htle : S.graph.dist s t ≤ k := by omega
    rcases ht with ⟨i, hi, hiD, rfl⟩ | ⟨j, hj, hjD, rfl⟩
    · have hti' : S.graph.dist s (P.seq i) = i := P.dist_seq_zero hP hiD
      omega
    · have htj : S.graph.dist s (Q.seq j) = j := Q.dist_seq_zero hQ (by have := P.D_eq Q; omega)
      omega
  · intro hk'
    exact ⟨Q.seq k, (P.seq_mem_tailSet_iff_Q Q hP hQ hk).mpr hk', by simp⟩

/-- The difference region is symmetric in the two diameters. -/
theorem Delta_comm (P Q : DiamPath S) (s : V) (h0 : P.p 0 = Q.p 0) :
    P.Delta Q s = Q.Delta P s := by
  unfold Delta
  rw [tailSet_comm P Q h0]

/-- **The spine `p 0, …, p r` lies in the common part.**  (`r = D - ℓ`; by `tail_le_meetIdx` the
spine is contained in the common prefix, so no tail vertex lies on the path from `s` to it.) -/
theorem spine_mem_Common (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {k : ℕ}
    (hk : k ≤ P.D - P.meetIdx Q) : P.seq k ∉ P.Delta Q s := by
  have htail := P.tail_le_meetIdx Q hP hQ
  have hlD := P.meetIdx_le Q
  rw [P.seq_mem_Delta_iff Q hP hQ (by omega)]
  omega

/-! ## 3. Agreement of the two folded vertex sets on the common part -/

/-! ### Vertices hanging below a tail

The lemmas of this subsection describe the vertices of `Δ`: a vertex hanging below a tail vertex is
in `Δ`, and its height above the diameter is bounded by Lemma 1. -/

/-- **Lemma 1 (`REF.md` §3) in `ℕ`-indexed form**: the distance from a live vertex `u` to the closest
vertex `P.seq i` of the diameter is at most `min i (D - i)`. -/
theorem dist_seq_le_min_index (P : DiamPath S) {u : V} (hu : u ∈ S.alive) {i : ℕ} (hi : i ≤ P.D)
    (hmin : ∀ j ≤ P.D, S.graph.dist u (P.seq i) ≤ S.graph.dist u (P.seq j)) :
    S.graph.dist u (P.seq i) ≤ min i (P.D - i) := by
  have hmin' : ∀ j : Fin (P.D + 1),
      S.graph.dist u (P.p ⟨i, by omega⟩) ≤ S.graph.dist u (P.p j) := by
    intro j
    have hj : (j : ℕ) ≤ P.D := by have := j.isLt; omega
    rw [← P.seq_val ⟨i, by omega⟩, ← P.seq_val j]
    exact hmin (j : ℕ) hj
  have h := dist_le_min_index P hu hmin'
  rw [← P.seq_val ⟨i, by omega⟩] at h
  simpa using h

/-- **A vertex of the diameter at the end of the `s`-path through it.**  If the path from `s` to the
live vertex `v` passes through `P.seq i`, then the height of `v` above `P.seq i` is at most `D - i`.
This is the form of Lemma 1 used for the `Δ`-bounds. -/
theorem dist_seq_le_sub_of_dist_eq (P : DiamPath S) {s : V} (hP : P.p 0 = s) {v : V}
    (hv : v ∈ S.alive) {i : ℕ} (hi : i ≤ P.D)
    (h : S.graph.dist s v = S.graph.dist s (P.seq i) + S.graph.dist (P.seq i) v) :
    S.graph.dist (P.seq i) v ≤ P.D - i := by
  obtain ⟨k, hkD, hkmin⟩ := P.exists_closest_index_seq v
  have hmain : S.graph.dist s v = i + S.graph.dist v (P.seq i) := by
    have hh := h
    rw [P.dist_seq_zero hP hi] at hh
    rw [hh, SimpleGraph.dist_comm]
  have hp0 : S.graph.dist s v = S.graph.dist v (P.seq k) + k := by
    have h0 := P.dist_seq_eq_add_of_ge (i := k) hv hkD hkmin (k := 0) (Nat.zero_le _)
    rw [P.seq_zero, hP, Nat.sub_zero] at h0
    rw [← h0, SimpleGraph.dist_comm]
  rcases le_total k i with hki | hik
  · have hproj := P.dist_seq_eq_add_of_le (i := k) hv hkmin (k := i) hki hi
    have hik' : i = k := by omega
    rw [hik']
    have hb := P.dist_seq_le_min_index (u := v) hv hkD hkmin
    rw [SimpleGraph.dist_comm]
    exact le_trans hb (min_le_right k (P.D - k))
  · have hproj := P.dist_seq_eq_add_of_ge (i := k) hv hkD hkmin (k := i) hik
    have hkey : min k (P.D - k) + k ≤ P.D := by
      rcases le_total k (P.D - k) with hle | hle
      · rw [min_eq_left hle]; omega
      · rw [min_eq_right hle]; omega
    have hb := P.dist_seq_le_min_index (u := v) hv hkD hkmin
    rw [SimpleGraph.dist_comm]
    omega

/-- A vertex off a diameter which is adjacent to a vertex of the diameter hangs from it: it is
further from `s` than that vertex by exactly one. -/
theorem dist_eq_of_adj_off_path (P : DiamPath S) {s : V} (hP : P.p 0 = s) {y : V}
    (hy : y ∉ P.pathSet) {i : ℕ} (hi : i ≤ P.D) (hadj : S.graph.Adj y (P.seq i)) :
    S.graph.dist s y = i + 1 := by
  have hyne : ∀ j, P.p j ≠ y := fun j hj =>
    hy (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
  have hu : y ∈ S.alive := (S.adj_alive hadj).1
  obtain ⟨k, hkD, hkmin⟩ := P.exists_closest_index_seq y
  have hd1 : S.graph.dist y (P.seq i) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have hki : k = i := by
    rcases le_total k i with hle | hle
    · have h1 := P.dist_seq_eq_add_of_le hu hkmin hle hi
      rw [hd1] at h1
      have hik : i - k = 0 := by
        by_contra hne
        have hge : 1 ≤ i - k := Nat.one_le_iff_ne_zero.mpr hne
        have hd0 : S.graph.dist y (P.seq k) = 0 := by omega
        have hyk : y = P.seq k := (S.dist_eq_zero_iff hu (P.seq_mem k)).mp hd0
        exact hyne ⟨k, by omega⟩ (by rw [← P.seq_val ⟨k, by omega⟩]; exact hyk.symm)
      omega
    · have h1 := P.dist_seq_eq_add_of_ge (i := k) hu hkD hkmin (k := i) hle
      rw [hd1] at h1
      have hki' : k - i = 0 := by
        by_contra hne
        have hge : 1 ≤ k - i := Nat.one_le_iff_ne_zero.mpr hne
        have hd0 : S.graph.dist y (P.seq k) = 0 := by omega
        have hyk : y = P.seq k := (S.dist_eq_zero_iff hu (P.seq_mem k)).mp hd0
        exact hyne ⟨k, by omega⟩ (by rw [← P.seq_val ⟨k, by omega⟩]; exact hyk.symm)
      omega
  have hval : S.graph.dist s y = S.graph.dist y (P.seq k) + k := by
    have h0 := P.dist_seq_eq_add_of_ge (i := k) hu hkD hkmin (k := 0) (Nat.zero_le _)
    rw [P.seq_zero, hP, Nat.sub_zero] at h0
    rw [← h0, SimpleGraph.dist_comm]
  have hd1k : S.graph.dist y (P.seq k) = 1 := by rw [hki]; exact hd1
  rw [hval, hd1k, ← hki]
  omega

/-- **A vertex hanging below a tail vertex belongs to `Δ`.** -/
theorem mem_Delta_of_adj_off_path (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {y : V} (hy : y ∉ P.pathSet) {i : ℕ} (hi : i ≤ P.D) (hmeet : P.meetIdx Q < i)
    (hadj : S.graph.Adj y (P.seq i)) : y ∈ P.Delta Q s := by
  have hd := P.dist_eq_of_adj_off_path hP hy hi hadj
  have h1 : S.graph.dist (P.seq i) y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm
  exact ⟨P.seq i, (P.seq_mem_tailSet_iff Q hP hQ hi).mpr hmeet, by
    rw [hd, P.dist_seq_zero hP hi, h1]⟩

/-- **The two folded states have the same vertices on the common part.** -/
theorem mem_foldAlive_iff_of_not_mem_Delta (P Q : DiamPath S) {s : V} (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) {u : V} (hu : u ∉ P.Delta Q s) :
    u ∈ P.foldAlive ↔ u ∈ Q.foldAlive := by
  have hrep := P.rep_eq_of_not_mem_tailSet Q hP hQ (P.notMem_tailSet_of_notMem_Delta Q hu)
  rw [P.mem_foldAlive, Q.mem_foldAlive, hrep]

/-! ## 4. Agreement of the two folded graphs on the common part

The proof of the converse direction is the only place where the description of `Δ` is used in
earnest: if an edge of `P.foldState` between two vertices of `C` is lifted to an edge `x y` of `S`,
then either both `x` and `y` lie off the tails — and then the lift works for `Q` as well, because
`P.rep` and `Q.rep` agree off the tails — or one of them lies in the `P`-tail (it cannot lie in the
`Q`-tail, since then the corresponding end would be in `Δ`), and then both ends `u`, `v` of the
folded edge are *neighbouring vertices of the spine*, which are adjacent in both folded states. -/

/-- Two vertices of a diameter whose index distance is one are adjacent (in either order). -/
theorem adj_seq_of_dist_eq_one (P : DiamPath S) {a b : ℕ} (ha : a ≤ P.D) (hb : b ≤ P.D)
    (h : (b - a) + (a - b) = 1) : S.graph.Adj (P.seq a) (P.seq b) := by
  rcases le_total a b with hle | hle
  · have hb' : b = a + 1 := by omega
    rw [hb']
    exact P.seq_adj a (by omega)
  · have ha' : a = b + 1 := by omega
    rw [ha']
    exact (P.seq_adj b (by omega)).symm

/-- An edge of `P.foldState` between two vertices of the common part has a lift whose two ends are
not in the two tails. -/
theorem exists_witnesses_adj_tail (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {u v x y : V} (hu : u ∉ P.Delta Q s) (hv : v ∉ P.Delta Q s)
    (hxy : S.graph.Adj x y) (hx : P.rep x = u) (hy : P.rep y = v) (hxt : x ∈ P.tailSet Q) :
    ∃ x' y', S.graph.Adj x' y' ∧ Q.rep x' = u ∧ Q.rep y' = v := by
  have htw := P.two_mul_tail_le Q hP hQ
  have hlD := P.meetIdx_le Q
  rcases hxt with ⟨i, hi, hiD, rfl⟩ | ⟨j, hj, hjD, hxj⟩
  · -- `x = p i` is the `i`-th vertex of the `P`-tail; then `u` is the spine vertex `p (D - i)`
    have hu' : u = P.seq (P.D - i) := by
      rw [← hx, show P.rep (P.seq i) = P.seq (P.D - i) by rw [P.rep_seq hiD]; congr 1; omega]
    by_cases hyP : y ∈ P.pathSet
    · -- `y` is on the `P`-diameter
      obtain ⟨m, -, hym⟩ := Finset.mem_image.mp hyP
      have hmD : (m : ℕ) ≤ P.D := by have := m.isLt; omega
      have hym' : y = P.seq (m : ℕ) := by rw [P.seq_val m]; exact hym.symm
      have hdist1 : S.graph.dist (P.seq i) (P.seq (m : ℕ)) = 1 := by
        rw [← hym']
        exact SimpleGraph.dist_eq_one_iff_adj.mpr hxy
      have habs : ((m : ℕ) - i) + (i - (m : ℕ)) = 1 := by
        rw [← P.dist_seq_seq (j := i) (i := m) hiD hmD]; exact hdist1
      by_cases hmℓ : P.meetIdx Q < (m : ℕ)
      · -- both `x` and `y` are in the `P`-tail: `u`, `v` are neighbouring spine vertices
        have hv' : v = P.seq (P.D - (m : ℕ)) := by
          rw [← hy, hym',
            show P.rep (P.seq (m : ℕ)) = P.seq (P.D - (m : ℕ)) by
              rw [P.rep_seq hmD]; congr 1; omega]
        rw [hu', hv']
        exact ⟨P.seq (P.D - i), P.seq (P.D - (m : ℕ)),
          P.adj_seq_of_dist_eq_one (by omega) (by omega) (by omega),
          P.rep_spine' Q hP hQ (by omega), P.rep_spine' Q hP hQ (by omega)⟩
      · -- `y = p ℓ` lies on the common prefix: `u`, `v` are `p (r-1)` and `p r`
        have hmval : (m : ℕ) = P.meetIdx Q := by omega
        have hv' : v = P.seq (P.D - P.meetIdx Q) := by
          rw [← hy, hym', hmval, P.rep_seq_meetIdx Q hP hQ]
        have hru : u = P.seq (P.D - P.meetIdx Q - 1) := by
          rw [hu', show P.D - i = P.D - P.meetIdx Q - 1 by omega]
        rw [hru, hv']
        exact ⟨P.seq (P.D - P.meetIdx Q - 1), P.seq (P.D - P.meetIdx Q),
          P.adj_seq_of_dist_eq_one (by omega) (by omega) (by omega),
          P.rep_spine' Q hP hQ (by omega), P.rep_spine' Q hP hQ (le_refl _)⟩
    · -- `y` hangs below `x = p i`, hence `v ∈ Δ`, contradicting `hv`
      exfalso
      have hy0 : P.rep y = y := P.rep_eq_self fun m hm =>
        hyP (Finset.mem_image.mpr ⟨m, Finset.mem_univ _, hm⟩)
      refine hv ?_
      rw [← hy, hy0]
      exact P.mem_Delta_of_adj_off_path Q hP hQ hyP hiD hi hxy.symm
  · -- `x` is in the `Q`-tail: then `u ∈ Δ`, contradicting `hu`
    exfalso
    refine hu ?_
    rw [← hx, hxj, P.rep_off_path Q hP hQ hj hjD]
    exact P.tailSet_subset_Delta Q s ((P.seq_mem_tailSet_iff_Q Q hP hQ hjD).mpr hj)

/-- An edge of `P.foldState` between two vertices of the common part can be lifted to an edge of `S`
whose two ends are not in the two tails; consequently it is also an edge of `Q.foldState`. -/
theorem exists_witnesses_adj (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {u v x y : V} (hu : u ∉ P.Delta Q s) (hv : v ∉ P.Delta Q s)
    (hxy : S.graph.Adj x y) (hx : P.rep x = u) (hy : P.rep y = v) :
    ∃ x' y', S.graph.Adj x' y' ∧ Q.rep x' = u ∧ Q.rep y' = v := by
  by_cases hxt : x ∈ P.tailSet Q
  · exact P.exists_witnesses_adj_tail Q hP hQ hu hv hxy hx hy hxt
  · by_cases hyt : y ∈ P.tailSet Q
    · obtain ⟨y', x', hyx', hy', hx'⟩ :=
        P.exists_witnesses_adj_tail Q hP hQ hv hu hxy.symm hy hx hyt
      exact ⟨x', y', hyx'.symm, hx', hy'⟩
    · exact ⟨x, y, hxy, (P.rep_eq_of_not_mem_tailSet Q hP hQ hxt).symm.trans hx,
        (P.rep_eq_of_not_mem_tailSet Q hP hQ hyt).symm.trans hy⟩

/-- **The two folded graphs agree on the common part.** -/
theorem foldGraph_adj_of_not_mem_Delta (P Q : DiamPath S) {s : V} (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) {u v : V} (hu : u ∉ P.Delta Q s) (hv : v ∉ P.Delta Q s)
    (h : P.foldGraph.Adj u v) : Q.foldGraph.Adj u v := by
  obtain ⟨hne, huA, hvA, x, y, hxy, hx, hy⟩ := P.foldGraph_adj.mp h
  have huQ : u ∈ Q.foldAlive := (P.mem_foldAlive_iff_of_not_mem_Delta Q hP hQ hu).mp huA
  have hvQ : v ∈ Q.foldAlive := (P.mem_foldAlive_iff_of_not_mem_Delta Q hP hQ hv).mp hvA
  obtain ⟨x', y', hxy', hx', hy'⟩ := P.exists_witnesses_adj Q hP hQ hu hv hxy hx hy
  exact ⟨hne, huQ, hvQ, x', y', hxy', hx', hy'⟩

/-- **The two folded graphs agree on the common part** (both directions). -/
theorem foldGraph_adj_iff_of_not_mem_Delta (P Q : DiamPath S) {s : V} (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) {u v : V} (hu : u ∉ P.Delta Q s) (hv : v ∉ P.Delta Q s) :
    P.foldGraph.Adj u v ↔ Q.foldGraph.Adj u v := by
  have h0 : P.p 0 = Q.p 0 := hP.trans hQ.symm
  have hDc := P.Delta_comm Q s h0
  have hu' : u ∉ Q.Delta P s := by rw [← hDc]; exact hu
  have hv' : v ∉ Q.Delta P s := by rw [← hDc]; exact hv
  exact ⟨fun h => P.foldGraph_adj_of_not_mem_Delta Q hP hQ hu hv h,
    fun h => Q.foldGraph_adj_of_not_mem_Delta P hQ hP hu' hv' h⟩

/-- **A path of `P.foldState` inside the common part is a walk of `Q.foldState`.**  This is the form
in which the synchronised phase uses the agreement of the two folded graphs: a common path can be
folded in either state. -/
theorem reachable_of_seq_common (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {n : ℕ} {q : ℕ → V} (hadj : ∀ k < n, P.foldGraph.Adj (q k) (q (k + 1)))
    (hq : ∀ k ≤ n, q k ∉ P.Delta Q s) : Q.foldGraph.Reachable (q 0) (q n) := by
  induction n with
  | zero => exact Reachable.rfl
  | succ n ih =>
      have h1 : Q.foldGraph.Reachable (q 0) (q n) :=
        ih (fun k hk => hadj k (by omega)) fun k hk => hq k (by omega)
      have h2 : Q.foldGraph.Adj (q n) (q (n + 1)) :=
        (P.foldGraph_adj_iff_of_not_mem_Delta Q hP hQ (hq n (by omega))
          (hq (n + 1) (by omega))).mp (hadj n (by omega))
      exact h1.trans h2.reachable

/-! ## 5. The `Δ`-bounds

A surviving vertex of the `Q`-tail is `q (ℓ+t)`, at distance `r + t ≤ 2r` from `s` in `P.foldState`
along the leg `p 0, …, p r, q (ℓ+1), …, q D`; a vertex hanging below it adds at most `D - (ℓ+t)`
more, by Lemma 1.  A vertex hanging below the `P`-tail is folded onto the spine first, at distance
`D - i` from `s`, and Lemma 1 bounds its height by `D - i` as well. -/

/-- The leg `p 0, …, p r, q (ℓ+1), …, q j` bounds the distance from `s` to `q j` in `P.foldState`. -/
theorem dist_seq_le_of_leg (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {j : ℕ} (hj : P.meetIdx Q < j) (hjD : j ≤ P.D) :
    P.foldGraph.dist (P.seq 0) (Q.seq j) ≤
      (P.D - P.meetIdx Q) + (j - P.meetIdx Q) := by
  have htw := P.two_mul_tail_le Q hP hQ
  have hr : 1 ≤ P.D - P.meetIdx Q := by omega
  have hn : (P.D - P.meetIdx Q) + (j - P.meetIdx Q) ≤ 2 * (P.D - P.meetIdx Q) := by omega
  obtain ⟨w, hw⟩ := exists_walk_of_seq (H := P.foldGraph) (q := P.legSeq Q)
    (n := (P.D - P.meetIdx Q) + (j - P.meetIdx Q))
    (fun k hk => P.legSeq_adj Q hP hQ hr (k := k) (by omega))
  have h0 : P.legSeq Q 0 = P.seq 0 := P.legSeq_zero Q
  have hlast : P.legSeq Q ((P.D - P.meetIdx Q) + (j - P.meetIdx Q)) = Q.seq j := by
    rw [P.legSeq_of_lt Q (by omega),
      show P.meetIdx Q + ((P.D - P.meetIdx Q) + (j - P.meetIdx Q) - (P.D - P.meetIdx Q)) = j
        by omega]
  calc P.foldGraph.dist (P.seq 0) (Q.seq j) ≤ (w.copy h0 hlast).length :=
        SimpleGraph.dist_le _
    _ = (P.D - P.meetIdx Q) + (j - P.meetIdx Q) := by
        rw [SimpleGraph.Walk.length_copy]; exact hw

/-- **The `Δ`-bound for `P.foldState`.**  Every vertex of the difference region that survives in
`P.foldState` is at distance at most `2r` from `s`, where `r = D - ℓ`. -/
theorem dist_le_two_mul_tail_of_mem_Delta (P Q : DiamPath S) {s : V} (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) {v : V} (hv : v ∈ P.Delta Q s) (hvA : v ∈ P.foldAlive) :
    P.foldGraph.dist (P.seq 0) v ≤ 2 * (P.D - P.meetIdx Q) := by
  obtain ⟨t, ht, hdist⟩ := hv
  obtain ⟨hvS, hvrep⟩ := P.mem_foldAlive.mp hvA
  have htw := P.two_mul_tail_le Q hP hQ
  rcases ht with ⟨i, hi, hiD, rfl⟩ | ⟨j, hj, hjD, rfl⟩
  · -- `t = p i` is in the `P`-tail: `P` folds it onto the spine vertex `p (D - i)`
    have hrep : P.rep (P.seq i) = P.seq (P.D - i) := by
      rw [P.rep_seq hiD]; congr 1; omega
    have htri : P.foldGraph.dist (P.seq 0) v ≤
        P.foldGraph.dist (P.seq 0) (P.rep (P.seq i)) + P.foldGraph.dist (P.rep (P.seq i)) v :=
      (P.foldState.connected (P.seq 0) (P.foldCone_seq_mem (Nat.zero_le _)) _
        (P.rep_mem_foldAlive (P.seq_mem i))).dist_triangle_left v
    have h1 : P.foldGraph.dist (P.seq 0) (P.rep (P.seq i)) ≤ P.D - i := by
      rw [hrep]
      have h := Cone.path_dist_le (H := P.foldGraph) (m := P.D / 2) (q := P.seq)
        P.foldGraph_isAcyclic P.foldCone_seq_adj P.foldCone_seq_inj
        (i := 0) (j := P.D - i) (Nat.zero_le _) (by omega)
      omega
    have h2 : P.foldGraph.dist (P.rep (P.seq i)) v ≤ S.graph.dist (P.seq i) v := by
      have h := P.foldCone_dist_le (P.seq i) v
      rwa [hvrep] at h
    have h3 : S.graph.dist (P.seq i) v ≤ P.D - i := P.dist_seq_le_sub_of_dist_eq hP hvS hiD hdist
    omega
  · -- `t = q j` is in the `Q`-tail and survives
    have hrept : P.rep (Q.seq j) = Q.seq j := P.rep_off_path Q hP hQ hj hjD
    have htri : P.foldGraph.dist (P.seq 0) v ≤
        P.foldGraph.dist (P.seq 0) (Q.seq j) + P.foldGraph.dist (Q.seq j) v :=
      (P.foldState.connected (P.seq 0) (P.foldCone_seq_mem (Nat.zero_le _)) _
        (P.mem_foldAlive_off_path Q hP hQ hj hjD)).dist_triangle_left v
    have h1 := P.dist_seq_le_of_leg Q hP hQ hj hjD
    have h2 : P.foldGraph.dist (Q.seq j) v ≤ S.graph.dist (Q.seq j) v := by
      have h := P.foldCone_dist_le (Q.seq j) v
      rwa [hrept, hvrep] at h
    have h3 : S.graph.dist (Q.seq j) v ≤ Q.D - j :=
      Q.dist_seq_le_sub_of_dist_eq (i := j) hQ hvS (by have := P.D_eq Q; omega) hdist
    have hDℓ : P.meetIdx Q + (P.D - P.meetIdx Q) = P.D := P.meetIdx_add_tail Q
    have hDi : P.D = Q.D := P.D_eq Q
    omega

/-- **The `Δ`-bound for `Q.foldState`.** -/
theorem dist_le_two_mul_tail_of_mem_Delta' (P Q : DiamPath S) {s : V} (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) {v : V} (hv : v ∈ P.Delta Q s) (hvA : v ∈ Q.foldAlive) :
    Q.foldGraph.dist (Q.seq 0) v ≤ 2 * (P.D - P.meetIdx Q) := by
  have h0 : P.p 0 = Q.p 0 := hP.trans hQ.symm
  have hv' : v ∈ Q.Delta P s := by rw [← P.Delta_comm Q s h0]; exact hv
  have h := Q.dist_le_two_mul_tail_of_mem_Delta P hQ hP hv' hvA
  have hcomm := P.meetIdx_comm Q h0
  have hDi := P.D_eq Q
  rwa [show Q.D - Q.meetIdx P = P.D - P.meetIdx Q by omega] at h

/-- **The far end of a long diameter is in the common part.**  If a vertex of `P.foldState` is
further than `2r` from `s`, it cannot belong to the difference region: this is the form in which the
synchronised phase uses the `Δ`-bound. -/
theorem notMem_Delta_of_lt_dist (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {v : V} (hvA : v ∈ P.foldAlive)
    (h : 2 * (P.D - P.meetIdx Q) < P.foldGraph.dist (P.seq 0) v) : v ∉ P.Delta Q s :=
  fun hv => absurd (P.dist_le_two_mul_tail_of_mem_Delta Q hP hQ hv hvA) (by omega)

/-- The same on the `Q` side. -/
theorem notMem_Delta_of_lt_dist' (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {v : V} (hvA : v ∈ Q.foldAlive)
    (h : 2 * (P.D - P.meetIdx Q) < Q.foldGraph.dist (Q.seq 0) v) : v ∉ P.Delta Q s :=
  fun hv => absurd (P.dist_le_two_mul_tail_of_mem_Delta' Q hP hQ hv hvA) (by omega)

/-! ## 6. What remains: the synchronised phase (obligation (b) of `ExchangeLemma5.lean` §4)

Sections 2–5 supply everything about `Δ` and its complement that the synchronised phase needs, but
the phase itself is *not* proved in this file.  Its exact Lean statement, in the form required by
the assembly `ExchangeProof.exchange_of_commonEndgame`, is

```
theorem exists_commonEndgame_of_deltaBounds (P Q : DiamPath S) {s : V} (hs : IsDiamEnd S s)
    (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    ∃ m T₁ T₂, FoldSeqAt s P.foldState T₁ m ∧ FoldSeqAt s Q.foldState T₂ m ∧
      CommonEndgame T₁ T₂ s
```

where (`ExchangeProof.lean` §4)

```
def CommonEndgame (T₁ T₂ : TreeState V) (s : V) : Prop :=
  ∃ (Z₁ : DiamPath T₁) (Z₂ : DiamPath T₂), 1 ≤ Z₁.D ∧ Z₁.p 0 = s ∧ Z₂.p 0 = s ∧
    Z₁.foldState = Z₂.foldState
```

The intended proof is the synchronised (lockstep) induction on the diameter, with `r = D - ℓ`,
`ℓ = P.meetIdx Q`:

* *One step.*  While `T₁.diam > 2 * r`, all the folds prescribed by the phase act on vertices in
  the common part: a vertex that is folded keeps its distance to `s` or is identified with a vertex
  at distance `1` or `2` less, so a vertex at distance `> 2 * r` from `s` never lies in `Δ`
  (`notMem_Delta_of_lt_dist`, `notMem_Delta_of_lt_dist'`).  One therefore folds both states along
  the *same* common diameter path `Z` (a `DiamPath P.foldState` whose vertices avoid `P.Delta Q s`),
  which is legitimate because on `C` the two states have the same vertices
  (`mem_foldAlive_iff_of_not_mem_Delta`) and the same edges
  (`foldGraph_adj_iff_of_not_mem_Delta`); an explicit common path is transported by
  `reachable_of_seq_common`.
* *Termination.*  Each such fold lowers the diameter of both states by `2`, until
  `T₁.diam = T₂.diam = 2 * r`; both states are then folded by their legs, which coincide by
  `ExchangeProof.legPath_foldState_eq`, so `CommonEndgame T₁ T₂ s` holds.

The missing input for the termination argument, which is *not* established here, is that the two
folded states have the *same* diameter to begin with: `P.foldState.diam = Q.foldState.diam` — the
`Δ`-bounds show that `dist` in either state is at most `2 * r` on the difference region, but an
equality of the two diameters (equivalently: a far vertex of the common part is equally far in
both states) still has to be proved. -/

end DiamPath

end OhtoaiTreeProof
