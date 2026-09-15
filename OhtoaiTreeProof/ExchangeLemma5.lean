/-
# REF.md Lemma 5 (§7): the delayed exchange lemma

This file proves the last missing structural ingredient of the proof of `REF.md`, the *delayed
exchange lemma* (`REF.md` Lemma 5, §7):

> Let `s` be a diameter endpoint of a state `S`, and let `P`, `Q` be two diameters of `S` starting
> at `s`.  Then the two folded trees `P.foldState` and `Q.foldState` admit complete folding
> processes towards `s` of the *same* length.

The proof follows `REF.md` §6–§7 and runs in three steps.

* **Setup.**  Write `D = P.D = Q.D` for the common diameter length, `ℓ` for the *last common
  index* of the two paths, `r = D - ℓ`, and `w = P.seq ℓ = Q.seq ℓ` for the vertex where the two
  diameters split.  `REF.md` Lemma 4 (§6) says `2r ≤ D`, i.e. `r ≤ ⌊D/2⌋ ≤ ℓ`: the two diameters
  can only split in the second half.  Everything the two folds do to the common prefix `p 0, …,
  p ℓ` is the same (`rep` acts by the mirror map `i ↦ min i (D - i)`, the same on both sides), and
  the `t`-th vertex of either tail is identified with the *same* prefix vertex `p (r - t)`.

* **Phase 1 (synchronised folds).**  In `P.foldState` the whole `Q`-tail survives as a path of
  length `r` hanging at `p r`, while the `P`-tail has been folded back onto the prefix; in
  `Q.foldState` the roles are exchanged.  All differences between the two states therefore live
  inside the ball of radius `2r` around `s`: outside it the two states are literally equal.
  As long as the diameter `H` of the two (equal) states is `> 2r`, we fold *both* of them along the
  *same* vertex path — a longest path from `s`, which lies in the common part — and the fold map is
  the identity on the difference region, so the situation is preserved while the state shrinks.

* **Phase 2 (endgame).**  When `H = 2r`, `s`–`Q.last` is a diameter of `P.foldState` and `s`–`P.last`
  is a diameter of `Q.foldState`.  Folding each along it lays the surviving tail onto the prefix and
  moves the subtrees hanging off the two tails to the *same* places `p (r - t)`; the two results are
  therefore the same state.

The lemmas are organised so that each step is a standalone statement: §1 fixes the combinatorics of
the two paths, §2 the identification of the tails with the prefix, §3 the structure of the two
folded states, §4 the endgame, §5 the synchronised phase and the final assembly.
-/
import OhtoaiTreeProof.Cone
import OhtoaiTreeProof.Iso
import OhtoaiTreeProof.Progress

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The common prefix of two diameters starting at the same vertex -/

namespace DiamPath

variable {S : TreeState V}

/-- The `0`-th vertex of a diameter. -/
theorem seq_zero (P : DiamPath S) : P.seq 0 = P.p 0 :=
  P.seq_eq (Nat.zero_le _)

/-- Every vertex of a diameter is live. -/
theorem seq_mem (P : DiamPath S) (k : ℕ) : P.seq k ∈ S.alive :=
  P.mem _

/-- Distance from the first vertex of a diameter to its `k`-th vertex. -/
theorem dist_seq_zero (P : DiamPath S) {s : V} (h0 : P.p 0 = s) {k : ℕ} (hk : k ≤ P.D) :
    S.graph.dist s (P.seq k) = k := by
  rw [← h0, P.seq_eq hk]
  simpa using P.dist_path (0 : Fin (P.D + 1)) ⟨k, by omega⟩

/-- Distance between two vertices of a diameter, in terms of the indices. -/
theorem dist_seq_seq (P : DiamPath S) {j i : ℕ} (hj : j ≤ P.D) (hi : i ≤ P.D) :
    S.graph.dist (P.seq j) (P.seq i) = (i - j) + (j - i) := by
  rw [P.seq_eq hj, P.seq_eq hi]
  exact P.dist_path ⟨j, by omega⟩ ⟨i, by omega⟩

/-- **Projection formula, `ℕ`-indexed form.**  If `P.seq i` is a closest vertex of the diameter to
the live vertex `u`, then the distance from `u` to `P.seq k` grows linearly with `|k - i|`. -/
theorem dist_seq_eq_add_of_le (P : DiamPath S) {u : V} (hu : u ∈ S.alive) {i : ℕ}
    (hmin : ∀ j ≤ P.D, S.graph.dist u (P.seq i) ≤ S.graph.dist u (P.seq j))
    {k : ℕ} (hik : i ≤ k) (hk : k ≤ P.D) :
    S.graph.dist u (P.seq k) = S.graph.dist u (P.seq i) + (k - i) :=
  dist_eq_dist_add_of_le S.acyclic P.seq_adj (P.seq_reachable hu) P.seq_inj hmin k hik hk

/-- The projection formula on the other side of the closest point. -/
theorem dist_seq_eq_add_of_ge (P : DiamPath S) {u : V} (hu : u ∈ S.alive) {i : ℕ}
    (hi : i ≤ P.D)
    (hmin : ∀ j ≤ P.D, S.graph.dist u (P.seq i) ≤ S.graph.dist u (P.seq j))
    {k : ℕ} (hk : k ≤ i) :
    S.graph.dist u (P.seq k) = S.graph.dist u (P.seq i) + (i - k) :=
  dist_eq_dist_add_of_ge S.acyclic P.seq_adj (P.seq_reachable hu) P.seq_inj hi hmin k hk

/-- A closest vertex of the diameter to `u`, in `ℕ`-indexed form. -/
theorem exists_closest_index_seq (P : DiamPath S) (u : V) :
    ∃ i ≤ P.D, ∀ j ≤ P.D, S.graph.dist u (P.seq i) ≤ S.graph.dist u (P.seq j) := by
  obtain ⟨i, hi⟩ := P.exists_closest_index u
  refine ⟨(i : ℕ), by have := i.isLt; omega, fun j hj => ?_⟩
  rw [P.seq_eq (by have := i.isLt; omega), P.seq_eq hj]
  exact hi ⟨j, by omega⟩

/-- **A vertex of a diameter is determined by its distance to the two endpoints.**  If a live vertex
`u` is at distance `j` from `Q.seq 0` and at distance `Q.D - j` from `Q.seq Q.D`, then `u` is the
`j`-th vertex of the diameter.  This is the "uniqueness of the geodesic" fact, obtained from the
projection formula. -/
theorem eq_seq_of_dist_eq (Q : DiamPath S) {u : V} (hu : u ∈ S.alive) {j : ℕ} (hj : j ≤ Q.D)
    (h1 : S.graph.dist u (Q.seq 0) = j)
    (h2 : S.graph.dist u (Q.seq Q.D) = Q.D - j) : u = Q.seq j := by
  obtain ⟨m, hmD, hm⟩ := Q.exists_closest_index_seq u
  have h0 := Q.dist_seq_eq_add_of_ge hu hmD hm (k := 0) (Nat.zero_le _)
  rw [h1] at h0
  have hmv : S.graph.dist u (Q.seq m) = j - m := by omega
  have hlast := Q.dist_seq_eq_add_of_le (i := m) hu hm hmD (le_refl Q.D)
  rw [h2, hmv] at hlast
  have hmj : m = j := by omega
  have hz : S.graph.dist u (Q.seq m) = 0 := by omega
  rw [← hmj]
  exact (S.dist_eq_zero_iff hu (Q.seq_mem m)).mp hz

/-- Two diameter paths have the same length. -/
theorem D_eq (P Q : DiamPath S) : P.D = Q.D := by
  rw [← P.diam_eq_D, Q.diam_eq_D]

section MeetIdx

variable (P Q : DiamPath S)

/-- The **last common index** of two diameters starting at the same vertex: the largest `k ≤ D`
with `P.seq k = Q.seq k`.  (`REF.md` §6 calls this `ℓ`; the vertex `P.seq ℓ = Q.seq ℓ` is the
point where the two diameters split.) -/
noncomputable def meetIdx : ℕ :=
  ((Finset.range (P.D + 1)).filter fun i => P.seq i = Q.seq i).sup (id : ℕ → ℕ)

theorem meetIdx_le : P.meetIdx Q ≤ P.D := by
  unfold meetIdx
  refine Finset.sup_le fun i hi => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hi
  show i ≤ P.D
  omega

theorem meetIdx_mem_set {i : ℕ} (hi : i ≤ P.D) (h : P.seq i = Q.seq i) :
    i ∈ (Finset.range (P.D + 1)).filter fun k => P.seq k = Q.seq k := by
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, h⟩

theorem meetIdx_max {i : ℕ} (hi : i ≤ P.D) (h : P.seq i = Q.seq i) : i ≤ P.meetIdx Q := by
  unfold meetIdx
  exact Finset.le_sup (f := id) (P.meetIdx_mem_set Q hi h)

/-- The two paths agree at the index `meetIdx`. -/
theorem seq_meetIdx_eq (h0 : P.p 0 = Q.p 0) :
    P.seq (P.meetIdx Q) = Q.seq (P.meetIdx Q) := by
  have hne : ((Finset.range (P.D + 1)).filter fun i => P.seq i = Q.seq i).Nonempty := by
    refine ⟨0, P.meetIdx_mem_set Q (Nat.zero_le _) ?_⟩
    rw [P.seq_zero, Q.seq_zero]
    exact h0
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup _ hne (id : ℕ → ℕ)
  have hi' : P.seq i = Q.seq i := (Finset.mem_filter.mp hi).2
  rw [show P.meetIdx Q = i from hsup]
  exact hi'

/-- **Prefix agreement.**  Two geodesics from the same vertex that meet again at index `i` agree at
every index up to `i`.  This makes the set of common indices an initial segment, so `meetIdx` really
is the length of the common prefix. -/
theorem seq_eq_of_le_meet {s : V} {i j : ℕ} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hi : i ≤ P.D) (hj : j ≤ i) (h : P.seq i = Q.seq i) :
    P.seq j = Q.seq j := by
  have hDi : P.D = Q.D := P.D_eq Q
  have hiQ : i ≤ Q.D := by omega
  have hjD : j ≤ P.D := le_trans hj hi
  have hjQ : j ≤ Q.D := by omega
  obtain ⟨m, hmD, hm⟩ := P.exists_closest_index_seq (Q.seq j)
  have hu : Q.seq j ∈ S.alive := Q.seq_mem j
  have hA : S.graph.dist (Q.seq j) (P.seq 0) = j := by
    rw [P.seq_zero, hP, dist_comm]
    exact Q.dist_seq_zero hQ hjQ
  have hB : S.graph.dist (Q.seq j) (P.seq i) = i - j := by
    rw [h, Q.dist_seq_seq hjQ hiQ]
    omega
  have h0 := P.dist_seq_eq_add_of_ge (i := m) hu hmD hm (k := 0) (Nat.zero_le _)
  rw [hA] at h0
  have hmval : S.graph.dist (Q.seq j) (P.seq m) = j - m := by omega
  by_cases hmi : m ≤ i
  · have h1 := P.dist_seq_eq_add_of_le (i := m) hu hm hmi hi
    rw [hB, hmval] at h1
    have hmj : m = j := by omega
    have hm0 : S.graph.dist (Q.seq j) (P.seq m) = 0 := by omega
    have hpm : P.seq m = Q.seq j :=
      (S.dist_eq_zero_iff (P.seq_mem m) hu).mp (by rw [dist_comm]; exact hm0)
    rw [hmj] at hpm
    exact hpm
  · have h1 := P.dist_seq_eq_add_of_ge (i := m) hu hmD hm (k := i) (le_of_lt (not_le.mp hmi))
    rw [hB, hmval] at h1
    have hm0 : S.graph.dist (Q.seq j) (P.seq m) = 0 := by omega
    have hpm : P.seq m = Q.seq j :=
      (S.dist_eq_zero_iff (P.seq_mem m) hu).mp (by rw [dist_comm]; exact hm0)
    have hdm : S.graph.dist s (P.seq m) = m := P.dist_seq_zero hP hmD
    have hdj : S.graph.dist s (Q.seq j) = j := Q.dist_seq_zero hQ hjQ
    rw [← hpm, hdm] at hdj
    omega

/-- The two paths agree at every index up to `meetIdx`. -/
theorem seq_eq_of_le_meetIdx {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {j : ℕ}
    (hj : j ≤ P.meetIdx Q) : P.seq j = Q.seq j :=
  P.seq_eq_of_le_meet Q hP hQ (P.meetIdx_le Q) hj (P.seq_meetIdx_eq Q (hP.trans hQ.symm))

/-- The two paths really split at `meetIdx`: either it is the whole diameter, or the next vertices
are different. -/
theorem meetIdx_eq_D_or_ne :
    P.meetIdx Q = P.D ∨ P.seq (P.meetIdx Q + 1) ≠ Q.seq (P.meetIdx Q + 1) := by
  by_cases h : P.meetIdx Q = P.D
  · exact Or.inl h
  · refine Or.inr fun hc => h ?_
    have hlt : P.meetIdx Q < P.D := lt_of_le_of_ne (P.meetIdx_le Q) h
    have hbad := P.meetIdx_max Q (i := P.meetIdx Q + 1) (by omega) hc
    omega

end MeetIdx

/-- **`REF.md` §6, Lemma 4.**  The two tails beyond the splitting point both have length
`r = D - meetIdx`, and `2r ≤ D`: two diameters sharing their starting point can only split in the
second half. -/
theorem two_mul_tail_le (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    2 * (P.D - P.meetIdx Q) ≤ P.D := by
  have hDi : P.D = Q.D := P.D_eq Q
  have hlD : P.meetIdx Q ≤ P.D := P.meetIdx_le Q
  have hlQ : P.meetIdx Q ≤ Q.D := by omega
  obtain ⟨m, hmD, hm⟩ := P.exists_closest_index_seq (Q.seq Q.D)
  have hu : Q.seq Q.D ∈ S.alive := Q.seq_mem Q.D
  have hA : S.graph.dist (Q.seq Q.D) (P.seq 0) = P.D := by
    rw [P.seq_zero, hP, dist_comm, hDi]
    exact Q.dist_seq_zero hQ (le_refl _)
  have h0 := P.dist_seq_eq_add_of_ge (i := m) hu hmD hm (k := 0) (Nat.zero_le _)
  rw [hA] at h0
  have hmval : S.graph.dist (Q.seq Q.D) (P.seq m) = P.D - m := by omega
  have hB : S.graph.dist (Q.seq Q.D) (P.seq (P.meetIdx Q)) = P.D - P.meetIdx Q := by
    rw [P.seq_meetIdx_eq Q (hP.trans hQ.symm),
      Q.dist_seq_seq (j := Q.D) (i := P.meetIdx Q) (le_refl _) hlQ]
    omega
  rcases lt_trichotomy m (P.meetIdx Q) with hlt | heq | hgt
  · have h1 := P.dist_seq_eq_add_of_le (i := m) hu hm (le_of_lt hlt) hlD
    rw [hB, hmval] at h1
    omega
  · have hlast : S.graph.dist (P.seq P.D) (Q.seq Q.D) = 2 * (P.D - P.meetIdx Q) := by
      rw [dist_comm]
      have h1 := P.dist_seq_eq_add_of_le (i := m) hu hm hmD (le_refl P.D)
      rw [h1, hmval]
      omega
    have hlive : P.seq P.D ∈ S.alive := P.seq_mem P.D
    have hle := S.dist_le_diam hlive hu
    rw [hlast, P.diam_eq_D] at hle
    omega
  · have h1 : S.graph.dist (P.seq m) (Q.seq 0) = m := by
      rw [Q.seq_zero, hQ, dist_comm]
      exact P.dist_seq_zero hP hmD
    have h2 : S.graph.dist (P.seq m) (Q.seq Q.D) = Q.D - m := by
      rw [dist_comm, hmval, hDi]
    have heq' := Q.eq_seq_of_dist_eq (P.seq_mem m) (by omega) h1 h2
    have hmax := P.meetIdx_max Q hmD heq'
    omega

/-! ## 2. The folding map identifies the two tails with the common prefix

Write `D` for the common diameter length, `ℓ = meetIdx` and `r = D - ℓ`.  Folding acts on the `i`-th
vertex of a diameter by the mirror map `i ↦ min i (D - i)`; by §1 the mirror image of a common index
is the same for both paths, and by Lemma 4 we have `r ≤ ℓ`, so the mirror image of `ℓ + t`
(`1 ≤ t ≤ r`) is `r - t`, an index in the common prefix.  This is `REF.md` §6, Lemma 4/§7 (1). -/

/-- `ℓ + r = D`. -/
theorem meetIdx_add_tail (P Q : DiamPath S) :
    P.meetIdx Q + (P.D - P.meetIdx Q) = P.D :=
  Nat.add_sub_cancel' (P.meetIdx_le Q)

/-- **Lemma 4, inequality form.**  The tail length `r` is at most the common prefix length `ℓ`. -/
theorem tail_le_meetIdx (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    P.D - P.meetIdx Q ≤ P.meetIdx Q := by
  have h := P.two_mul_tail_le Q hP hQ
  omega

/-- The folding map on the `k`-th vertex of a diameter is the mirror map `k ↦ min k (D - k)`. -/
theorem rep_seq (P : DiamPath S) {k : ℕ} (hk : k ≤ P.D) :
    P.rep (P.seq k) = P.seq (min k (P.D - k)) := by
  rw [P.seq_eq hk, P.rep_path ⟨k, by omega⟩]
  exact (P.seq_eq (le_trans (Nat.min_le_left k (P.D - k)) hk)).symm

/-- Vertices in the first half of a diameter are fixed by the folding map. -/
theorem rep_seq_eq_self (P : DiamPath S) {k : ℕ} (hk : 2 * k ≤ P.D) :
    P.rep (P.seq k) = P.seq k := by
  rw [P.rep_seq (by omega)]
  congr 1
  omega

/-- The two folding maps agree on the common prefix. -/
theorem rep_seq_eq_of_le_meetIdx (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {i : ℕ} (hi : i ≤ P.meetIdx Q) : P.rep (P.seq i) = Q.rep (Q.seq i) := by
  have hDi : P.D = Q.D := P.D_eq Q
  have hiD : i ≤ P.D := le_trans hi (P.meetIdx_le Q)
  rw [P.rep_seq hiD, Q.rep_seq (by omega),
    P.seq_eq_of_le_meetIdx Q hP hQ (le_trans (Nat.min_le_left _ _) hi),
    show min i (Q.D - i) = min i (P.D - i) by omega]

/-- The two paths agree on the whole prefix, in particular at the tail indices `r - t`. -/
theorem seq_tail_eq (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {t : ℕ}
    (ht : t ≤ P.D - P.meetIdx Q) :
    P.seq (P.D - P.meetIdx Q - t) = Q.seq (P.D - P.meetIdx Q - t) :=
  P.seq_eq_of_le_meetIdx Q hP hQ (by have := P.tail_le_meetIdx Q hP hQ; omega)

/-- **The `t`-th vertex of the `P`-tail is folded onto the prefix vertex `p (r - t)`.** -/
theorem rep_seq_tail (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {t : ℕ}
    (ht : 1 ≤ t) (htr : t ≤ P.D - P.meetIdx Q) :
    P.rep (P.seq (P.meetIdx Q + t)) = P.seq (P.D - P.meetIdx Q - t) := by
  have h := P.two_mul_tail_le Q hP hQ
  rw [P.rep_seq (by omega)]
  congr 1
  omega

/-- **The `t`-th vertex of the `Q`-tail is folded onto the same prefix vertex `p (r - t)`.** -/
theorem rep_seq_tail_Q (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {t : ℕ}
    (ht : 1 ≤ t) (htr : t ≤ P.D - P.meetIdx Q) :
    Q.rep (Q.seq (P.meetIdx Q + t)) = P.seq (P.D - P.meetIdx Q - t) := by
  have h := P.two_mul_tail_le Q hP hQ
  have hDi : P.D = Q.D := P.D_eq Q
  rw [Q.rep_seq (by omega)]
  rw [show min (P.meetIdx Q + t) (Q.D - (P.meetIdx Q + t)) = P.D - P.meetIdx Q - t by omega,
    P.seq_tail_eq Q hP hQ htr]

/-- The vertex `p r`, where the two folded trees are glued to the surviving tail.  In `P.foldState`
the `Q`-tail `q_{ℓ+1}, …, q_D` hangs there; in `Q.foldState` the `P`-tail does. -/
theorem rep_seq_meetIdx (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    P.rep (P.seq (P.meetIdx Q)) = P.seq (P.D - P.meetIdx Q) := by
  have h := P.two_mul_tail_le Q hP hQ
  rw [P.rep_seq (P.meetIdx_le Q)]
  congr 1
  omega

/-! ## 3. The structure of the two folded states

Everything the two folds do to the common prefix is the same, and both tails land on the spine
`p 0, …, p r` (`r = D - ℓ`).  The only vertices on which `P.foldState` and `Q.foldState` differ are
the two tails themselves and the subtrees hanging off them; this section collects the concrete
membership and adjacency facts for those tails. -/

/-- A walk along a sequence of consecutive adjacent vertices. -/
theorem exists_walk_of_seq {H : SimpleGraph V} {n : ℕ} {q : ℕ → V}
    (hadj : ∀ k < n, H.Adj (q k) (q (k + 1))) :
    ∃ w : H.Walk (q 0) (q n), w.length = n := by
  induction n with
  | zero => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | succ n ih =>
      obtain ⟨w, hw⟩ := ih fun k hk => hadj k (by omega)
      exact ⟨w.concat (hadj n (by omega)), by rw [SimpleGraph.Walk.length_concat, hw]⟩

/-- `meetIdx` is symmetric. -/
theorem meetIdx_comm (P Q : DiamPath S) (h0 : P.p 0 = Q.p 0) : P.meetIdx Q = Q.meetIdx P := by
  have hDi : P.D = Q.D := P.D_eq Q
  refine le_antisymm ?_ ?_
  · refine Q.meetIdx_max P (i := P.meetIdx Q) (by have := P.meetIdx_le Q; omega) ?_
    exact (P.seq_meetIdx_eq Q h0).symm
  · refine P.meetIdx_max Q (i := Q.meetIdx P) (by have := Q.meetIdx_le P; omega) ?_
    exact (Q.seq_meetIdx_eq P h0.symm).symm

/-- **The `Q`-tail is off the `P`-diameter**, hence fixed by the folding map of `P`: it survives in
`P.foldState` and hangs at `P.seq r`. -/
theorem rep_off_path (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {j : ℕ} (hj : P.meetIdx Q < j) (hjD : j ≤ P.D) : P.rep (Q.seq j) = Q.seq j := by
  have hDi : P.D = Q.D := P.D_eq Q
  have hjQ : j ≤ Q.D := by omega
  refine P.rep_eq_self fun i hi => ?_
  have hiD : (i : ℕ) ≤ P.D := by have := i.isLt; omega
  have hval : (i : ℕ) = j := by
    have h1 : S.graph.dist s (P.seq (i : ℕ)) = (i : ℕ) := P.dist_seq_zero hP hiD
    have h2 : S.graph.dist s (Q.seq j) = j := Q.dist_seq_zero hQ hjQ
    have : S.graph.dist s (P.seq (i : ℕ)) = S.graph.dist s (Q.seq j) := by rw [P.seq_val i, hi]
    omega
  have hmeet : P.seq j = Q.seq j := by
    rw [← hval, P.seq_val i, hi, ← hval]
  exact absurd (P.meetIdx_max Q hjD hmeet) (by omega)

/-- The `Q`-tail is a set of vertices of `P.foldState`. -/
theorem mem_foldAlive_off_path (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {j : ℕ} (hj : P.meetIdx Q < j) (hjD : j ≤ P.D) : Q.seq j ∈ P.foldAlive :=
  P.mem_foldAlive.mpr ⟨Q.seq_mem j, P.rep_off_path Q hP hQ hj hjD⟩

/-- Symmetric form: the `P`-tail is off the `Q`-diameter. -/
theorem rep_off_path' (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {j : ℕ} (hj : P.meetIdx Q < j) (hjD : j ≤ P.D) : Q.rep (P.seq j) = P.seq j := by
  have hcomm := P.meetIdx_comm Q (hP.trans hQ.symm)
  have hDi : P.D = Q.D := P.D_eq Q
  exact Q.rep_off_path P hQ hP (by omega) (by omega)

/-- The `P`-tail is a set of vertices of `Q.foldState`. -/
theorem mem_foldAlive_off_path' (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {j : ℕ} (hj : P.meetIdx Q < j) (hjD : j ≤ P.D) : P.seq j ∈ Q.foldAlive :=
  Q.mem_foldAlive.mpr ⟨P.seq_mem j, P.rep_off_path' Q hP hQ hj hjD⟩

/-- The gluing edge of `P.foldState`: the surviving `Q`-tail is attached at the spine vertex
`P.seq r`. -/
theorem foldGraph_adj_leg (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) :
    P.foldGraph.Adj (P.seq (P.D - P.meetIdx Q)) (Q.seq (P.meetIdx Q + 1)) := by
  have htw := P.two_mul_tail_le Q hP hQ
  have hlD := P.meetIdx_le Q
  have hDi : P.D = Q.D := P.D_eq Q
  have hℓ : P.seq (P.meetIdx Q) = Q.seq (P.meetIdx Q) := P.seq_meetIdx_eq Q (hP.trans hQ.symm)
  have h1 : S.graph.dist s (P.seq (P.D - P.meetIdx Q)) = P.D - P.meetIdx Q :=
    P.dist_seq_zero hP (by omega)
  have h2 : S.graph.dist s (Q.seq (P.meetIdx Q + 1)) = P.meetIdx Q + 1 :=
    Q.dist_seq_zero hQ (by omega)
  refine ⟨?_, P.foldCone_seq_mem (by omega),
    P.mem_foldAlive_off_path Q hP hQ (by omega) (by omega),
    Q.seq (P.meetIdx Q), Q.seq (P.meetIdx Q + 1), Q.seq_adj (P.meetIdx Q) (by omega), ?_, ?_⟩
  · intro h
    have heq : P.D - P.meetIdx Q = P.meetIdx Q + 1 := by rw [← h1, h, h2]
    have hmeet : P.seq (P.D - P.meetIdx Q) = Q.seq (P.D - P.meetIdx Q) := by
      rw [heq] at h ⊢
      exact h
    exact absurd (P.meetIdx_max Q (i := P.D - P.meetIdx Q) (by omega) hmeet) (by omega)
  · rw [← hℓ]
    exact P.rep_seq_meetIdx Q hP hQ
  · exact P.rep_off_path Q hP hQ (by omega) (by omega)

/-- The edges of the surviving `Q`-tail inside `P.foldState`. -/
theorem foldGraph_adj_tail (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {j : ℕ} (hj : P.meetIdx Q < j) (hjD : j < P.D) :
    P.foldGraph.Adj (Q.seq j) (Q.seq (j + 1)) := by
  have hDi : P.D = Q.D := P.D_eq Q
  refine ⟨?_, P.mem_foldAlive_off_path Q hP hQ hj (by omega),
    P.mem_foldAlive_off_path Q hP hQ (by omega) (by omega),
    Q.seq j, Q.seq (j + 1), Q.seq_adj j (by omega), ?_, ?_⟩
  · intro h
    exact absurd (Q.seq_inj j (by omega) (j + 1) (by omega) h) (by omega)
  · exact P.rep_off_path Q hP hQ hj (by omega)
  · exact P.rep_off_path Q hP hQ (by omega) (by omega)

/-- **The leg of `P.foldState` has length exactly `2r`** (upper bound): the surviving `Q`-tail is a
path of length `r` attached at `P.seq r`, and `P.seq 0, …, P.seq r` is a path of length `r`. -/
theorem dist_leg_le (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) :
    P.foldGraph.dist (P.seq 0) (Q.seq Q.D) ≤ 2 * (P.D - P.meetIdx Q) := by
  have htw := P.two_mul_tail_le Q hP hQ
  have hlD := P.meetIdx_le Q
  have hDi : P.D = Q.D := P.D_eq Q
  obtain ⟨w₁, hw₁⟩ := exists_walk_of_seq (H := P.foldGraph) (q := P.seq) (n := P.D - P.meetIdx Q)
    (fun k hk => P.foldCone_seq_adj k (by omega))
  have hglue : P.foldGraph.Adj (P.seq (P.D - P.meetIdx Q)) (Q.seq (P.meetIdx Q + 1)) :=
    P.foldGraph_adj_leg Q hP hQ (by omega)
  obtain ⟨w₃, hw₃⟩ := exists_walk_of_seq (H := P.foldGraph)
    (q := fun k => Q.seq (P.meetIdx Q + 1 + k)) (n := P.D - P.meetIdx Q - 1)
    (fun k hk => by
      have hltD : P.meetIdx Q + 1 + k < P.D := by omega
      have h := P.foldGraph_adj_tail Q hP hQ (j := P.meetIdx Q + 1 + k) (by omega) hltD
      rwa [show P.meetIdx Q + 1 + k + 1 = P.meetIdx Q + 1 + (k + 1) by omega] at h)
  have hend : Q.seq (P.meetIdx Q + 1 + (P.D - P.meetIdx Q - 1)) = Q.seq Q.D := by
    rw [show P.meetIdx Q + 1 + (P.D - P.meetIdx Q - 1) = Q.D by omega]
  refine le_trans (SimpleGraph.dist_le (((w₁.concat hglue).append w₃).copy rfl hend)) ?_
  rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_concat, hw₁, hw₃]
  omega

/-- **The leg of `P.foldState`**: the surviving half `P.seq 0, …, P.seq r` of the `P`-diameter
followed by the surviving `Q`-tail `Q.seq (ℓ+1), …, Q.seq D`.  It is a path of length exactly `2r`
(Theorem `dist_leg` below), which is the longest path from `s` as soon as the folded state has
diameter `2r`. -/
noncomputable def legSeq (P Q : DiamPath S) (k : ℕ) : V :=
  if k ≤ P.D - P.meetIdx Q then P.seq k
  else Q.seq (P.meetIdx Q + (k - (P.D - P.meetIdx Q)))

theorem legSeq_of_le (P Q : DiamPath S) {k : ℕ} (hk : k ≤ P.D - P.meetIdx Q) :
    P.legSeq Q k = P.seq k := by
  rw [legSeq]
  exact ite_eq_left hk

theorem legSeq_of_lt (P Q : DiamPath S) {k : ℕ} (hk : P.D - P.meetIdx Q < k) :
    P.legSeq Q k = Q.seq (P.meetIdx Q + (k - (P.D - P.meetIdx Q))) := by
  rw [legSeq]
  exact ite_eq_right (not_le.mpr hk)

theorem legSeq_zero (P Q : DiamPath S) : P.legSeq Q 0 = P.seq 0 :=
  P.legSeq_of_le Q (Nat.zero_le _)

/-- The leg ends at the far end of the `Q`-diameter. -/
theorem legSeq_two_mul (P Q : DiamPath S) (hr : 1 ≤ P.D - P.meetIdx Q) :
    P.legSeq Q (2 * (P.D - P.meetIdx Q)) = Q.seq Q.D := by
  have hDi : P.D = Q.D := P.D_eq Q
  rw [P.legSeq_of_lt Q (by omega),
    show P.meetIdx Q + (2 * (P.D - P.meetIdx Q) - (P.D - P.meetIdx Q)) = Q.D by omega]

/-- Distance in the original tree from `s` to the `k`-th vertex of the leg. -/
theorem legSeq_dist_S (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) {k : ℕ} (hk : k ≤ 2 * (P.D - P.meetIdx Q)) :
    S.graph.dist s (P.legSeq Q k) =
      if k ≤ P.D - P.meetIdx Q then k else P.meetIdx Q + (k - (P.D - P.meetIdx Q)) := by
  have hDi : P.D = Q.D := P.D_eq Q
  by_cases h : k ≤ P.D - P.meetIdx Q
  · rw [ite_eq_left h, P.legSeq_of_le Q h]
    exact P.dist_seq_zero hP (by omega)
  · rw [ite_eq_right h, P.legSeq_of_lt Q (by omega), Q.dist_seq_zero hQ (by omega)]

/-- The leg has no repeated vertex (it is a path). -/
theorem legSeq_inj (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) :
    ∀ k ≤ 2 * (P.D - P.meetIdx Q), ∀ l ≤ 2 * (P.D - P.meetIdx Q),
      P.legSeq Q k = P.legSeq Q l → k = l := by
  have htail := P.tail_le_meetIdx Q hP hQ
  intro k hk l hl h
  have hk' := P.legSeq_dist_S Q hP hQ hr hk
  have hl' := P.legSeq_dist_S Q hP hQ hr hl
  rw [h] at hk'
  rw [hk'] at hl'
  by_cases h1 : k ≤ P.D - P.meetIdx Q <;> by_cases h2 : l ≤ P.D - P.meetIdx Q
  · simp only [ite_eq_left h1, ite_eq_left h2] at hl'; omega
  · simp only [ite_eq_left h1, ite_eq_right h2] at hl'; omega
  · simp only [ite_eq_right h1, ite_eq_left h2] at hl'; omega
  · simp only [ite_eq_right h1, ite_eq_right h2] at hl'; omega

/-- The leg is a path of the folded tree `P.foldState`. -/
theorem legSeq_adj (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) :
    ∀ k < 2 * (P.D - P.meetIdx Q), P.foldGraph.Adj (P.legSeq Q k) (P.legSeq Q (k + 1)) := by
  have htw := P.two_mul_tail_le Q hP hQ
  intro k hk
  by_cases h : k + 1 ≤ P.D - P.meetIdx Q
  · rw [P.legSeq_of_le Q h, P.legSeq_of_le Q (by omega)]
    exact P.foldCone_seq_adj k (by omega)
  · have hkr : P.D - P.meetIdx Q ≤ k := by omega
    rcases eq_or_lt_of_le hkr with heq | hlt
    · rw [P.legSeq_of_le Q (le_of_eq heq.symm), P.legSeq_of_lt Q (by omega),
        show P.meetIdx Q + (k + 1 - (P.D - P.meetIdx Q)) = P.meetIdx Q + 1 by omega, ← heq]
      exact P.foldGraph_adj_leg Q hP hQ (by omega)
    · rw [P.legSeq_of_lt Q (by omega), P.legSeq_of_lt Q (by omega),
        show P.meetIdx Q + (k + 1 - (P.D - P.meetIdx Q)) =
          P.meetIdx Q + (k - (P.D - P.meetIdx Q)) + 1 by omega]
      exact P.foldGraph_adj_tail Q hP hQ (j := P.meetIdx Q + (k - (P.D - P.meetIdx Q)))
        (by omega) (by omega)

/-- Vertices of the leg are vertices of the folded tree. -/
theorem legSeq_mem (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) {k : ℕ} (hk : k ≤ 2 * (P.D - P.meetIdx Q)) :
    P.legSeq Q k ∈ P.foldAlive := by
  by_cases h : k ≤ P.D - P.meetIdx Q
  · rw [P.legSeq_of_le Q h]
    exact P.foldCone_seq_mem (by have := P.two_mul_tail_le Q hP hQ; omega)
  · rw [P.legSeq_of_lt Q (by omega)]
    exact P.mem_foldAlive_off_path Q hP hQ (by omega) (by omega)

/-- **The leg of `P.foldState` has length exactly `2r`.**  The upper bound is the explicit walk of
`dist_leg_le`; for the lower bound, the projection formula of the tree `P.foldState` along the leg
shows that the closest vertex of the leg to its own far end is that far end, and then the distance
to `s` is the distance along the leg. -/
theorem dist_leg (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) :
    P.foldGraph.dist (P.seq 0) (Q.seq Q.D) = 2 * (P.D - P.meetIdx Q) := by
  have htw := P.two_mul_tail_le Q hP hQ
  have hDi : P.D = Q.D := P.D_eq Q
  refine le_antisymm (P.dist_leg_le Q hP hQ hr) ?_
  have hmem : ∀ k ≤ 2 * (P.D - P.meetIdx Q), P.legSeq Q k ∈ P.foldAlive :=
    fun k hk => P.legSeq_mem Q hP hQ hr hk
  have hreach : ∀ k ≤ 2 * (P.D - P.meetIdx Q),
      P.foldGraph.Reachable (P.legSeq Q (2 * (P.D - P.meetIdx Q))) (P.legSeq Q k) :=
    fun k hk => P.foldState.connected _ (hmem _ le_rfl) _ (hmem k hk)
  have hmin : ∀ j ≤ 2 * (P.D - P.meetIdx Q),
      P.foldGraph.dist (P.legSeq Q (2 * (P.D - P.meetIdx Q))) (P.legSeq Q (2 * (P.D - P.meetIdx Q)))
        ≤ P.foldGraph.dist (P.legSeq Q (2 * (P.D - P.meetIdx Q))) (P.legSeq Q j) :=
    fun j _ => by rw [dist_self]; exact Nat.zero_le _
  have hproj := dist_eq_dist_add_of_ge (G := P.foldGraph) P.foldGraph_isAcyclic
    (p := P.legSeq Q) (n := 2 * (P.D - P.meetIdx Q)) (P.legSeq_adj Q hP hQ hr) hreach
    (P.legSeq_inj Q hP hQ hr) (i := 2 * (P.D - P.meetIdx Q)) le_rfl hmin 0 (Nat.zero_le _)
  rw [P.legSeq_zero Q, P.legSeq_two_mul Q hr, dist_self, Nat.zero_add] at hproj
  rw [dist_comm, hproj]
  omega


/-- The common spine `P.seq 0, …, P.seq r` is fixed by the folding map of `P`. -/
theorem rep_spine (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {k : ℕ}
    (hk : k ≤ P.D - P.meetIdx Q) : P.rep (P.seq k) = P.seq k :=
  P.rep_seq_eq_self (by have := P.two_mul_tail_le Q hP hQ; omega)

/-- The common spine is also fixed by the folding map of `Q`. -/
theorem rep_spine' (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {k : ℕ}
    (hk : k ≤ P.D - P.meetIdx Q) : Q.rep (P.seq k) = P.seq k := by
  have hDi : P.D = Q.D := P.D_eq Q
  have hkk : k ≤ P.meetIdx Q := by have := P.tail_le_meetIdx Q hP hQ; omega
  have hseq := P.seq_eq_of_le_meetIdx Q hP hQ hkk
  rw [hseq]
  exact Q.rep_seq_eq_self (by have := P.two_mul_tail_le Q hP hQ; omega)

/-- Vertices of the spine belong to both folded states. -/
theorem seq_mem_both (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {k : ℕ}
    (hk : k ≤ P.D - P.meetIdx Q) : P.seq k ∈ P.foldAlive ∧ P.seq k ∈ Q.foldAlive :=
  ⟨P.mem_foldAlive.mpr ⟨P.seq_mem k, P.rep_spine Q hP hQ hk⟩,
    Q.mem_foldAlive.mpr ⟨P.seq_mem k, P.rep_spine' Q hP hQ hk⟩⟩

/-- The two legs coincide on the spine `s = P.seq 0, …, P.seq r`. -/
theorem legSeq_eq_legSeq (P Q : DiamPath S) (h0 : P.p 0 = Q.p 0) {k : ℕ}
    (hk : k ≤ P.D - P.meetIdx Q) : P.legSeq Q k = Q.legSeq P k := by
  have hcomm := P.meetIdx_comm Q h0
  have hDi : P.D = Q.D := P.D_eq Q
  have hk' : k ≤ Q.D - Q.meetIdx P := by
    rw [← hDi, ← hcomm]
    exact hk
  have htail : P.D - P.meetIdx Q ≤ P.meetIdx Q := P.tail_le_meetIdx Q h0 rfl
  rw [P.legSeq_of_le Q hk, Q.legSeq_of_le P hk',
    P.seq_eq_of_le_meetIdx Q h0 rfl (by omega)]

/-- **The leg of `Q.foldState` also has length exactly `2r`.**  This is `dist_leg` with the two
diameters exchanged; the surviving `P`-tail hangs at the same spine vertex `P.seq r`. -/
theorem dist_leg' (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hr : 1 ≤ P.D - P.meetIdx Q) :
    Q.foldGraph.dist (P.seq 0) (P.seq P.D) = 2 * (P.D - P.meetIdx Q) := by
  have hcomm := P.meetIdx_comm Q (hP.trans hQ.symm)
  have hDi : P.D = Q.D := P.D_eq Q
  have hcase : Q.seq 0 = P.seq 0 := by rw [Q.seq_zero, hQ, ← hP, P.seq_zero]
  have h := Q.dist_leg P hQ hP (by omega)
  rwa [show Q.D - Q.meetIdx P = P.D - P.meetIdx Q by omega, hcase] at h

/-! ## 4. What remains

The two facts proved above are the two ends of the `REF.md` §7 argument.  What is still missing is
the *synchronised phase* and the *endgame*; the statements below are the exact obligations, in the
order in which they should be attacked (they are deliberately **not** stated in the file, so that
the file stays free of `sorry`).

**(a) The common part.**  Let `C : Finset V` be the complement of

    Δ := {P.seq i : ℓ < i} ∪ {Q.seq j : ℓ < j} ∪ (the vertices whose `s`-path meets one of those)

(equivalently `v ∉ Δ ↔ ∀ x ∈ Δ, dist_S s v ≠ dist_S s x + dist_S x v`).  `C` is closed under
`s`-paths in `S`, and one must show

    `∀ u v ∈ C, (u ∈ P.foldAlive ↔ u ∈ Q.foldAlive) ∧ (P.foldGraph.Adj u v ↔ Q.foldGraph.Adj u v)`

("the two folded states agree on the common part") together with the two distance bounds

    `∀ v ∈ Δ, v ∈ P.foldAlive → P.foldGraph.dist (P.seq 0) v ≤ 2r`   (and the same for `Q`).

The distance bounds are the computations of §2/§3: a vertex of the `Q`-tail is `Q.seq (ℓ+t)`, which
survives in `P.foldState` at distance `r + t ≤ 2r`, and a vertex hanging below `Q.seq (ℓ+t)` adds at
most `min (ℓ+t) (D-ℓ-t) = r - t` (Lemma 1) more; symmetrically on the `Q` side.  Together with
`dist_leg`/`dist_leg'` this gives

    `P.foldState.diam = Q.foldState.diam = max (2 * (P.D - P.meetIdx Q)) M`

where `M` is the (common) maximum of `dist (P.seq 0) ·` over the common part.

**(b) Phase 1 (synchronised folds).**  While `H := P.foldState.diam > 2r`, take a vertex `z` at
distance `H` from `s` in `P.foldState`; by (a) it is at distance `H` in `Q.foldState` too, the
`s`-`z` paths agree, and that common path `Z` is a diameter of both states.  Because `H > 2r` and
`Z` lies in the common part, the fold map `ρ_Z` is the identity on `Δ` and on the spine, hence

    `(ρ_Z (P.foldState)).Adj u v ↔ (ρ_Z (Q.foldState)).Adj u v`  for `u, v ∈ C`

(the `∃ x y, Adj x y ∧ ρ x = u ∧ ρ y = v` form of `foldGraph_adj` plus `ρ = id` on `Δ`), and the
whole situation of (a) is reproduced with `H` strictly smaller.  Induction on `H` reduces to
`H = 2r`.

**(c) The endgame.**  For `H = 2r`, `Z₁ := P.legSeq Q` (resp. `Z₂ := Q.legSeq P`) is a diameter
path of `P.foldState` (resp. `Q.foldState`) starting at `s`, by `dist_leg`/`dist_leg'` and (a).  The
statement to prove is

    `∃ (Z₁ : DiamPath P.foldState) (Z₂ : DiamPath Q.foldState),
        Z₁.p 0 = s ∧ Z₂.p 0 = s ∧ Z₁.foldState = Z₂.foldState`

with `Z₁ := P.legSeq Q` and `Z₂ := Q.legSeq P`.  Folding along them identifies `Z₁.rep ∘ P.rep`
with `Z₂.rep ∘ Q.rep` (`REF.md` §7: the `t`-th vertex of either tail goes to `P.seq (r-t)`, carrying
its hanging subtree; by `rep_seq_tail`/`rep_seq_tail_Q` both tails land on the same spine vertex, and
the pieces attached to the spine are already in the same place by (a)), and then
`foldGraph_adj`'s witness description gives the equality of the two folded states.

**(d) Assembly.**  (b) gives `m` with `FoldSeqAt s P.foldState U m` and `FoldSeqAt s Q.foldState U m`
for a common state `U`; (c) gives the last step for both.  Then `LValue P.foldState s n ↔
LValue Q.foldState s n` for `n = m + 1 + ·` and `exchange` follows from
`LValue_exists_of_isDiamEnd`. -/


end DiamPath

end OhtoaiTreeProof
