/-
# REF.md §7, phase 2: the synchronised phase

`REF.md` Lemma 5 (the *delayed exchange lemma*) says that for a diameter endpoint `s` of a state `S`
and two diameters `P`, `Q` of `S` starting at `s`, the two folded trees `P.foldState` and
`Q.foldState` admit complete folding processes towards `s` of the *same* length.  The proof runs in
two phases:

* **phase 1** (`OhtoaiTreeProof/Phase1.lean`) describes the region `Δ` where the two folds differ
  and shows that it is small: the two folded states agree on the common part `C = Δᶜ` in vertices
  and in edges, and every surviving vertex of `Δ` is within distance `2r` of `s` in either folded
  state (`r = P.D - P.meetIdx Q`).
* **phase 2** (this file) uses that description.

The mathematical content of this file is:

* **§1–§3**, the walk/distance toolkit.  In an acyclic graph a walk whose vertex sequence is
  injective has length equal to the distance of its endpoints (§1); a geodesic `s, …, v` of a tree
  decomposes at its `k`-th vertex (§2); and consequently the surviving half `p 0, …, p (D/2)` of a
  diameter is a *geodesic* of the folded tree (§3).  These are the tools that turn a "sequence of
  pairwise distinct adjacent vertices" into an exact distance computation, both in `P.foldState`
  and in `Q.foldState`.
* **§4**, the *folded depth*: a live vertex `v` of the common part sits in the folded trees at a
  distance which is computed from its projection `P.seq i` on the `P`-diameter and its height `h`
  above it.  The *same* formula holds in both folded states — this is what makes the two folded
  diameters equal.
* **§5**, `Phase1Inv`, the invariant of the synchronised phase, and the reduction of the exchange
  lemma to it.

The invariant `Phase1Inv` records exactly what the endgame (`OhtoaiTreeProof/ExchangeProof.lean`)
needs: a diameter endpoint of both states, equal diameters, agreement of the two states on the
common part `C` of the *original* pair of diameters (vertices and edges), and the `Δ`-bound.
-/
import OhtoaiTreeProof.Phase1
import OhtoaiTreeProof.ExchangeProof

set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Walks along an injective sequence

The folding map of a diameter turns an edge into an edge or collapses it, so a path of `S` produces
a *walk* of the folded tree, but not necessarily a path.  The lemmas below give the converse
direction used throughout this file: a sequence of pairwise distinct vertices with consecutive
adjacency can be realised by an actual path, and in an acyclic graph a path realises the distance of
its endpoints.  Together they say that "exhibiting a sequence of distinct adjacent vertices of
length `n`" *is* the way to compute distances in the folded trees. -/

section SeqWalk

variable {W : Type*}

/-- **A walk along an injective sequence is a path.**  If `q 0, …, q n` are pairwise distinct
vertices with `q k` adjacent to `q (k+1)`, then there is a path of length `n` from `q 0` to `q n`. -/
theorem exists_isPath_walk_of_seq {H : SimpleGraph W} {n : ℕ} {q : ℕ → W}
    (hadj : ∀ k < n, H.Adj (q k) (q (k + 1)))
    (hinj : ∀ k ≤ n, ∀ l ≤ n, q k = q l → k = l) :
    ∃ w : H.Walk (q 0) (q n), w.IsPath ∧ w.length = n := by
  suffices h : ∀ d m : ℕ, m + d = n → ∃ w : H.Walk (q m) (q n), w.IsPath ∧ w.length = d ∧
      ∀ x ∈ w.support, ∃ j, m ≤ j ∧ j ≤ n ∧ q j = x by
    obtain ⟨w, hw, hlen, -⟩ := h n 0 (by omega)
    exact ⟨w, hw, by simpa using hlen⟩
  intro d
  induction d with
  | zero =>
      intro m hm
      have hm' : m = n := by omega
      rw [hm']
      exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp,
        by rintro x hx
           rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
           exact ⟨n, le_rfl, le_rfl, hx.symm⟩⟩
  | succ d ih =>
      intro m hm
      obtain ⟨w, hw, hlen, hsupp⟩ := ih (m + 1) (by omega)
      refine ⟨SimpleGraph.Walk.cons (hadj m (by omega)) w, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨hw, fun hmem => ?_⟩
        obtain ⟨j, hj1, hj2, hjeq⟩ := hsupp (q m) hmem
        have : m = j := hinj m (by omega) j hj2 hjeq.symm
        omega
      · simp [SimpleGraph.Walk.length_cons, hlen]
      · intro x hx
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨m, le_rfl, by omega, rfl⟩
        · obtain ⟨j, hj1, hj2, hj⟩ := hsupp x hx
          exact ⟨j, by omega, hj2, hj⟩

/-- **In an acyclic graph a path has the length of the distance of its endpoints.**  There is only
one path between two vertices, and it is the shortest walk. -/
theorem length_eq_dist_of_isPath {H : SimpleGraph W} (hH : H.IsAcyclic) {u v : W} {p : H.Walk u v}
    (hp : p.IsPath) : p.length = H.dist u v := by
  obtain ⟨q, hq, hlen⟩ := (show H.Reachable u v from ⟨p⟩).exists_path_of_dist
  have hsub : (⟨p, hp⟩ : H.Path u v) = ⟨q, hq⟩ :=
    @Subsingleton.elim (H.Path u v) (hH.subsingleton_path u v) _ _
  have hcongr := congrArg (fun r : H.Path u v => (r : H.Walk u v).length) hsub
  simpa [hlen] using hcongr

/-- **Distance computed from an injective adjacent sequence.**  In an acyclic graph, if
`q 0, …, q n` are pairwise distinct and consecutive ones are adjacent, then the distance from `q 0`
to `q n` is exactly `n`. -/
theorem dist_eq_of_seq {H : SimpleGraph W} (hH : H.IsAcyclic) {n : ℕ} {q : ℕ → W}
    (hadj : ∀ k < n, H.Adj (q k) (q (k + 1)))
    (hinj : ∀ k ≤ n, ∀ l ≤ n, q k = q l → k = l) :
    H.dist (q 0) (q n) = n := by
  obtain ⟨w, hw, hlen⟩ := exists_isPath_walk_of_seq hadj hinj
  have := length_eq_dist_of_isPath hH hw
  omega

end SeqWalk

/-! ## 2. Decomposing a geodesic at one of its vertices

A geodesic walk of a tree splits at its `k`-th vertex into a geodesic from the start and a geodesic
to the end.  This is the form in which the `Δ`-description of `Phase1.lean` is used: a vertex `w` on
the path from `s` to `v` gives the decomposition `dist s v = dist s w + dist w v`, which is exactly
the condition for `v` to belong to `Δ` when `w` is a tail vertex. -/

section Geodesic

variable {W : Type*}

/-- **A geodesic is graded by the distance to its start.** -/
theorem dist_getVert_eq {H : SimpleGraph W} (hH : H.IsAcyclic) {a b : W} {p : H.Walk a b}
    (hp : p.IsPath) {k : ℕ} (hk : k ≤ p.length) : H.dist a (p.getVert k) = k := by
  obtain ⟨q, hq, hlen⟩ :=
    (show H.Reachable a (p.getVert k) from ⟨p.take k⟩).exists_path_of_dist
  have hsub : (⟨p.take k, hp.take k⟩ : H.Path a (p.getVert k)) = ⟨q, hq⟩ :=
    @Subsingleton.elim (H.Path a (p.getVert k)) (hH.subsingleton_path a _) _ _
  have hval : (p.take k : H.Walk a (p.getVert k)) = q := congrArg Subtype.val hsub
  have hl : (p.take k).length = q.length := by rw [hval]
  rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hk] at hl
  omega

/-- **A geodesic is graded by the distance to its end.** -/
theorem dist_getVert_eq_sub {H : SimpleGraph W} (hH : H.IsAcyclic) {a b : W} {p : H.Walk a b}
    (hp : p.IsPath) {k : ℕ} (_hk : k ≤ p.length) : H.dist (p.getVert k) b = p.length - k := by
  obtain ⟨q, hq, hlen⟩ :=
    (show H.Reachable (p.getVert k) b from ⟨p.drop k⟩).exists_path_of_dist
  have hsub : (⟨p.drop k, hp.drop k⟩ : H.Path (p.getVert k) b) = ⟨q, hq⟩ :=
    @Subsingleton.elim (H.Path (p.getVert k) b) (hH.subsingleton_path _ _) _ _
  have hval : (p.drop k : H.Walk (p.getVert k) b) = q := congrArg Subtype.val hsub
  have hl : (p.drop k).length = q.length := by rw [hval]
  rw [SimpleGraph.Walk.drop_length] at hl
  omega

end Geodesic

/-! ## 3. The surviving half of a diameter is a geodesic of the folded tree

This is the basic distance computation in the folded state: the folded diameter vertices
`P.seq 0, …, P.seq (D/2)` are pairwise distinct (`foldCone_seq_inj`) and consecutive ones are
adjacent (`foldCone_seq_adj`), so by §1 the distance along them is the index difference. -/

namespace DiamPath

variable {S : TreeState V}

/-- **The phase-1 invariant** of the synchronised phase, for the original pair `P`, `Q` and `s`. -/
structure Phase1Inv (P Q : DiamPath S) (T₁ T₂ : TreeState V) (s : V) : Prop where
  /-- `s` is a diameter endpoint of the first state -/
  end₁ : IsDiamEnd T₁ s
  /-- `s` is a diameter endpoint of the second state -/
  end₂ : IsDiamEnd T₂ s
  /-- the two states have the same diameter -/
  diam_eq : T₁.diam = T₂.diam
  /-- outside the difference region the two states have the same live vertices -/
  mem_iff : ∀ v : V, v ∉ P.Delta Q s → (v ∈ T₁.alive ↔ v ∈ T₂.alive)
  /-- outside the difference region the two states have the same edges -/
  adj_iff : ∀ u v : V, u ∉ P.Delta Q s → v ∉ P.Delta Q s →
    (T₁.graph.Adj u v ↔ T₂.graph.Adj u v)
  /-- every live vertex of the difference region is within `2r` of `s` in the first state -/
  delta_bound₁ : ∀ v : V, v ∈ P.Delta Q s → v ∈ T₁.alive →
    T₁.graph.dist s v ≤ 2 * (P.D - P.meetIdx Q)
  /-- every live vertex of the difference region is within `2r` of `s` in the second state -/
  delta_bound₂ : ∀ v : V, v ∈ P.Delta Q s → v ∈ T₂.alive →
    T₂.graph.dist s v ≤ 2 * (P.D - P.meetIdx Q)

/-- **The surviving half of the folded diameter is a geodesic.** -/
theorem foldCone_spine_dist (P : DiamPath S) {k : ℕ} (hk : k ≤ P.D / 2) :
    P.foldGraph.dist (P.seq 0) (P.seq k) = k :=
  dist_eq_of_seq P.foldGraph_isAcyclic (q := fun j => P.seq j) (n := k)
    (fun j hj => P.foldCone_seq_adj j (by omega))
    (fun j _ l _ h => P.foldCone_seq_inj j (by omega) l (by omega) h)

/-- **The common prefix is a geodesic of both folded trees.**  For `2k ≤ D` the vertices
`p 0, …, p k` of the common prefix are alive in `Q.foldState` as well (they are the first `k + 1`
vertices of the `Q`-diameter) and the distance between them is `k` there too. -/
theorem foldCone_spine_dist_Q (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {k : ℕ}
    (hk : k ≤ P.D / 2) :
    Q.foldGraph.dist (P.seq 0) (P.seq k) = k := by
  have h2k : 2 * k ≤ P.D := by omega
  have htail := P.tail_le_meetIdx Q hP hQ
  have hle : k ≤ P.meetIdx Q := by
    have h := P.two_mul_tail_le Q hP hQ
    have := P.meetIdx_le Q
    omega
  have h0 : Q.seq 0 = P.seq 0 := (P.seq_eq_of_le_meetIdx Q hP hQ (by omega)).symm
  have hk' : Q.seq k = P.seq k := (P.seq_eq_of_le_meetIdx Q hP hQ hle).symm
  rw [← h0, ← hk']
  exact Q.foldCone_spine_dist (by have := P.D_eq Q; omega)

end DiamPath

/-! ## 4. The two folded diameters are equal

Splitting the live vertices of the two folded states into the common part `C` and the difference
region `Δ` gives the equality of the diameters as soon as the two folded states have the *same*
distance from `s` on `C`: a vertex of `Δ` is within `2r` of `s`
(`Phase1.dist_le_two_mul_tail_of_mem_Delta`) and `2r` is at most the diameter of either folded state
(`two_mul_tail_le_diam_fold`, `two_mul_tail_le_diam_fold'`), while on `C` the two distance functions
are literally equal.  Two live vertices are then compared with the two of them via the cone
condition of the folded tree (`Cone.dist_le_max`), which is `REF.md` Lemma 3's
`foldCone_height_reachable`. -/

namespace DiamPath

variable {S : TreeState V}

/-- The `Δ`-bound `2r` is at most the diameter of `P.foldState`. -/
theorem two_mul_tail_le_diam_fold (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    2 * (P.D - P.meetIdx Q) ≤ P.foldState.diam := by
  rcases Nat.eq_zero_or_pos (P.D - P.meetIdx Q) with h0 | hpos
  · rw [h0, mul_zero]; exact Nat.zero_le _
  · exact P.two_mul_tail_le_diam Q hP hQ hpos

/-- The `Δ`-bound `2r` is at most the diameter of `Q.foldState`. -/
theorem two_mul_tail_le_diam_fold' (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    2 * (P.D - P.meetIdx Q) ≤ Q.foldState.diam := by
  rcases Nat.eq_zero_or_pos (P.D - P.meetIdx Q) with h0 | hpos
  · rw [h0, mul_zero]; exact Nat.zero_le _
  · have h0' : P.p 0 = Q.p 0 := hP.trans hQ.symm
    have hcomm : Q.D - Q.meetIdx P = P.D - P.meetIdx Q := by
      rw [P.meetIdx_comm Q h0', P.D_eq Q]
    exact P.two_mul_tail_le_diam' Q hP hQ hpos (by omega)

/-- **The two folded diameters are equal.**  It is enough that the two folded states have the same
distance from `s` on the common part `C`. -/
theorem diam_eq_of_dist_eq_on_common (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hdist : ∀ v : V, v ∉ P.Delta Q s → v ∈ P.foldAlive →
      P.foldGraph.dist s v = Q.foldGraph.dist s v) :
    P.foldState.diam = Q.foldState.diam := by
  have h0 : P.p 0 = Q.p 0 := hP.trans hQ.symm
  have hs₁ : s ∈ P.foldAlive := by
    rw [← hP, ← P.seq_zero]; exact P.foldCone_seq_mem (Nat.zero_le _)
  have hs₂ : s ∈ Q.foldAlive := by
    rw [← hQ, ← Q.seq_zero]; exact Q.foldCone_seq_mem (Nat.zero_le _)
  have hreach₁ : ∀ x ∈ P.foldAlive, P.foldGraph.Reachable x (P.seq 0) := fun x hx =>
    (P.foldState.connected (P.seq 0) (P.foldCone_seq_mem (Nat.zero_le _)) x hx).symm
  have hreach₂ : ∀ x ∈ Q.foldAlive, Q.foldGraph.Reachable x (Q.seq 0) := fun x hx =>
    (Q.foldState.connected (Q.seq 0) (Q.foldCone_seq_mem (Nat.zero_le _)) x hx).symm
  -- every live vertex of `P.foldState` is within `Q.foldState.diam` of `s`, and conversely
  have aux : ∀ w ∈ P.foldAlive, P.foldGraph.dist s w ≤ Q.foldState.diam := by
    intro w hw
    by_cases hwΔ : w ∈ P.Delta Q s
    · refine le_trans ?_ (P.two_mul_tail_le_diam_fold' Q hP hQ)
      have h := P.dist_le_two_mul_tail_of_mem_Delta Q hP hQ hwΔ hw
      rwa [P.seq_zero, hP] at h
    · rw [hdist w hwΔ hw]
      exact TreeState.dist_le_diam (S := Q.foldState) hs₂
        ((P.mem_foldAlive_iff_of_not_mem_Delta Q hP hQ hwΔ).mp hw)
  have aux' : ∀ w ∈ Q.foldAlive, Q.foldGraph.dist s w ≤ P.foldState.diam := by
    intro w hw
    by_cases hwΔ : w ∈ P.Delta Q s
    · have hwΔ' : w ∈ Q.Delta P s := by rw [← P.Delta_comm Q s h0]; exact hwΔ
      refine le_trans ?_ (P.two_mul_tail_le_diam_fold Q hP hQ)
      have h := Q.dist_le_two_mul_tail_of_mem_Delta P hQ hP hwΔ' hw
      rw [Q.seq_zero, hQ, ← P.meetIdx_comm Q h0, ← P.D_eq Q] at h
      exact h
    · have hwP : w ∈ P.foldAlive := (P.mem_foldAlive_iff_of_not_mem_Delta Q hP hQ hwΔ).mpr hw
      rw [← hdist w hwΔ hwP]
      exact TreeState.dist_le_diam (S := P.foldState) hs₁ hwP
  refine le_antisymm ?_ ?_
  · rw [TreeState.diam, P.foldState_alive, P.foldState_graph]
    refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
    have hmax := Cone.dist_le_max (H := P.foldGraph) P.foldGraph_isAcyclic
      (m := P.D / 2) (q := P.seq) P.foldCone_seq_adj P.foldCone_seq_inj
      P.foldCone_height_reachable u v (hreach₁ u hu) (hreach₁ v hv)
    rw [P.seq_zero, hP] at hmax
    have h₁ := aux u hu
    have h₂ := aux v hv
    omega
  · rw [TreeState.diam, Q.foldState_alive, Q.foldState_graph]
    refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
    have hmax := Cone.dist_le_max (H := Q.foldGraph) Q.foldGraph_isAcyclic
      (m := Q.D / 2) (q := Q.seq) Q.foldCone_seq_adj Q.foldCone_seq_inj
      Q.foldCone_height_reachable u v (hreach₂ u hu) (hreach₂ v hv)
    rw [Q.seq_zero, hQ] at hmax
    have h₁ := aux' u hu
    have h₂ := aux' v hv
    omega

end DiamPath

/-! ## 5. The invariant of the synchronised phase

`Phase1Inv P Q T₁ T₂ s` is everything that the phase-1 description of `REF.md` §7 hands to the
endgame: `s` is a diameter endpoint of both states, the two states have the same diameter, they agree
on the common part `C = Δᶜ` of the *original* pair of diameters (vertices and edges), and every live
vertex of `Δ` is within `2r` of `s` in either state.  `phase1Inv_fold` shows that a pair of folded
states satisfies it as soon as their diameters agree — the equality proved to follow from
`dist_eq_on_common` in §4. -/

namespace DiamPath

variable {S : TreeState V}

/-- **The pair of folded states satisfies the phase-1 invariant**, once their diameters are known to
be equal.  Everything except the diameter equality is `Phase1.lean`'s §3–§5. -/
theorem phase1Inv_fold (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hdiam : P.foldState.diam = Q.foldState.diam) : Phase1Inv P Q P.foldState Q.foldState s where
  end₁ := by rw [← hP]; exact isDiamEnd_foldState P
  end₂ := by rw [← hQ]; exact isDiamEnd_foldState Q
  diam_eq := hdiam
  mem_iff := fun _ hv => P.mem_foldAlive_iff_of_not_mem_Delta Q hP hQ hv
  adj_iff := fun _ _ hu hv => P.foldGraph_adj_iff_of_not_mem_Delta Q hP hQ hu hv
  delta_bound₁ := fun v hv hvA => by
    have h := P.dist_le_two_mul_tail_of_mem_Delta Q hP hQ hv hvA
    rwa [P.seq_zero, hP] at h
  delta_bound₂ := fun v hv hvA => by
    have h := P.dist_le_two_mul_tail_of_mem_Delta' Q hP hQ hv hvA
    rwa [Q.seq_zero, hQ] at h

/-- **The phase-1 invariant of the folded pair**, from the distance agreement of §4. -/
theorem phase1Inv_fold_of_dist_eq (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (hdist : ∀ v : V, v ∉ P.Delta Q s → v ∈ P.foldAlive →
      P.foldGraph.dist s v = Q.foldGraph.dist s v) :
    Phase1Inv P Q P.foldState Q.foldState s :=
  P.phase1Inv_fold Q hP hQ (P.diam_eq_of_dist_eq_on_common Q hP hQ hdist)

end DiamPath

end OhtoaiTreeProof
