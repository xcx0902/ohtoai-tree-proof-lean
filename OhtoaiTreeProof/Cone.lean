/-
# the projection formula, the cone lemma and `isDiamEnd_foldState`

This file formalises `REF.md` §4 and §5:

* **Stage 1** — the projection formula on a diameter path: for a live vertex `u` whose closest
  diameter vertex is `P.p i`, one has `dist u (P.p k) = dist u (P.p i) + |k - i|`, which is
  `DiamPath.dist_eq_dist_add_abs` below, together with the two special cases
  `DiamPath.dist_proj_zero` (`dist u (P.p 0) = h + i`) and `DiamPath.dist_proj_last`
  (`dist u (P.p P.last) = h + (D - i)`).

* **Stage 2** — **Lemma 2 of `REF.md`**, the *cone lemma*, for an arbitrary acyclic graph `H` with a
  path `q 0, …, q m` such that every vertex hangs above its closest path vertex `q i` at height at
  most `i`: then `q 0` is the endpoint of a diameter.  See `OhtoaiTreeProof.Cone.dist_le_max` (the
  distance form `d x y ≤ max (d (q 0) x) (d (q 0) y)`) and `OhtoaiTreeProof.Cone.exists_dist_eq`
  (the eccentricity form).

* **Stage 3** — **Lemma 3 of `REF.md`**, `OhtoaiTreeProof.isDiamEnd_foldState`: folding along a
  diameter towards the endpoint `P.p 0` keeps `P.p 0` a diameter endpoint.

The only ingredient taken on faith is `DiamPath.foldGraph_isAcyclic` (`Basic.lean`), the acyclicity
of the folded graph, which is proved elsewhere.

The auxiliary declarations of Stage 3 are prefixed `foldCone_` to keep them apart from the folding
lemmas that live in `Basic.lean`.
-/
import OhtoaiTreeProof.Diameter

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Stage 1: the projection formula on a diameter -/

namespace DiamPath

variable {S : TreeState V} (P : DiamPath S)

/-- **Stage 1, projection formula.**  If `P.p i` is a closest vertex of the diameter `P` to the
live vertex `u`, then the distance from `u` to `P.p k` is the distance to `P.p i` plus the index
distance `|k - i|` (written as `(k - i) + (i - k)`). -/
theorem dist_eq_dist_add_abs {u : V} (hu : u ∈ S.alive) (i : Fin (P.D + 1))
    (hmin : ∀ j : Fin (P.D + 1), S.graph.dist u (P.p i) ≤ S.graph.dist u (P.p j))
    (k : Fin (P.D + 1)) :
    S.graph.dist u (P.p k) =
      S.graph.dist u (P.p i) + (((k : ℕ) - (i : ℕ)) + ((i : ℕ) - (k : ℕ))) := by
  rcases le_total (i : ℕ) (k : ℕ) with h | h
  · rw [(P.dist_eq_dist_add hu i hmin).1 k h, Nat.sub_eq_zero_of_le h, add_zero]
  · rw [(P.dist_eq_dist_add hu i hmin).2 k h, Nat.sub_eq_zero_of_le h, zero_add]

/-- **Stage 1, special case at the beginning.**  `dist u (P.p 0) = h + i` where `h` is the distance
from `u` to its closest point `P.p i` of the diameter. -/
theorem dist_proj_zero {u : V} (hu : u ∈ S.alive) {i : Fin (P.D + 1)}
    (hmin : ∀ j : Fin (P.D + 1), S.graph.dist u (P.p i) ≤ S.graph.dist u (P.p j)) :
    S.graph.dist u (P.p 0) = S.graph.dist u (P.p i) + (i : ℕ) := by
  simpa using (P.dist_eq_dist_add hu i hmin).2 0 (Nat.zero_le _)

/-- **Stage 1, special case at the end.**  `dist u (P.p P.last) = h + (D - i)`. -/
theorem dist_proj_last {u : V} (hu : u ∈ S.alive) {i : Fin (P.D + 1)}
    (hmin : ∀ j : Fin (P.D + 1), S.graph.dist u (P.p i) ≤ S.graph.dist u (P.p j)) :
    S.graph.dist u (P.p P.last) = S.graph.dist u (P.p i) + (P.D - (i : ℕ)) := by
  simpa [DiamPath.val_last] using (P.dist_eq_dist_add hu i hmin).1 P.last (P.val_le_last i)

/-- Every vertex has a closest vertex on the diameter. -/
theorem exists_closest_index (u : V) :
    ∃ i : Fin (P.D + 1), ∀ j : Fin (P.D + 1), S.graph.dist u (P.p i) ≤ S.graph.dist u (P.p j) :=
  Finite.exists_min _

/-- **Stage 1, collected form.**  A closest point `P.p i` of the diameter to a live vertex `u`
satisfies the projection formula at every `k`, the two endpoint formulae, and the branch height
bound `dist u (P.p i) ≤ min i (D - i)` of Lemma 1. -/
theorem dist_proj {u : V} (hu : u ∈ S.alive) {i : Fin (P.D + 1)}
    (hmin : ∀ j : Fin (P.D + 1), S.graph.dist u (P.p i) ≤ S.graph.dist u (P.p j)) :
    (∀ k : Fin (P.D + 1), S.graph.dist u (P.p k) =
        S.graph.dist u (P.p i) + (((k : ℕ) - (i : ℕ)) + ((i : ℕ) - (k : ℕ)))) ∧
      S.graph.dist u (P.p 0) = S.graph.dist u (P.p i) + (i : ℕ) ∧
      S.graph.dist u (P.p P.last) = S.graph.dist u (P.p i) + (P.D - (i : ℕ)) ∧
      S.graph.dist u (P.p i) ≤ min (i : ℕ) (P.D - (i : ℕ)) :=
  ⟨fun k => P.dist_eq_dist_add_abs hu i hmin k, P.dist_proj_zero hu hmin,
    P.dist_proj_last hu hmin, dist_le_min_index P hu hmin⟩

end DiamPath

/-! ## Stage 2: the cone lemma (REF.md Lemma 2) -/

namespace Cone

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The vertices `q 0, …, q m` of the path are all reachable from `q 0`. -/
theorem reachable_zero {H : SimpleGraph W} {m : ℕ} {q : ℕ → W}
    (hadj : ∀ k < m, H.Adj (q k) (q (k + 1))) :
    ∀ k ≤ m, H.Reachable (q 0) (q k) := by
  intro k hk
  induction k with
  | zero => exact Reachable.rfl
  | succ k ih => exact (ih (by omega)).trans (hadj k (by omega)).reachable

/-- The vertices of the path `q 0, …, q m` are mutually reachable. -/
theorem reachable {H : SimpleGraph W} {m : ℕ} {q : ℕ → W}
    (hadj : ∀ k < m, H.Adj (q k) (q (k + 1))) (k : ℕ) (hk : k ≤ m) (l : ℕ) (hl : l ≤ m) :
    H.Reachable (q k) (q l) :=
  ((reachable_zero hadj k hk).symm).trans (reachable_zero hadj l hl)

/-- Distances along the path: `d (q i) (q j) ≤ |i - j|`. -/
theorem path_dist_le {H : SimpleGraph W} (hH : H.IsAcyclic) {m : ℕ} {q : ℕ → W}
    (hadj : ∀ k < m, H.Adj (q k) (q (k + 1)))
    (hinj : ∀ k ≤ m, ∀ l ≤ m, q k = q l → k = l) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m) :
    H.dist (q i) (q j) ≤ (j - i) + (i - j) := by
  have hreach : ∀ k ≤ m, H.Reachable (q i) (q k) := fun k hk => reachable hadj i hi k hk
  have hmin : ∀ j' ≤ m, H.dist (q i) (q i) ≤ H.dist (q i) (q j') := fun j' _ => by
    rw [dist_self]; exact Nat.zero_le _
  rcases le_total i j with h | h
  · rw [dist_eq_dist_add_of_le hH hadj hreach hinj hmin j h hj, dist_self, Nat.zero_add]
    omega
  · rw [dist_eq_dist_add_of_ge hH hadj hreach hinj hi hmin j h, dist_self, Nat.zero_add]
    omega

/-- Projection formula along the path: if `q i` is a closest vertex of the path to `x`, then
`d x (q j) = d x (q i) + |i - j|` for every `j ≤ m`. -/
theorem dist_proj {H : SimpleGraph W} (hH : H.IsAcyclic) {m : ℕ} {q : ℕ → W}
    (hadj : ∀ k < m, H.Adj (q k) (q (k + 1)))
    (hinj : ∀ k ≤ m, ∀ l ≤ m, q k = q l → k = l) {x : W} {i : ℕ} (him : i ≤ m)
    (hmin : ∀ j ≤ m, H.dist x (q i) ≤ H.dist x (q j))
    (hreach : ∀ k ≤ m, H.Reachable x (q k)) (j : ℕ) (hj : j ≤ m) :
    H.dist x (q j) = H.dist x (q i) + ((j - i) + (i - j)) := by
  rcases le_total i j with h | h
  · rw [dist_eq_dist_add_of_le hH hadj hreach hinj hmin j h hj, Nat.sub_eq_zero_of_le h, add_zero]
  · rw [dist_eq_dist_add_of_ge hH hadj hreach hinj him hmin j h, Nat.sub_eq_zero_of_le h, zero_add]

/-- **Lemma 2 of `REF.md` (cone lemma), distance form.**  Let `H` be a tree (acyclic) containing a
path `q 0, …, q m`, and suppose that every vertex `x` has a closest path vertex `q i` at distance at
most `i` (the "branch heights are at most the distance to `q 0`" condition).  Then for all `x`, `y`
reachable from `q 0`,
`d x y ≤ max (d (q 0) x) (d (q 0) y)`.

Consequently the eccentricity of `q 0` is the diameter of the tree, see `exists_dist_eq`. -/
theorem dist_le_max {H : SimpleGraph W} (hH : H.IsAcyclic) {m : ℕ} {q : ℕ → W}
    (hadj : ∀ k < m, H.Adj (q k) (q (k + 1)))
    (hinj : ∀ k ≤ m, ∀ l ≤ m, q k = q l → k = l)
    (hcone : ∀ x : W, H.Reachable x (q 0) → ∃ i ≤ m,
      (∀ j ≤ m, H.dist x (q i) ≤ H.dist x (q j)) ∧ H.dist x (q i) ≤ i) :
    ∀ x y : W, H.Reachable x (q 0) → H.Reachable y (q 0) →
      H.dist x y ≤ max (H.dist (q 0) x) (H.dist (q 0) y) := by
  intro x y hx hy
  obtain ⟨i, him, hmini, hci⟩ := hcone x hx
  obtain ⟨j, hjm, hminj, hcj⟩ := hcone y hy
  have hq := reachable_zero hadj
  have hxq : ∀ k ≤ m, H.Reachable x (q k) := fun k hk => hx.trans (hq k hk)
  have hyq : ∀ k ≤ m, H.Reachable y (q k) := fun k hk => hy.trans (hq k hk)
  -- distances from `q 0` to `x` and to `y`, computed from the projection formula
  have hxi : H.dist x (q 0) = H.dist x (q i) + i := by
    simpa using dist_eq_dist_add_of_ge hH hadj hxq hinj him hmini 0 (Nat.zero_le _)
  have hyj : H.dist y (q 0) = H.dist y (q j) + j := by
    simpa using dist_eq_dist_add_of_ge hH hadj hyq hinj hjm hminj 0 (Nat.zero_le _)
  -- the geodesic from `x` to `y` passes through `q i` and `q j`
  have htri : H.dist x y ≤ H.dist x (q i) + H.dist (q i) (q j) + H.dist y (q j) := by
    have h1 : H.dist x y ≤ H.dist x (q i) + H.dist (q i) y := (hxq i him).dist_triangle_left y
    have h2 : H.dist (q i) y ≤ H.dist (q i) (q j) + H.dist (q j) y :=
      (reachable hadj i him j hjm).dist_triangle_left y
    have h3 : H.dist (q j) y = H.dist y (q j) := dist_comm
    omega
  have hpath := path_dist_le hH hadj hinj him hjm
  rcases le_total i j with hij | hji
  · have : H.dist x y ≤ H.dist y (q 0) := by
      rw [hyj]
      omega
    calc H.dist x y ≤ H.dist y (q 0) := this
      _ = H.dist (q 0) y := dist_comm
      _ ≤ max (H.dist (q 0) x) (H.dist (q 0) y) := le_max_right _ _
  · have : H.dist x y ≤ H.dist x (q 0) := by
      rw [hxi]
      omega
    calc H.dist x y ≤ H.dist x (q 0) := this
      _ = H.dist (q 0) x := dist_comm
      _ ≤ max (H.dist (q 0) x) (H.dist (q 0) y) := le_max_left _ _

/-- **Lemma 2 of `REF.md` (cone lemma), `Fin`-indexed form.**  This is `Cone.dist_le_max` with the
path `q 0, …, q m` indexed by `Fin (m + 1)`, as in the statement of `REF.md`. -/
theorem dist_le_max_fin {H : SimpleGraph W} (hH : H.IsAcyclic) {m : ℕ} {q : Fin (m + 1) → W}
    (hadj : ∀ i : Fin m, H.Adj (q i.castSucc) (q i.succ)) (hinj : Function.Injective q)
    (hcone : ∀ x : W, H.Reachable x (q 0) → ∃ i : Fin (m + 1),
      (∀ j : Fin (m + 1), H.dist x (q i) ≤ H.dist x (q j)) ∧ H.dist x (q i) ≤ (i : ℕ)) :
    ∀ x y : W, H.Reachable x (q 0) → H.Reachable y (q 0) →
      H.dist x y ≤ max (H.dist (q 0) x) (H.dist (q 0) y) := by
  let q' : ℕ → W := fun k => q ⟨min k m, Nat.lt_succ_of_le (min_le_right k m)⟩
  have hq' : ∀ k (hk : k ≤ m), q' k = q ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k hk
    simp only [q']
    exact congrArg q (Fin.ext (by simp [Nat.min_eq_left hk]))
  have h0 : q' 0 = q 0 := hq' 0 (Nat.zero_le m)
  have hadj' : ∀ k < m, H.Adj (q' k) (q' (k + 1)) := by
    intro k hk
    rw [hq' k (by omega), hq' (k + 1) (by omega)]
    exact hadj ⟨k, hk⟩
  have hinj' : ∀ k ≤ m, ∀ l ≤ m, q' k = q' l → k = l := by
    intro k hk l hl h
    rw [hq' k hk, hq' l hl] at h
    exact Fin.ext_iff.mp (hinj h)
  have hcone' : ∀ x : W, H.Reachable x (q' 0) → ∃ i ≤ m,
      (∀ j ≤ m, H.dist x (q' i) ≤ H.dist x (q' j)) ∧ H.dist x (q' i) ≤ i := by
    intro x hx
    rw [h0] at hx
    obtain ⟨i, himin, hle⟩ := hcone x hx
    refine ⟨(i : ℕ), by have := i.isLt; omega, fun j hj => ?_, ?_⟩
    · rw [hq' (i : ℕ) (by have := i.isLt; omega), hq' j hj]
      exact himin ⟨j, by omega⟩
    · rw [hq' (i : ℕ) (by have := i.isLt; omega)]
      exact hle
  intro x y hx hy
  rw [← h0] at hx hy ⊢
  exact dist_le_max hH hadj' hinj' hcone' x y hx hy

/-- **Lemma 2 of `REF.md` (cone lemma), eccentricity form.**  Under the hypotheses of
`Cone.dist_le_max`, if `Δ` bounds all distances between vertices reachable from `q 0` and is
attained, then `Δ` is attained from `q 0`: the eccentricity of `q 0` is the diameter. -/
theorem exists_dist_eq {H : SimpleGraph W} (hH : H.IsAcyclic) {m : ℕ} {q : ℕ → W}
    (hadj : ∀ k < m, H.Adj (q k) (q (k + 1)))
    (hinj : ∀ k ≤ m, ∀ l ≤ m, q k = q l → k = l)
    (hcone : ∀ x : W, H.Reachable x (q 0) → ∃ i ≤ m,
      (∀ j ≤ m, H.dist x (q i) ≤ H.dist x (q j)) ∧ H.dist x (q i) ≤ i)
    {Δ : ℕ} (hdiam : ∀ x y : W, H.Reachable x (q 0) → H.Reachable y (q 0) → H.dist x y ≤ Δ)
    (hatt : ∃ x : W, H.Reachable x (q 0) ∧ ∃ y : W, H.Reachable y (q 0) ∧ H.dist x y = Δ) :
    ∃ y : W, H.Reachable y (q 0) ∧ H.dist (q 0) y = Δ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hatt
  have hmax := dist_le_max hH hadj hinj hcone x y hx hy
  have hxΔ : H.dist (q 0) x ≤ Δ := by
    rw [dist_comm]; exact hdiam x (q 0) hx Reachable.rfl
  have hyΔ : H.dist (q 0) y ≤ Δ := by
    rw [dist_comm]; exact hdiam y (q 0) hy Reachable.rfl
  have hmaxeq : max (H.dist (q 0) x) (H.dist (q 0) y) = Δ := by
    refine le_antisymm (max_le hxΔ hyΔ) ?_
    rw [← hxy]
    exact hmax
  rcases max_cases (H.dist (q 0) x) (H.dist (q 0) y) with ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨x, hx, h.symm.trans hmaxeq⟩
  · exact ⟨y, hy, h.symm.trans hmaxeq⟩

end Cone

/-! ## Stage 3: folding towards a diameter endpoint (REF.md Lemma 3) -/

namespace DiamPath

variable {S : TreeState V} (P : DiamPath S)

/-! ### Folding does not increase distances -/

/-- An edge of the tree is mapped by the folding map to a walk of length at most one. -/
theorem foldCone_walk_of_adj {a b : V} (h : S.graph.Adj a b) :
    ∃ w : P.foldGraph.Walk (P.rep a) (P.rep b), w.length ≤ 1 := by
  rcases eq_or_ne (P.rep a) (P.rep b) with heq | hne
  · exact ⟨SimpleGraph.Walk.nil.copy heq.symm rfl, by simp⟩
  · exact ⟨SimpleGraph.Walk.cons ⟨hne, P.rep_mem_foldAlive (S.adj_alive h).1,
      P.rep_mem_foldAlive (S.adj_alive h).2, a, b, h, rfl, rfl⟩ SimpleGraph.Walk.nil, le_rfl⟩

/-- A walk of the tree is mapped by the folding map to a walk of the folded tree of no greater
length. -/
theorem foldCone_walk_le {a b : V} (w : S.graph.Walk a b) :
    ∃ w' : P.foldGraph.Walk (P.rep a) (P.rep b), w'.length ≤ w.length := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | cons hadj rest ih =>
      obtain ⟨u, hu⟩ := P.foldCone_walk_of_adj hadj
      obtain ⟨w', hw'⟩ := ih
      refine ⟨u.append w', ?_⟩
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
      omega

/-! ### Which vertices of the ambient type lie in the folded tree -/

/-- A vertex reachable from a vertex of the folded tree is itself a vertex of the folded tree. -/
theorem foldCone_alive_of_reachable {u v : V} (h : P.foldGraph.Reachable u v) :
    v ∈ P.foldAlive → u ∈ P.foldAlive := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons hadj rest ih => exact fun _ => (P.foldGraph_adj_subset hadj).1

/-- Two reachable vertices of the folded graph are live or not simultaneously. -/
theorem foldCone_alive_iff {u v : V} (h : P.foldGraph.Reachable u v) :
    u ∈ P.foldAlive ↔ v ∈ P.foldAlive :=
  ⟨fun hu => P.foldCone_alive_of_reachable h.symm hu, fun hv => P.foldCone_alive_of_reachable h hv⟩

/-- A reachable vertex of the folded graph which is not live is the other endpoint. -/
theorem foldCone_eq_of_not_mem {u v : V} (h : P.foldGraph.Reachable u v) :
    u ∉ P.foldAlive → u = v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact fun _ => rfl
  | cons hadj rest ih => exact fun hu => absurd (P.foldGraph_adj_subset hadj).1 hu

/-- **Folding does not increase distances.**  The folded distance of the representatives of two
vertices is at most their distance in the original tree. -/
theorem foldCone_dist_le (a b : V) :
    P.foldGraph.dist (P.rep a) (P.rep b) ≤ S.graph.dist a b := by
  by_cases h : S.graph.Reachable a b
  · obtain ⟨w, hw⟩ := h.exists_walk_length_eq_dist
    obtain ⟨w', hw'⟩ := P.foldCone_walk_le w
    calc P.foldGraph.dist (P.rep a) (P.rep b) ≤ w'.length := SimpleGraph.dist_le w'
      _ ≤ w.length := hw'
      _ = S.graph.dist a b := hw
  · rw [SimpleGraph.dist_eq_zero_of_not_reachable h, Nat.le_zero,
      SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
    by_cases hab : P.rep a = P.rep b
    · exact Or.inl hab
    · refine Or.inr fun hr => h ?_
      have ha : P.rep a ∈ P.foldAlive := by
        by_contra hcon
        exact hab (P.foldCone_eq_of_not_mem hr hcon)
      have hb : P.rep b ∈ P.foldAlive := by
        by_contra hcon
        exact hab (P.foldCone_eq_of_not_mem hr.symm hcon).symm
      exact S.connected a (P.rep_mem_iff.mp (P.foldAlive_subset ha)) b
        (P.rep_mem_iff.mp (P.foldAlive_subset hb))

/-! ### The half of the diameter that survives the folding -/

/-- The first half `q 0, …, q m` of the diameter, `m = D / 2`, is a path of the folded tree. -/
theorem foldCone_seq_mem {j : ℕ} (hj : j ≤ P.D / 2) : P.seq j ∈ P.foldAlive := by
  have h2 : 2 * j ≤ P.D := by omega
  rw [P.seq_eq (by omega)]
  exact P.path_mem_foldAlive.mpr (by simpa using h2)

theorem foldCone_seq_rep {j : ℕ} (hj : j ≤ P.D / 2) : P.rep (P.seq j) = P.seq j :=
  (P.mem_foldAlive.mp (P.foldCone_seq_mem hj)).2

theorem foldCone_seq_adj : ∀ k < P.D / 2, P.foldGraph.Adj (P.seq k) (P.seq (k + 1)) := by
  intro k hk
  have hne : P.seq k ≠ P.seq (k + 1) := by
    intro h
    have := P.seq_inj k (show k ≤ P.D by omega) (k + 1) (show k + 1 ≤ P.D by omega) h
    omega
  exact ⟨hne, P.foldCone_seq_mem (by omega), P.foldCone_seq_mem (by omega), P.seq k, P.seq (k + 1),
    P.seq_adj k (by omega), P.foldCone_seq_rep (by omega), P.foldCone_seq_rep (by omega)⟩

theorem foldCone_seq_inj : ∀ k ≤ P.D / 2, ∀ l ≤ P.D / 2, P.seq k = P.seq l → k = l :=
  fun k hk l hl h => P.seq_inj k (show k ≤ P.D by omega) l (show l ≤ P.D by omega) h

/-- The representative of a diameter vertex is a vertex of the surviving half-path. -/
theorem foldCone_rep_path_eq_seq (i : Fin (P.D + 1)) :
    P.rep (P.p i) = P.seq (min (i : ℕ) (P.D - (i : ℕ))) := by
  rw [P.rep_path, P.seq_eq (show min (i : ℕ) (P.D - (i : ℕ)) ≤ P.D by omega)]

/-- The folded index of a diameter vertex lies in the surviving half. -/
theorem foldCone_min_sub_le_half (n : ℕ) : min n (P.D - n) ≤ P.D / 2 := by omega

/-! ### The cone condition of the folded tree -/

/-- **REF.md §5.**  Every vertex `x` of the folded tree has a closest vertex `P.seq i` of the
surviving half-path at distance at most `i`: the branch heights of the folded tree are bounded by
the distance to the folded endpoint. -/
theorem foldCone_height (x : V) (hx : x ∈ P.foldAlive) :
    ∃ i ≤ P.D / 2,
      (∀ j ≤ P.D / 2, P.foldGraph.dist x (P.seq i) ≤ P.foldGraph.dist x (P.seq j)) ∧
        P.foldGraph.dist x (P.seq i) ≤ i := by
  -- the closest vertex of the diameter to `x` in the original tree
  obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i : Fin (P.D + 1) => S.graph.dist x (P.p i))
  set i' := min (i0 : ℕ) (P.D - (i0 : ℕ)) with hi'def
  have hi'half : i' ≤ P.D / 2 := P.foldCone_min_sub_le_half i0
  -- Lemma 1: the height of `x` above `P.p i0` is at most `i'`
  have hheight : S.graph.dist x (P.p i0) ≤ i' :=
    dist_le_min_index P (P.foldAlive_subset hx) hi0
  -- the folded distance to `P.seq i'` is at most that height
  have hub : P.foldGraph.dist x (P.seq i') ≤ S.graph.dist x (P.p i0) := by
    have h := P.foldCone_dist_le x (P.p i0)
    rwa [P.foldCone_rep_path_eq_seq i0, (P.mem_foldAlive.mp hx).2] at h
  -- the closest vertex of the half-path to `x` in the folded tree
  obtain ⟨i, hi⟩ := Finite.exists_min (fun j : Fin (P.D / 2 + 1) =>
    P.foldGraph.dist x (P.seq (j : ℕ)))
  have hile : (i : ℕ) ≤ P.D / 2 := by have := i.isLt; omega
  have hreach : ∀ k ≤ P.D / 2, P.foldGraph.Reachable x (P.seq k) := by
    intro k hk
    have h := P.fold_reachable (S.connected x (P.foldAlive_subset hx) (P.seq k)
      (P.foldAlive_subset (P.foldCone_seq_mem hk)))
    rwa [(P.mem_foldAlive.mp hx).2, P.foldCone_seq_rep hk] at h
  -- the projection formula of the folded tree at `j = i'`
  have hproj : P.foldGraph.dist x (P.seq i') =
      P.foldGraph.dist x (P.seq (i : ℕ)) + ((i' - (i : ℕ)) + ((i : ℕ) - i')) :=
    Cone.dist_proj (H := P.foldGraph) (m := P.D / 2) (q := P.seq) P.foldGraph_isAcyclic
      P.foldCone_seq_adj P.foldCone_seq_inj hile (fun j hj => hi ⟨j, by omega⟩) hreach i' hi'half
  have hkey : P.foldGraph.dist x (P.seq (i : ℕ)) + ((i' - (i : ℕ)) + ((i : ℕ) - i')) ≤ i' := by
    rw [← hproj]
    exact le_trans hub hheight
  refine ⟨(i : ℕ), hile, fun j hj => hi ⟨j, by omega⟩, ?_⟩
  rcases le_total (i : ℕ) i' with h | h <;> omega

/-- The cone condition, stated for the vertices reachable from the folded endpoint. -/
theorem foldCone_height_reachable (x : V) (hx : P.foldGraph.Reachable x (P.seq 0)) :
    ∃ i ≤ P.D / 2,
      (∀ j ≤ P.D / 2, P.foldGraph.dist x (P.seq i) ≤ P.foldGraph.dist x (P.seq j)) ∧
        P.foldGraph.dist x (P.seq i) ≤ i :=
  P.foldCone_height x (P.foldCone_alive_of_reachable hx (P.foldCone_seq_mem (Nat.zero_le _)))

end DiamPath

/-- **REF.md Lemma 3 (§5).**  Folding along a diameter towards the endpoint `P.p 0` keeps `P.p 0` a
diameter endpoint of the folded tree.

The proof is `REF.md`'s: the surviving half `q 0, …, q m` (`m = D / 2`) of the diameter is a path of
the folded tree, every vertex of the folded tree hangs above its closest `q i` at height at most `i`
(this is where Lemma 1 and "folding does not increase distances" are used), and the cone lemma
(`Cone.exists_dist_eq`) then shows that the eccentricity of `q 0 = P.p 0` is the diameter. -/
theorem isDiamEnd_foldState {S : TreeState V} (P : DiamPath S) :
    IsDiamEnd P.foldState (P.p 0) := by
  have hmem : P.seq 0 ∈ P.foldAlive := P.foldCone_seq_mem (Nat.zero_le _)
  obtain ⟨y, hyr, hyd⟩ := Cone.exists_dist_eq (H := P.foldGraph) (m := P.D / 2) (q := P.seq)
    P.foldGraph_isAcyclic P.foldCone_seq_adj P.foldCone_seq_inj P.foldCone_height_reachable
    (Δ := P.foldState.diam)
    (fun x y hx hy => P.foldState.dist_le_diam (P.foldCone_alive_of_reachable hx hmem)
      (P.foldCone_alive_of_reachable hy hmem))
    (by
      obtain ⟨u, hu, v, hv, huv⟩ := P.foldState.exists_dist_eq_diam ⟨P.seq 0, hmem⟩
      exact ⟨u, P.foldState.connected u hu (P.seq 0) hmem, v,
        P.foldState.connected v hv (P.seq 0) hmem, huv⟩)
  refine ⟨?_, y, P.foldCone_alive_of_reachable hyr hmem, ?_⟩
  · rw [← P.seq_val (0 : Fin (P.D + 1))]
    exact hmem
  · rw [← P.seq_val (0 : Fin (P.D + 1))]
    exact hyd

end OhtoaiTreeProof
