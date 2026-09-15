/-
# Scratch: the diameter lemmas of `REF.md` §3 and §9

This file contains `sorry`-free proofs of

* `dist_le_min_index` (REF.md §3, Lemma 1): a branch hanging off the diameter at `p i` has height
  at most `min i (D - i)`;
* `dist_le_max_dist_ends` (REF.md §9, Lemma 6): for a diameter with endpoints `p 0` and `p D`, the
  eccentricity of any vertex is realised by one of the two endpoints.

Everything rests on the fact that a state is a *tree*: `S.acyclic` together with the connectivity
`S.connected` on `alive`.

The two distance lemmas about acyclic graphs that we use are

* `dist_eq_add_of_mem_support`: a vertex on a shortest walk splits distances additively;
* `not_dist_eq_of_adj_adj`: two distinct neighbours `x`, `z` of `y` which are equidistant from `u`
  force `y` to be *closer* to `u` than they are (otherwise a cycle appears).

The second one drives the "no zigzag" induction of `dist_eq_dist_add_of_le` /
`dist_eq_dist_add_of_ge`, which computes the distance from `u` to every vertex of the diameter when
`u`'s closest point on the diameter is known.
-/
import OhtoaiTreeProof.Basic
import Mathlib.Data.Fintype.Lattice

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Distances in an acyclic graph -/

/-- If `w` lies on a walk `p` from `u` to `v` that realises `dist u v`, then `w` splits that
distance additively. -/
theorem dist_eq_add_of_mem_support {G : SimpleGraph V} {u v w : V} {p : G.Walk u v}
    (hp : p.length = G.dist u v) (hw : w ∈ p.support) :
    G.dist u v = G.dist u w + G.dist w v := by
  obtain ⟨q, r, hqr⟩ := (Walk.mem_support_iff_exists_append (p := p)).mp hw
  have hq : q.length = G.dist u w :=
    length_eq_dist_of_subwalk hp (Walk.isSubwalk_of_append_left hqr)
  have hr : r.length = G.dist w v :=
    length_eq_dist_of_subwalk hp (Walk.isSubwalk_of_append_right hqr)
  rw [← hp, hqr, Walk.length_append, hq, hr]

/-- **No zigzag.**  In a tree, if `x` and `z` are two distinct neighbours of `y` which are at the
same distance from `u`, then `y` cannot be *farther* from `u` than they are: the geodesics from `u`
to `x` and to `z` would together with the edges `x–y–z` produce a cycle. -/
theorem not_dist_eq_of_adj_adj {G : SimpleGraph V} (hG : G.IsAcyclic) {u x y z : V}
    (hx : G.Reachable u x) (hy : G.Reachable u y) (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hxz : x ≠ z) (hd : G.dist u x = G.dist u z) (hdy : G.dist u y = G.dist u x + 1) : False := by
  have hz : G.Reachable u z := hy.trans hyz.reachable
  have hdistyx : G.dist y x = 1 := dist_eq_one_iff_adj.mpr hxy.symm
  have hdistyz : G.dist y z = 1 := dist_eq_one_iff_adj.mpr hyz
  have hdistzy : G.dist z y = 1 := dist_eq_one_iff_adj.mpr hyz.symm
  have hdistxy : G.dist x y = 1 := dist_eq_one_iff_adj.mpr hxy
  have hpos : 0 < G.dist x z := (hx.symm.trans hz).pos_dist_of_ne hxz
  have hzpos : 0 < G.dist z x := by rw [dist_comm]; exact hpos
  obtain ⟨γ, hγp, hγl⟩ := hy.exists_path_of_dist
  obtain ⟨γx, hγxp, hγxl⟩ := hx.exists_path_of_dist
  obtain ⟨γz, hγzp, hγzl⟩ := hz.exists_path_of_dist
  -- `y` is on neither of the geodesics from `u` to `x`, `z`
  have hyγx : y ∉ γx.support := by
    intro hmem
    have h := dist_eq_add_of_mem_support hγxl hmem
    rw [hdistyx] at h
    omega
  have hyγz : y ∉ γz.support := by
    intro hmem
    have h := dist_eq_add_of_mem_support hγzl hmem
    rw [hdistyz, ← hd] at h
    omega
  -- hence `x` and `z` both lie on the geodesic from `u` to `y`
  have hxmem : x ∈ γ.support :=
    hG.mem_support_of_ne_mem_support_of_adj_of_isPath hγp hγxp hxy.symm hyγx
  have hzmem : z ∈ γ.support :=
    hG.mem_support_of_ne_mem_support_of_adj_of_isPath hγp hγzp hyz hyγz
  -- split that geodesic at `z`
  obtain ⟨A, B, _, _, hAB⟩ := (hγp.mem_support_iff_exists_append (w := z)).mp hzmem
  have hAl : A.length = G.dist u z :=
    length_eq_dist_of_subwalk hγl (Walk.isSubwalk_of_append_left hAB)
  have hBl : B.length = G.dist z y :=
    length_eq_dist_of_subwalk hγl (Walk.isSubwalk_of_append_right hAB)
  rw [hAB, Walk.mem_support_append_iff] at hxmem
  rcases hxmem with hxA | hxB
  · have h := dist_eq_add_of_mem_support hAl hxA
    rw [hd] at h
    omega
  · have h := dist_eq_add_of_mem_support hBl hxB
    rw [hdistzy, hdistxy] at h
    omega

/-- Walking away from a closest point of a path: distances to `u` grow by one at each step. -/
theorem dist_eq_dist_add_of_le {G : SimpleGraph V} (hG : G.IsAcyclic) {u : V} {n : ℕ} {p : ℕ → V}
    (hadj : ∀ k < n, G.Adj (p k) (p (k + 1))) (hreach : ∀ k ≤ n, G.Reachable u (p k))
    (hinj : ∀ k ≤ n, ∀ l ≤ n, p k = p l → k = l)
    {i : ℕ} (hmin : ∀ j ≤ n, G.dist u (p i) ≤ G.dist u (p j))
    (k : ℕ) (hik : i ≤ k) (hkn : k ≤ n) :
    G.dist u (p k) = G.dist u (p i) + (k - i) := by
  revert hik hkn
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hik hkn
    rcases eq_or_lt_of_le hik with hk | hk
    · subst hk
      simp
    · have hkm1lt : k - 1 < n := by omega
      have hkm1i : i ≤ k - 1 := by omega
      have hkm1n : k - 1 ≤ n := by omega
      have hIH1 := ih (k - 1) (by omega) hkm1i hkm1n
      have hedge := hG.dist_eq_dist_add_one_of_adj_of_reachable u
        (hadj (k - 1) hkm1lt) (hreach (k - 1) hkm1n)
      rw [show k - 1 + 1 = k by omega] at hedge
      rcases hedge with hdown | hup
      · -- the step from `k - 1` to `k` moves towards `u`
        rcases eq_or_lt_of_le hkm1i with heq | hlt
        · -- `k = i + 1`, contradicting minimality of `i`
          have := hmin k hkn
          omega
        · -- otherwise the three vertices `k - 2, k - 1, k` form a zigzag
          have hkm2lt : k - 2 < n := by omega
          have hkm2i : i ≤ k - 2 := by omega
          have hkm2n : k - 2 ≤ n := by omega
          have hIH2 := ih (k - 2) (by omega) hkm2i hkm2n
          have hxy : G.Adj (p (k - 2)) (p (k - 1)) := by
            have h := hadj (k - 2) hkm2lt
            rwa [show k - 2 + 1 = k - 1 by omega] at h
          have hyz : G.Adj (p (k - 1)) (p k) := by
            have h := hadj (k - 1) hkm1lt
            rwa [show k - 1 + 1 = k by omega] at h
          have hxz : p (k - 2) ≠ p k := by
            intro h
            have := hinj (k - 2) (by omega) k hkn h
            omega
          have hd : G.dist u (p (k - 2)) = G.dist u (p k) := by omega
          have hdy : G.dist u (p (k - 1)) = G.dist u (p (k - 2)) + 1 := by omega
          exact (not_dist_eq_of_adj_adj hG (hreach (k - 2) hkm2n) (hreach (k - 1) hkm1n)
            hxy hyz hxz hd hdy).elim
      · omega

/-- Walking towards the beginning of the path from a closest point: distances to `u` also grow by
one at each step.  This is the previous lemma applied to the reversed path. -/
theorem dist_eq_dist_add_of_ge {G : SimpleGraph V} (hG : G.IsAcyclic) {u : V} {n : ℕ} {p : ℕ → V}
    (hadj : ∀ k < n, G.Adj (p k) (p (k + 1))) (hreach : ∀ k ≤ n, G.Reachable u (p k))
    (hinj : ∀ k ≤ n, ∀ l ≤ n, p k = p l → k = l)
    {i : ℕ} (hi : i ≤ n) (hmin : ∀ j ≤ n, G.dist u (p i) ≤ G.dist u (p j))
    (k : ℕ) (hki : k ≤ i) :
    G.dist u (p k) = G.dist u (p i) + (i - k) := by
  have h := dist_eq_dist_add_of_le (G := G) (hG := hG) (u := u) (n := n) (p := fun m => p (n - m))
    (i := n - i)
    (hadj := fun m _ => by
      have h1 : G.Adj (p (n - m - 1)) (p (n - m - 1 + 1)) := hadj (n - m - 1) (by omega)
      rw [show n - m - 1 + 1 = n - m by omega] at h1
      rw [show n - (m + 1) = n - m - 1 by omega]
      exact h1.symm)
    (hreach := fun m _ => hreach (n - m) (by omega))
    (hinj := fun m _ l _ hml => by
      have h2 := hinj (n - m) (by omega) (n - l) (by omega) hml
      omega)
    (hmin := fun j _ => by
      rw [show n - (n - i) = i by omega]
      exact hmin (n - j) (by omega))
    (k := n - k) (by omega) (by omega)
  rwa [show n - (n - k) = k by omega, show n - (n - i) = i by omega,
    show (n - k) - (n - i) = i - k by omega] at h

/-! ## The diameter path, re-indexed by `ℕ` -/

namespace DiamPath

variable {S : TreeState V} (P : DiamPath S)

/-- The diameter path as a sequence indexed by `ℕ` (constant after index `D`). -/
noncomputable def seq (k : ℕ) : V := P.p ⟨min k P.D, by omega⟩

theorem seq_eq {k : ℕ} (hk : k ≤ P.D) : P.seq k = P.p ⟨k, by omega⟩ := by
  unfold seq
  congr 1
  exact Fin.ext (by omega)

/-- The `ℕ`-indexed sequence agrees with the `Fin`-indexed path. -/
theorem seq_val (i : Fin (P.D + 1)) : P.seq (i : ℕ) = P.p i := by
  rw [P.seq_eq (by omega)]
  congr 1
  exact Fin.ext rfl

theorem seq_adj : ∀ k < P.D, S.graph.Adj (P.seq k) (P.seq (k + 1)) := by
  intro k hk
  rw [P.seq_eq (by omega), P.seq_eq (by omega)]
  simpa [Fin.castSucc, Fin.succ, Fin.castAdd, Fin.castLE, Fin.natAdd] using P.adj ⟨k, hk⟩

theorem seq_reachable {u : V} (hu : u ∈ S.alive) :
    ∀ k ≤ P.D, S.graph.Reachable u (P.seq k) := by
  intro k hk
  rw [P.seq_eq hk]
  exact S.connected u hu _ (P.mem _)

theorem seq_inj : ∀ k ≤ P.D, ∀ l ≤ P.D, P.seq k = P.seq l → k = l := by
  intro k hk l hl h
  rw [P.seq_eq hk, P.seq_eq hl] at h
  exact Fin.ext_iff.mp (P.inj h)

/-- `↑P.last = P.D`. -/
theorem val_last : ((P.last : Fin (P.D + 1)) : ℕ) = P.D := DiamPath.last_val P

/-- **Distance from a vertex to the diameter.**  If `P.p i` is a closest vertex of the diameter to
the live vertex `u`, then the distance from `u` to `P.p k` is obtained from the distance to `P.p i`
by adding the index distance `|k - i|`. -/
theorem dist_eq_dist_add {u : V} (hu : u ∈ S.alive) (i : Fin (P.D + 1))
    (hmin : ∀ j : Fin (P.D + 1), S.graph.dist u (P.p i) ≤ S.graph.dist u (P.p j)) :
    (∀ k : Fin (P.D + 1), (i : ℕ) ≤ (k : ℕ) →
        S.graph.dist u (P.p k) = S.graph.dist u (P.p i) + ((k : ℕ) - (i : ℕ))) ∧
    (∀ k : Fin (P.D + 1), (k : ℕ) ≤ (i : ℕ) →
        S.graph.dist u (P.p k) = S.graph.dist u (P.p i) + ((i : ℕ) - (k : ℕ))) := by
  have hmin' : ∀ j ≤ P.D, S.graph.dist u (P.seq (i : ℕ)) ≤ S.graph.dist u (P.seq j) := by
    intro j hj
    rw [P.seq_val i, P.seq_eq hj]
    exact hmin ⟨j, by omega⟩
  constructor
  · intro k hik
    have h := dist_eq_dist_add_of_le S.acyclic P.seq_adj (P.seq_reachable hu) P.seq_inj
      hmin' (k : ℕ) hik (by omega)
    rwa [P.seq_val k, P.seq_val i] at h
  · intro k hki
    have h := dist_eq_dist_add_of_ge S.acyclic P.seq_adj (P.seq_reachable hu) P.seq_inj
      (by omega) hmin' (k : ℕ) hki
    rwa [P.seq_val k, P.seq_val i] at h

/-- Distance between two vertices of the diameter: `dist (p i) (p k) = |k - i|`. -/
theorem dist_path (i j : Fin (P.D + 1)) :
    S.graph.dist (P.p i) (P.p j) = ((j : ℕ) - (i : ℕ)) + ((i : ℕ) - (j : ℕ)) := by
  have hmin : ∀ k : Fin (P.D + 1), S.graph.dist (P.p i) (P.p i) ≤ S.graph.dist (P.p i) (P.p k) :=
    fun k => by rw [dist_self]; exact Nat.zero_le _
  have h := P.dist_eq_dist_add (P.mem i) i hmin
  rcases le_total (i : ℕ) (j : ℕ) with hij | hji
  · rw [h.1 j hij, dist_self, Nat.zero_add]
    omega
  · rw [h.2 j hji, dist_self, Nat.zero_add]
    omega

/-- The length of the diameter is its number of edges. -/
theorem diam_eq_D : S.diam = P.D := by
  have hmin : ∀ k : Fin (P.D + 1), S.graph.dist (P.p 0) (P.p 0) ≤ S.graph.dist (P.p 0) (P.p k) :=
    fun k => by rw [dist_self]; exact Nat.zero_le _
  have h := (P.dist_eq_dist_add (P.mem 0) 0 hmin).1 P.last (Nat.zero_le _)
  have hisDiam : S.graph.dist (P.p 0) (P.p P.last) = S.diam := P.isDiam
  rw [← hisDiam, h, dist_self]
  simp

end DiamPath

/-! ## REF.md §3, Lemma 1 -/

/-- REF.md Lemma 1 (branch height bound).  If `P.p i` is a closest vertex of the diameter `P` to
the live vertex `u`, then that distance is at most `min i (D - i)`. -/
theorem dist_le_min_index (P : DiamPath S) {u : V} (hu : u ∈ S.alive) {i : Fin (P.D + 1)}
    (hmin : ∀ j : Fin (P.D + 1), S.graph.dist u (P.p i) ≤ S.graph.dist u (P.p j)) :
    S.graph.dist u (P.p i) ≤ min (i : ℕ) (P.D - (i : ℕ)) := by
  have h := P.dist_eq_dist_add hu i hmin
  have hile : (i : ℕ) ≤ (P.last : ℕ) := by simpa [DiamPath.val_last] using i.isLt.le
  -- distances to the two endpoints
  have hfst := h.2 0 (Nat.zero_le _)
  have hlst := h.1 P.last hile
  -- every live vertex is at distance at most the diameter, which is `D`
  have h1 : S.graph.dist u (P.p 0) ≤ S.diam := S.dist_le_diam hu (P.mem 0)
  have h2 : S.graph.dist u (P.p P.last) ≤ S.diam := S.dist_le_diam hu (P.mem P.last)
  have h3 : S.diam = P.D := P.diam_eq_D
  have hlast : ((P.last : Fin (P.D + 1)) : ℕ) = P.D := DiamPath.val_last P
  omega

/-! ## REF.md §9, Lemma 6 -/

/-- REF.md Lemma 6: for a diameter with endpoints `P.p 0` and `P.p P.last`, the eccentricity of any
live vertex `x` is realised by one of the two endpoints. -/
theorem dist_le_max_dist_ends (P : DiamPath S) {x : V} (hx : x ∈ S.alive) :
    ∀ y ∈ S.alive,
      S.graph.dist x y ≤ max (S.graph.dist x (P.p 0)) (S.graph.dist x (P.p P.last)) := by
  intro y hy
  -- closest points of the diameter to `x` and to `y`
  obtain ⟨i, hi⟩ := Finite.exists_min (fun i : Fin (P.D + 1) => S.graph.dist x (P.p i))
  obtain ⟨j, hj⟩ := Finite.exists_min (fun j : Fin (P.D + 1) => S.graph.dist y (P.p j))
  have hx' := P.dist_eq_dist_add hx i hi
  have hile : (i : ℕ) ≤ (P.last : ℕ) := by simpa [DiamPath.val_last] using i.isLt.le
  -- the three point inequality around `P.p i` and `P.p j`
  have htri : S.graph.dist x y ≤
      S.graph.dist x (P.p i) + S.graph.dist (P.p i) (P.p j) + S.graph.dist y (P.p j) := by
    have h1 := (S.connected x hx (P.p i) (P.mem i)).dist_triangle_left y
    have h2 := (S.connected (P.p i) (P.mem i) (P.p j) (P.mem j)).dist_triangle_left y
    have h3 : S.graph.dist (P.p j) y = S.graph.dist y (P.p j) := dist_comm
    omega
  -- the branch height bound at `y`
  have hy' := P.dist_le_min_index hy hj
  have hdist_p := P.dist_path i j
  have hlast : ((P.last : Fin (P.D + 1)) : ℕ) = P.D := DiamPath.val_last P
  rcases le_total (i : ℕ) (j : ℕ) with hij | hji
  · have hk : S.graph.dist y (P.p j) ≤ P.D - (j : ℕ) :=
      le_trans hy' (min_le_right _ _)
    have hlast' : S.graph.dist x (P.p P.last) =
        S.graph.dist x (P.p i) + (P.D - (i : ℕ)) := hx'.1 P.last hile
    rw [hdist_p] at htri
    have : S.graph.dist x y ≤ S.graph.dist x (P.p P.last) := by omega
    exact le_trans this (le_max_right _ _)
  · have hk : S.graph.dist y (P.p j) ≤ (j : ℕ) :=
      le_trans hy' (min_le_left _ _)
    have hfst : S.graph.dist x (P.p 0) =
        S.graph.dist x (P.p i) + ((i : ℕ) - 0) := hx'.2 0 (Nat.zero_le _)
    rw [hdist_p] at htri
    have : S.graph.dist x y ≤ S.graph.dist x (P.p 0) := by omega
    exact le_trans this (le_max_left _ _)

end OhtoaiTreeProof
