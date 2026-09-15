/-
# REF.md §7: the two folded trees have the same distances on the common part

`REF.md` Lemma 5 (the delayed exchange lemma) folds two diameters `P`, `Q` of a state `S` which
start at the same diameter endpoint `s`, and compares the two results `P.foldState`, `Q.foldState`.
`OhtoaiTreeProof/Phase1.lean` shows that the two folded states agree off the *difference region* `Δ`
of the two folds: on the common part `C = Δᶜ` they have the same vertices
(`mem_foldAlive_iff_of_not_mem_Delta`) and the same edges (`foldGraph_adj_iff_of_not_mem_Delta`).
What is still missing to compare the two states is the *metric* statement proved here: a live vertex
`v` of the common part is at the *same* distance from `s` in the two folded trees.

`dist_eq_on_common` is exactly the `hdist` hypothesis of `DiamPath.diam_eq_of_dist_eq_on_common`
(`OhtoaiTreeProof/Phase2.lean`), hence it yields the equality of the two folded diameters and, with
`phase1Inv_fold_of_dist_eq`, the phase-1 invariant of the synchronised phase.

## The argument

Let `P.seq i` be a closest vertex of the `P`-diameter to `v`, and `h = d (P.seq i) v`, so that the
`s`-`v` geodesic is `s, …, P.seq i` followed by a geodesic `u 0 = P.seq i, u 1, …, u h = v` of the
branch of `v` (`hproj`).

* `i ≤ ℓ := P.meetIdx Q`: otherwise `P.seq i` is a vertex of the `P`-tail, and `hproj` exhibits it
  as the `Δ`-witness for `v`, contradicting `v ∈ C`.
* For `1 ≤ j ≤ h` the vertex `u j` is off *both* diameters: off `P` because otherwise
  `d v (u j) = h - j < h = d v (P.seq i)` would contradict the minimality of `i`; off `Q` because
  either `u j = Q.seq m` with `m ≤ ℓ` — and then `u j` is on `P` as well — or `m > ℓ`, and then
  `u j` is a `Q`-tail vertex on the `s`-`v` geodesic (`d s (u j) = i + j`), so that `v ∈ Δ` again.
* The vertex sequence `p 0, …, p μ, u 1, …, u h`, where `μ = min i (D - i)`, is therefore injective,
  and consecutive vertices are adjacent in *both* folded trees: on the spine by
  `foldCone_seq_adj`, at the junction because `P.rep (P.seq i) = Q.rep (P.seq i) = P.seq μ`
  (`i ≤ ℓ` and `rep_seq`), and along `u` because `u j` is fixed by both folding maps.  Hence
  `dist_eq_of_seq` computes the distance from `s` to `v` as `μ + h` in either folded tree.
* If `h = 0` then `v = P.seq i` is a vertex of the spine of both folded trees — it survives in
  `P.foldState` by hypothesis, which forces `2i ≤ D` — and `foldCone_spine_dist` /
  `foldCone_spine_dist_Q` give the common value `i`.
-/

import OhtoaiTreeProof.Phase2
import OhtoaiTreeProof.Phase1
import OhtoaiTreeProof.ExchangeLemma5
import OhtoaiTreeProof.ExchangeProof
import OhtoaiTreeProof.Cone
import OhtoaiTreeProof.Iso
import OhtoaiTreeProof.Progress

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DiamPath

variable {S : TreeState V}

/-! ## 1. Vertices off a diameter, and the combined sequence `p 0, …, p m, u 1, …, u n` -/

/-- A vertex which does not lie on the `P`-diameter is fixed by the folding map of `P`. -/
theorem rep_eq_self_of_notMem_pathSet (P : DiamPath S) {v : V} (hv : v ∉ P.pathSet) :
    P.rep v = v :=
  P.rep_eq_self fun i hi => hv (hi ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- A vertex of the `P`-diameter belongs to the path set of `P`. -/
theorem seq_mem_pathSet (P : DiamPath S) {k : ℕ} (hk : k ≤ P.D) : P.seq k ∈ P.pathSet := by
  rw [P.seq_eq hk]
  exact Finset.mem_image.mpr ⟨⟨k, by omega⟩, Finset.mem_univ _, rfl⟩

/-- **A geodesic which has left the diameter walks inside the folded tree.**  If `w` is a path of `S`
from `P.seq i` to `v` whose vertices after the start are off the `P`-diameter, then its consecutive
vertices (from the first one on) are adjacent in `P.foldState`: the two ends are fixed by the folding
map, so the corresponding edge of `S` survives. -/
theorem foldGraph_adj_getVert (P : DiamPath S) {a b : V} {w : S.graph.Walk a b} (hwp : w.IsPath)
    (hu : ∀ j, 1 ≤ j → j ≤ w.length → w.getVert j ∉ P.pathSet) {j : ℕ} (hj1 : 1 ≤ j)
    (hjl : j < w.length) :
    P.foldGraph.Adj (w.getVert j) (w.getVert (j + 1)) := by
  have hadj : S.graph.Adj (w.getVert j) (w.getVert (j + 1)) :=
    w.adj_getVert_succ (i := j) hjl
  have hrep : P.rep (w.getVert j) = w.getVert j :=
    P.rep_eq_self_of_notMem_pathSet (hu j hj1 (le_of_lt hjl))
  have hrep' : P.rep (w.getVert (j + 1)) = w.getVert (j + 1) :=
    P.rep_eq_self_of_notMem_pathSet (hu (j + 1) (by omega) (by omega))
  refine ⟨?_, P.mem_foldAlive.mpr ⟨(S.adj_alive hadj).1, hrep⟩,
    P.mem_foldAlive.mpr ⟨(S.adj_alive hadj).2, hrep'⟩, w.getVert j, w.getVert (j + 1), hadj,
    hrep, hrep'⟩
  intro h
  exact absurd (hwp.getVert_injOn (show j ≤ w.length by omega)
    (show j + 1 ≤ w.length by omega) h) (by omega)

/-- The vertex sequence `p 0, …, p m, u 1, u 2, …`, where `u` is the sequence of vertices of a walk
`w` from `P.seq i` to `v`.  It is the sequence along which both folded trees are traversed in the
main argument: the first `m` edges are edges of the spine, the remaining ones are edges of `w`
(counting `w.getVert 0 = P.seq i` as the `m`-th spine vertex). -/
noncomputable def combSeq (P : DiamPath S) {a b : V} (w : S.graph.Walk a b) (m k : ℕ) : V :=
  if k ≤ m then P.seq k else w.getVert (k - m)

theorem combSeq_of_le (P : DiamPath S) {a b : V} (w : S.graph.Walk a b) {m k : ℕ} (hk : k ≤ m) :
    P.combSeq w m k = P.seq k :=
  ite_eq_left hk

theorem combSeq_of_lt (P : DiamPath S) {a b : V} (w : S.graph.Walk a b) {m k : ℕ} (hk : m < k) :
    P.combSeq w m k = w.getVert (k - m) :=
  ite_eq_right (not_le.mpr hk)

/-! ## 2. The distance in `P.foldState` along `p 0, …, p μ, u 1, …, u h`

The junction vertex is `P.seq μ` with `μ = min i (D - i)`: the edge `P.seq i`–`u 1` of `S` is folded
onto it, because `P.rep (P.seq i) = P.seq μ` and `u 1` is off the diameter. -/

/-- **The distance from `s` to `v` in `P.foldState`.**  If `w` is a path of `S` from `P.seq i` to `v`
whose vertices after `P.seq i` avoid the `P`-diameter, then the distance from `s = P.seq 0` to `v` in
`P.foldState` is `min i (D - i) + w.length`: folding carries `P.seq i` onto the spine vertex
`P.seq (min i (D - i))`, and the rest of `w` survives unchanged. -/
theorem foldGraph_dist_of_getVert (P : DiamPath S) {s v : V} (hP : P.p 0 = s) {i : ℕ}
    (hiD : i ≤ P.D) {w : S.graph.Walk (P.seq i) v} (hwp : w.IsPath) (hwpos : 0 < w.length)
    (hu : ∀ j, 1 ≤ j → j ≤ w.length → w.getVert j ∉ P.pathSet) :
    P.foldGraph.dist s v = min i (P.D - i) + w.length := by
  set μ := min i (P.D - i) with hμ
  have h2μ : 2 * μ ≤ P.D := by
    have h := P.min_le_sub i
    rw [hμ]
    omega
  have hμD : μ ≤ P.D := by omega
  have hjunc : P.foldGraph.Adj (P.seq μ) (w.getVert 1) := by
    have hrep1 : P.rep (w.getVert 1) = w.getVert 1 :=
      P.rep_eq_self_of_notMem_pathSet (hu 1 le_rfl hwpos)
    have hadj1 : S.graph.Adj (P.seq i) (w.getVert 1) := by
      simpa using w.adj_getVert_succ (i := 0) hwpos
    refine ⟨?_, P.mem_foldAlive.mpr ⟨P.seq_mem μ, P.rep_seq_eq_self (by omega)⟩,
      P.mem_foldAlive.mpr ⟨(S.adj_alive hadj1).2, hrep1⟩, P.seq i, w.getVert 1, hadj1, ?_,
      hrep1⟩
    · intro h
      exact hu 1 le_rfl hwpos (h ▸ P.seq_mem_pathSet hμD)
    · rw [P.rep_seq hiD, ← hμ]
  have hadj : ∀ k < μ + w.length, P.foldGraph.Adj (P.combSeq w μ k) (P.combSeq w μ (k + 1)) := by
    intro k hk
    rcases lt_trichotomy k μ with hlt | heq | hgt
    · rw [P.combSeq_of_le w (le_of_lt hlt), P.combSeq_of_le w (by omega)]
      exact P.foldCone_seq_adj k (by omega)
    · rw [heq, P.combSeq_of_le w le_rfl, P.combSeq_of_lt w (by omega),
        show μ + 1 - μ = 1 by omega]
      exact hjunc
    · rw [P.combSeq_of_lt w hgt, P.combSeq_of_lt w (by omega),
        show k + 1 - μ = (k - μ) + 1 by omega]
      exact P.foldGraph_adj_getVert hwp hu (j := k - μ) (by omega) (by omega)
  have hinj : ∀ k ≤ μ + w.length, ∀ l ≤ μ + w.length, P.combSeq w μ k = P.combSeq w μ l → k = l := by
    intro k hk l hl hkl
    by_cases hkμ : k ≤ μ
    · by_cases hlμ : l ≤ μ
      · rw [P.combSeq_of_le w hkμ, P.combSeq_of_le w hlμ] at hkl
        exact P.foldCone_seq_inj k (by omega) l (by omega) hkl
      · exfalso
        rw [P.combSeq_of_le w hkμ, P.combSeq_of_lt w (Nat.lt_of_not_le hlμ)] at hkl
        exact hu (l - μ) (by omega) (by omega) (hkl ▸ P.seq_mem_pathSet (by omega))
    · by_cases hlμ : l ≤ μ
      · exfalso
        rw [P.combSeq_of_lt w (Nat.lt_of_not_le hkμ), P.combSeq_of_le w hlμ] at hkl
        exact hu (k - μ) (by omega) (by omega) (hkl.symm ▸ P.seq_mem_pathSet (by omega))
      · rw [P.combSeq_of_lt w (Nat.lt_of_not_le hkμ),
          P.combSeq_of_lt w (Nat.lt_of_not_le hlμ)] at hkl
        have h1 := hwp.getVert_injOn (show k - μ ≤ w.length by omega)
          (show l - μ ≤ w.length by omega) hkl
        omega
  have h0 : P.combSeq w μ 0 = s := by
    rw [P.combSeq_of_le w (Nat.zero_le μ), P.seq_zero, hP]
  have hn : P.combSeq w μ (μ + w.length) = v := by
    rw [P.combSeq_of_lt w (by omega), show μ + w.length - μ = w.length by omega,
      w.getVert_length]
  have hres := dist_eq_of_seq (H := P.foldGraph) P.foldGraph_isAcyclic (q := P.combSeq w μ)
    (n := μ + w.length) hadj hinj
  rwa [h0, hn] at hres

/-- **The distance from `s` to `v` in `Q.foldState`**, computed along the same sequence.  Here the
junction needs `P.seq i = Q.seq i` (which holds because `i` lies in the common prefix) and
`Q.rep (P.seq i) = P.seq (min i (D - i))`. -/
theorem foldGraph_dist_of_getVert_Q (P Q : DiamPath S) {s v : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {i : ℕ} (hiD : i ≤ P.D) (hile : i ≤ P.meetIdx Q)
    {w : S.graph.Walk (P.seq i) v} (hwp : w.IsPath) (hwpos : 0 < w.length)
    (hu : ∀ j, 1 ≤ j → j ≤ w.length → w.getVert j ∉ Q.pathSet) :
    Q.foldGraph.dist s v = min i (P.D - i) + w.length := by
  have hDi : P.D = Q.D := P.D_eq Q
  have hlD : P.meetIdx Q ≤ P.D := P.meetIdx_le Q
  set μ := min i (P.D - i) with hμ
  have h2μ : 2 * μ ≤ P.D := by
    have h := P.min_le_sub i
    rw [hμ]
    omega
  have hμℓ : μ ≤ P.meetIdx Q := by
    rw [hμ]
    exact le_trans (Nat.min_le_left _ _) hile
  have hμeq : P.seq μ = Q.seq μ := P.seq_eq_of_le_meetIdx Q hP hQ hμℓ
  -- every spine vertex is a vertex of the `Q`-path
  have hspine : ∀ t ≤ P.meetIdx Q, P.seq t ∈ Q.pathSet := by
    intro t ht
    rw [P.seq_eq_of_le_meetIdx Q hP hQ ht]
    exact Q.seq_mem_pathSet (by omega)
  have hjunc : Q.foldGraph.Adj (P.seq μ) (w.getVert 1) := by
    have hrep1 : Q.rep (w.getVert 1) = w.getVert 1 :=
      Q.rep_eq_self_of_notMem_pathSet (hu 1 le_rfl hwpos)
    have hadj1 : S.graph.Adj (P.seq i) (w.getVert 1) := by
      simpa using w.adj_getVert_succ (i := 0) hwpos
    refine ⟨?_, Q.mem_foldAlive.mpr ⟨P.seq_mem μ, ?_⟩,
      Q.mem_foldAlive.mpr ⟨(S.adj_alive hadj1).2, hrep1⟩, P.seq i, w.getVert 1, hadj1, ?_,
      hrep1⟩
    · intro h
      exact hu 1 le_rfl hwpos (h ▸ hspine μ hμℓ)
    · rw [hμeq]
      exact Q.rep_seq_eq_self (by omega)
    · calc Q.rep (P.seq i) = Q.rep (Q.seq i) := by rw [P.seq_eq_of_le_meetIdx Q hP hQ hile]
        _ = Q.seq (min i (Q.D - i)) := Q.rep_seq (by omega)
        _ = Q.seq (min i (P.D - i)) := by rw [show min i (Q.D - i) = min i (P.D - i) by omega]
        _ = P.seq (min i (P.D - i)) := (P.seq_eq_of_le_meetIdx Q hP hQ (by omega)).symm
        _ = P.seq μ := by rw [hμ]
  have hadj : ∀ k < μ + w.length, Q.foldGraph.Adj (P.combSeq w μ k) (P.combSeq w μ (k + 1)) := by
    intro k hk
    rcases lt_trichotomy k μ with hlt | heq | hgt
    · rw [P.combSeq_of_le w (le_of_lt hlt), P.combSeq_of_le w (by omega),
        P.seq_eq_of_le_meetIdx Q hP hQ (by omega), P.seq_eq_of_le_meetIdx Q hP hQ (by omega)]
      exact Q.foldCone_seq_adj k (by omega)
    · rw [heq, P.combSeq_of_le w le_rfl, P.combSeq_of_lt w (by omega),
        show μ + 1 - μ = 1 by omega]
      exact hjunc
    · rw [P.combSeq_of_lt w hgt, P.combSeq_of_lt w (by omega),
        show k + 1 - μ = (k - μ) + 1 by omega]
      exact Q.foldGraph_adj_getVert hwp hu (j := k - μ) (by omega) (by omega)
  have hinj : ∀ k ≤ μ + w.length, ∀ l ≤ μ + w.length, P.combSeq w μ k = P.combSeq w μ l → k = l := by
    intro k hk l hl hkl
    by_cases hkμ : k ≤ μ
    · by_cases hlμ : l ≤ μ
      · rw [P.combSeq_of_le w hkμ, P.combSeq_of_le w hlμ] at hkl
        exact P.foldCone_seq_inj k (by omega) l (by omega) hkl
      · exfalso
        rw [P.combSeq_of_le w hkμ, P.combSeq_of_lt w (Nat.lt_of_not_le hlμ)] at hkl
        exact hu (l - μ) (by omega) (by omega) (hkl ▸ hspine k (by omega))
    · by_cases hlμ : l ≤ μ
      · exfalso
        rw [P.combSeq_of_lt w (Nat.lt_of_not_le hkμ), P.combSeq_of_le w hlμ] at hkl
        exact hu (k - μ) (by omega) (by omega) (hkl.symm ▸ hspine l (by omega))
      · rw [P.combSeq_of_lt w (Nat.lt_of_not_le hkμ),
          P.combSeq_of_lt w (Nat.lt_of_not_le hlμ)] at hkl
        have h1 := hwp.getVert_injOn (show k - μ ≤ w.length by omega)
          (show l - μ ≤ w.length by omega) hkl
        omega
  have h0 : P.combSeq w μ 0 = s := by
    rw [P.combSeq_of_le w (Nat.zero_le μ), P.seq_zero, hP]
  have hn : P.combSeq w μ (μ + w.length) = v := by
    rw [P.combSeq_of_lt w (by omega), show μ + w.length - μ = w.length by omega,
      w.getVert_length]
  have hres := dist_eq_of_seq (H := Q.foldGraph) Q.foldGraph_isAcyclic (q := P.combSeq w μ)
    (n := μ + w.length) hadj hinj
  rwa [h0, hn] at hres

/-! ## 3. The common part of the two folds is at the same distance from `s` -/

/-- **The two folded trees have the same distances on the common part.**  If `P` and `Q` are
diameters of `S` starting at the same vertex `s`, then a live vertex `v` of `P.foldState` which lies
outside the difference region `Δ` is at the same distance from `s` in `P.foldState` and in
`Q.foldState`.

This is the metric half of "the two folded states agree on the common part"
(`Phase1.lean` supplies the combinatorial half), and it is the hypothesis `hdist` of
`DiamPath.diam_eq_of_dist_eq_on_common`. -/
theorem dist_eq_on_common (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    {v : V} (hvC : v ∉ P.Delta Q s) (hvA : v ∈ P.foldAlive) :
    P.foldGraph.dist s v = Q.foldGraph.dist s v := by
  have hvS : v ∈ S.alive := (P.mem_foldAlive.mp hvA).1
  obtain ⟨i, hiD, hmin⟩ := P.exists_closest_index_seq v
  have hlD : P.meetIdx Q ≤ P.D := P.meetIdx_le Q
  -- the projection of `v` on the `P`-diameter
  have hproj : S.graph.dist s v = i + S.graph.dist (P.seq i) v := by
    have h0 := P.dist_seq_eq_add_of_ge (u := v) hvS hiD hmin (k := 0) (Nat.zero_le _)
    rw [P.seq_zero, hP, Nat.sub_zero] at h0
    calc S.graph.dist s v = S.graph.dist v s := SimpleGraph.dist_comm ..
      _ = S.graph.dist v (P.seq i) + i := h0
      _ = S.graph.dist (P.seq i) v + i := by rw [SimpleGraph.dist_comm]
      _ = i + S.graph.dist (P.seq i) v := by omega
  -- the closest index of `v` is in the common prefix
  have hile : i ≤ P.meetIdx Q := by
    by_contra hcon
    refine hvC ⟨P.seq i, (P.seq_mem_tailSet_iff Q hP hQ hiD).mpr (Nat.lt_of_not_le hcon), ?_⟩
    rw [P.dist_seq_zero hP hiD]
    exact hproj
  rcases Nat.eq_zero_or_pos (S.graph.dist (P.seq i) v) with hz | hpos
  · -- `v` itself is a vertex of the `P`-diameter, hence a vertex of the spine of both folded trees
    have hvi : v = P.seq i := ((S.dist_eq_zero_iff (P.seq_mem i) hvS).mp hz).symm
    have hrep : P.rep (P.seq i) = P.seq i := by
      rw [← hvi]
      exact (P.mem_foldAlive.mp hvA).2
    have hmin_eq : min i (P.D - i) = i := by
      have h1 := P.rep_seq hiD
      rw [hrep] at h1
      exact (P.seq_inj i hiD (min i (P.D - i)) (le_trans (Nat.min_le_left _ _) hiD) h1).symm
    have hhalf : i ≤ P.D / 2 := by
      have h2 := Nat.min_le_right i (P.D - i)
      omega
    rw [hvi]
    have h1 : P.foldGraph.dist s (P.seq i) = i := by
      rw [← hP, ← P.seq_zero]
      exact P.foldCone_spine_dist hhalf
    have h2 : Q.foldGraph.dist s (P.seq i) = i := by
      rw [← hP, ← P.seq_zero]
      exact P.foldCone_spine_dist_Q Q hP hQ hhalf
    rw [h1, h2]
  · -- the branch of `v` above the diameter
    obtain ⟨w, hwp, hwl⟩ := (S.connected (P.seq i) (P.seq_mem i) v hvS).exists_path_of_dist
    have hwpos : 0 < w.length := by rw [hwl]; exact hpos
    have hprojW : S.graph.dist s v = i + w.length := by rw [hproj, ← hwl]
    -- (A) the vertices of `w` after its start avoid the `P`-diameter
    have huP : ∀ j, 1 ≤ j → j ≤ w.length → w.getVert j ∉ P.pathSet := by
      intro j hj1 hjw hmem
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hmem
      have hmD : (m : ℕ) ≤ P.D := by have := m.isLt; omega
      have hseqm : P.seq (m : ℕ) = w.getVert j := by rw [P.seq_val m]; exact hm
      have hdj : S.graph.dist (w.getVert j) v = w.length - j :=
        dist_getVert_eq_sub S.acyclic hwp hjw
      have hlt : S.graph.dist v (P.seq (m : ℕ)) < S.graph.dist v (P.seq i) := by
        have h1 : S.graph.dist v (P.seq (m : ℕ)) = w.length - j := by
          rw [hseqm, SimpleGraph.dist_comm]
          exact hdj
        have h2 : S.graph.dist v (P.seq i) = w.length := by
          rw [SimpleGraph.dist_comm]
          exact hwl.symm
        rw [h1, h2]
        omega
      exact absurd (hmin (m : ℕ) hmD) (by omega)
    -- (B) the `s`-`v` geodesic is `s, …, P.seq i, u 1, …, u h`
    have huS : ∀ j, 1 ≤ j → j ≤ w.length → S.graph.dist s (w.getVert j) = i + j := by
      intro j hj1 hjw
      have h0 : P.combSeq w i 0 = s := by
        rw [P.combSeq_of_le w (Nat.zero_le i), P.seq_zero, hP]
      have hj : P.combSeq w i (i + j) = w.getVert j := by
        rw [P.combSeq_of_lt w (by omega), show i + j - i = j by omega]
      have hadj : ∀ k < i + j, S.graph.Adj (P.combSeq w i k) (P.combSeq w i (k + 1)) := by
        intro k hk
        rcases lt_trichotomy k i with hlt | heq | hgt
        · rw [P.combSeq_of_le w (le_of_lt hlt), P.combSeq_of_le w (by omega)]
          exact P.seq_adj k (by omega)
        · rw [heq, P.combSeq_of_le w le_rfl, P.combSeq_of_lt w (by omega),
            show i + 1 - i = 1 by omega]
          simpa using w.adj_getVert_succ (i := 0) hwpos
        · rw [P.combSeq_of_lt w hgt, P.combSeq_of_lt w (by omega),
            show k + 1 - i = (k - i) + 1 by omega]
          exact w.adj_getVert_succ (i := k - i) (by omega)
      have hinj : ∀ k ≤ i + j, ∀ l ≤ i + j, P.combSeq w i k = P.combSeq w i l → k = l := by
        intro k hk l hl hkl
        by_cases hkμ : k ≤ i
        · by_cases hlμ : l ≤ i
          · rw [P.combSeq_of_le w hkμ, P.combSeq_of_le w hlμ] at hkl
            exact P.seq_inj k (by omega) l (by omega) hkl
          · exfalso
            rw [P.combSeq_of_le w hkμ, P.combSeq_of_lt w (Nat.lt_of_not_le hlμ)] at hkl
            exact huP (l - i) (by omega) (by omega) (hkl ▸ P.seq_mem_pathSet (by omega))
        · by_cases hlμ : l ≤ i
          · exfalso
            rw [P.combSeq_of_lt w (Nat.lt_of_not_le hkμ), P.combSeq_of_le w hlμ] at hkl
            exact huP (k - i) (by omega) (by omega)
              (hkl.symm ▸ P.seq_mem_pathSet (by omega))
          · rw [P.combSeq_of_lt w (Nat.lt_of_not_le hkμ),
              P.combSeq_of_lt w (Nat.lt_of_not_le hlμ)] at hkl
            have h1 := hwp.getVert_injOn (show k - i ≤ w.length by omega)
              (show l - i ≤ w.length by omega) hkl
            omega
      have hres := dist_eq_of_seq (H := S.graph) S.acyclic (q := P.combSeq w i) (n := i + j)
        hadj hinj
      rwa [h0, hj] at hres
    -- (C) the vertices of `w` after its start avoid the `Q`-diameter
    have huQ : ∀ j, 1 ≤ j → j ≤ w.length → w.getVert j ∉ Q.pathSet := by
      intro j hj1 hjw hmem
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hmem
      have hmD : (m : ℕ) ≤ P.D := by have := P.D_eq Q; have := m.isLt; omega
      have hseqm : Q.seq (m : ℕ) = w.getVert j := by rw [Q.seq_val m]; exact hm
      by_cases hmle : (m : ℕ) ≤ P.meetIdx Q
      · -- `u j` lies on the `P`-diameter as well
        have hPseq : P.seq (m : ℕ) = w.getVert j := by
          rw [P.seq_eq_of_le_meetIdx Q hP hQ hmle]
          exact hseqm
        exact huP j hj1 hjw (hPseq ▸ P.seq_mem_pathSet (by omega))
      · -- `u j` is a vertex of the `Q`-tail, so that `v` lies in `Δ`
        have htail : Q.seq (m : ℕ) ∈ P.tailSet Q :=
          (P.seq_mem_tailSet_iff_Q Q hP hQ hmD).mpr (Nat.lt_of_not_le hmle)
        refine hvC ⟨Q.seq (m : ℕ), htail, ?_⟩
        have h1 : S.graph.dist s (Q.seq (m : ℕ)) = i + j := by
          rw [hseqm]
          exact huS j hj1 hjw
        have h2 : S.graph.dist (Q.seq (m : ℕ)) v = w.length - j := by
          rw [hseqm]
          exact dist_getVert_eq_sub S.acyclic hwp hjw
        rw [h1, h2, hprojW]
        omega
    rw [P.foldGraph_dist_of_getVert hP hiD hwp hwpos huP,
      P.foldGraph_dist_of_getVert_Q Q hP hQ hiD hile hwp hwpos huQ]

end DiamPath

end OhtoaiTreeProof
