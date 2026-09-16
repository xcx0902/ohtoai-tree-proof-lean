/-
# REF.md §7: the invariant for the synchronised phase

This file defines `SyncCtx` and proves its initial instance, the geodesic property, and transport
of a common diameter. `SyncStep.lean` proves preservation and termination of the phase;
`SyncEndgame.lean` proves the common endgame and `DiamPath.synchronized_exchange`.
Coincident initial diameters are handled separately, including singleton first-fold states.

## The shape of the argument

Write `r = P.D - P.meetIdx Q` for the common tail length and `Δ = P.Delta Q s` for the difference
region.  The two folded states agree outside `Δ` (`Phase1Inv`) and every live vertex of `Δ` is
within `2r` of `s` in either of them.

* **The geodesic property** (`GeodAvoid`, §1).  Instead of the descent property `DeltaClosed` of
  `Phase3.lean`, the phase is driven by the much cheaper statement that every live vertex *outside*
  `Δ` is the end of a geodesic from `s` that avoids `Δ` entirely.  It is proved for the initial pair
  by pushing the geodesic of `S` through `P.rep` and taking the `bypass` of the resulting walk (§2),
  and it is preserved by a fold along a path contained in `C` for the same reason (§4).
* **The leg survives** (`SeqPath`, §3).  The leg `p 0, …, p r, q (ℓ+1), …, q D` of `P.foldState` is
  a path of length `2r` from `s` whose first half (the spine) is fixed by every synchronised fold
  (it lies at distance `≤ r < H/2` on the folded diameter) and whose second half lies in `Δ`, hence
  off the folded diameter.  So it stays a path and gives `2 * r ≤ T.diam` at every stage.
* **The quotient map `σ`.**  All synchronised folds use the *same vertex sequence* in the two
  states, so they use the *same* folding map as a function `V → V`; the invariant `SyncCtx` records
  the composite `σ` together with the descriptions of the two states as quotients of `P.foldState`
  and `Q.foldState` by `σ` (§3).  Membership and adjacency of `C` are then preserved by a step
  *because every witness of an adjacency lies outside `Δ`* (§4).
* **The phase** (`SyncStep.lean`) is a strong induction on the number of live vertices: while `2r < T₁.diam` one
  synchronised step strictly decreases it (`FoldStep.card_lt`), and the invariant — including
  `T₁.diam = T₂.diam`, re-derived from the distance agreement on `C` — is preserved.  The phase stops
  exactly at `T₁.diam = 2r`.
* **The endgame** (`SyncEndgame.lean`): folding `T₁` along its leg and `T₂` along *its* leg (the spine followed by
  the `P`-tail) gives the same state, because the two composites `ρ ∘ σ ∘ P.rep` and
  `ρ' ∘ σ ∘ Q.rep` agree pointwise (`legAt_rep_comp`). Off the original tails, both representatives
  agree; on the tails, `σ` fixes both the surviving tail and the corresponding spine vertex.
-/
import OhtoaiTreeProof.Phase3
import OhtoaiTreeProof.CommonDist
import OhtoaiTreeProof.PathExists

set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Geodesics from `s`, and sequences that are paths -/

/-- **The geodesic property.**  Every live vertex of `T` outside the set `D` is the endpoint of a
geodesic from `s` whose vertices all lie outside `D`.  For `D = Δ` this is what the synchronised
phase needs: the far end of a long diameter is outside `Δ`, hence the whole diameter path is. -/
def GeodAvoid (T : TreeState V) (D : Set V) (s : V) : Prop :=
  ∀ x : V, x ∈ T.alive → x ∉ D →
    ∃ p : T.graph.Walk s x, p.IsPath ∧ p.length = T.graph.dist s x ∧
      ∀ k ≤ p.length, p.getVert k ∉ D

/-- Reading a path in two acyclic graphs gives the same distance. -/
theorem GeodAvoid.dist_eq {T U : TreeState V} {D : Set V} {s x : V}
    (h : GeodAvoid T D s)
    (hadj : ∀ u v, u ∉ D → v ∉ D → (T.graph.Adj u v ↔ U.graph.Adj u v))
    (hx : x ∈ T.alive) (hxD : x ∉ D) :
    T.graph.dist s x = U.graph.dist s x := by
  obtain ⟨p, hp, hlen, havoid⟩ := h x hx hxD
  have heq := dist_eq_of_seq U.acyclic
    (fun k hk => (hadj _ _ (havoid k (by omega))
      (havoid (k + 1) (by omega))).mp (p.adj_getVert_succ hk))
    (fun k hk l hl hkl => hp.getVert_injOn hk hl hkl)
  rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length] at heq
  exact (heq.trans hlen).symm

/-- `SeqPath T q L`: the vertices `q 0, …, q L` form a path of the state `T` (they are live,
consecutive ones are adjacent, and there is no repetition). -/
def SeqPath (T : TreeState V) (q : ℕ → V) (L : ℕ) : Prop :=
  (∀ k ≤ L, q k ∈ T.alive) ∧ (∀ k < L, T.graph.Adj (q k) (q (k + 1))) ∧
    ∀ k ≤ L, ∀ l ≤ L, q k = q l → k = l

/-- A path of a state, read as a geodesic: the distance from its start to its `k`-th vertex is
`k`. -/
theorem SeqPath.dist_eq {T : TreeState V} {q : ℕ → V} {L : ℕ} (h : SeqPath T q L) {k : ℕ}
    (hk : k ≤ L) : T.graph.dist (q 0) (q k) = k :=
  dist_eq_of_seq T.acyclic (q := q) (n := k)
    (fun j hj => h.2.1 j (by omega)) (fun j _ l _ hij => h.2.2 j (by omega) l (by omega) hij)

namespace DiamPath

variable {S : TreeState V}

/-- The image of an edge under a folding map, with control on the vertices of the image: they are
the two images of the endpoints of the edge. -/
theorem exists_walk_rep_of_adj_mem (Z : DiamPath S) {a b : V} (h : S.graph.Adj a b) :
    ∃ w : Z.foldGraph.Walk (Z.rep a) (Z.rep b), w.length ≤ 1 ∧
      ∀ y ∈ w.support, y = Z.rep a ∨ y = Z.rep b := by
  rcases eq_or_ne (Z.rep a) (Z.rep b) with heq | hne
  · refine ⟨SimpleGraph.Walk.nil.copy heq.symm rfl, by simp, fun y hy => ?_⟩
    simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil, List.mem_singleton]
      at hy
    exact Or.inl (hy.trans heq.symm)
  · have hadj : Z.foldGraph.Adj (Z.rep a) (Z.rep b) :=
      ⟨hne, Z.rep_mem_foldAlive (S.adj_alive h).1, Z.rep_mem_foldAlive (S.adj_alive h).2,
        a, b, h, rfl, rfl⟩
    refine ⟨hadj.toWalk, by simp, fun y hy => ?_⟩
    rw [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The image of a walk under a folding map, with control on its vertices. -/
theorem exists_fold_walk_le_mem (Z : DiamPath S) {u v : V} (w : S.graph.Walk u v) :
    ∃ w' : Z.foldGraph.Walk (Z.rep u) (Z.rep v), w'.length ≤ w.length ∧
      ∀ y ∈ w'.support, ∃ x ∈ w.support, Z.rep x = y := by
  induction w with
  | nil =>
      refine ⟨SimpleGraph.Walk.nil, le_rfl, ?_⟩
      intro y hy
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      exact ⟨_, List.mem_singleton_self _, by rw [hy]⟩
  | @cons a b c hadj rest ih =>
      obtain ⟨w₁, h₁, hs₁⟩ := Z.exists_walk_rep_of_adj_mem hadj
      obtain ⟨w₂, h₂, hs₂⟩ := ih
      refine ⟨w₁.append w₂, ?_, ?_⟩
      · simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
        omega
      · have ha : a ∈ (SimpleGraph.Walk.cons hadj rest).support := by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inl trivial
        have hb : b ∈ (SimpleGraph.Walk.cons hadj rest).support := by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr (SimpleGraph.Walk.start_mem_support rest)
        intro y hy
        rw [SimpleGraph.Walk.mem_support_append_iff] at hy
        rcases hy with hy | hy
        · rcases hs₁ y hy with hy' | hy'
          · exact ⟨a, ha, hy'.symm⟩
          · exact ⟨b, hb, hy'.symm⟩
        · obtain ⟨x, hx, rfl⟩ := hs₂ y hy
          refine ⟨x, ?_, rfl⟩
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
          exact Or.inr hx

/-- **`P.rep` maps the common part into itself**: the representative of a vertex outside `Δ` lies
outside `Δ` as well.  On the diameter this is the description of `Δ` on the spine
(`seq_mem_Delta_iff`), off the diameter `rep` is the identity. -/
theorem rep_notMem_Delta (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) {v : V}
    (hv : v ∉ P.Delta Q s) : P.rep v ∉ P.Delta Q s := by
  by_cases hmem : v ∈ P.pathSet
  · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
    have hiD : (i : ℕ) ≤ P.D := by have := i.isLt; omega
    have hv' : v = P.seq (i : ℕ) := by rw [P.seq_val i]; exact hi.symm
    have hiℓ : (i : ℕ) ≤ P.meetIdx Q := by
      by_contra hcon
      exact hv (hv' ▸ (P.seq_mem_Delta_iff Q hP hQ hiD).mpr (Nat.lt_of_not_le hcon))
    rw [hv', P.rep_seq hiD]
    intro hcon
    exact absurd ((P.seq_mem_Delta_iff Q hP hQ (by omega)).mp hcon) (by omega)
  · rw [P.rep_eq_self_of_notMem_pathSet hmem]
    exact hv

/-! ## 2. The geodesic property for the initial pair -/

/-- **The geodesic property of `P.foldState`.**  Let `x` be a live vertex outside `Δ`.  The geodesic
of `S` from `s` to `x` avoids `Δ` (a vertex `t` of the tail set on it would witness `x ∈ Δ` by the
triangle inequality), and `P.rep` carries it to a walk of `P.foldState` whose vertices are all
representatives of vertices outside `Δ`, hence outside `Δ` as well (`rep_notMem_Delta`).  The
`bypass` of that walk is a geodesic of `P.foldState` with the same property. -/
theorem geod_fold (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    GeodAvoid P.foldState (P.Delta Q s) s := by
  intro x hx hxΔ
  have hsA : s ∈ S.alive := by rw [← hP]; exact P.seq_mem 0
  have hxA : x ∈ S.alive := P.foldAlive_subset hx
  obtain ⟨p, hp, hplen⟩ := (S.connected s hsA x hxA).exists_path_of_dist
  -- the geodesic of `S` from `s` to `x` avoids `Δ`
  have hpΔ : ∀ k ≤ p.length, p.getVert k ∉ P.Delta Q s := by
    intro k hk hmem
    obtain ⟨t, ht, hdt⟩ := hmem
    have htA : t ∈ S.alive := by
      rcases P.mem_tailSet.mp ht with ⟨i, -, -, rfl⟩ | ⟨j, -, -, rfl⟩
      · exact P.seq_mem i
      · exact Q.seq_mem j
    have hkA : p.getVert k ∈ S.alive := getVert_mem_alive hsA p k
    have hdist1 : S.graph.dist s (p.getVert k) = k := dist_getVert_eq S.acyclic hp hk
    have hdist2 : S.graph.dist (p.getVert k) x = p.length - k :=
      dist_getVert_eq_sub S.acyclic hp hk
    have hsplit : S.graph.dist s x =
        S.graph.dist s (p.getVert k) + S.graph.dist (p.getVert k) x := by
      rw [hdist1, hdist2, hplen]
      omega
    have hmain : S.graph.dist s x = S.graph.dist s t + S.graph.dist t x := by
      refine le_antisymm ?_ ?_
      · have h1 : S.graph.dist s x ≤ S.graph.dist s t + S.graph.dist t x :=
          (S.connected s hsA t htA).dist_triangle_left x
        have h2 : S.graph.dist t x ≤ S.graph.dist t (p.getVert k) + S.graph.dist (p.getVert k) x :=
          (S.connected t htA (p.getVert k) hkA).dist_triangle_left x
        omega
      · have h2 : S.graph.dist t x ≤ S.graph.dist t (p.getVert k) + S.graph.dist (p.getVert k) x :=
          (S.connected t htA (p.getVert k) hkA).dist_triangle_left x
        omega
    exact hxΔ ⟨t, ht, hmain⟩
  -- push the geodesic through `P.rep`
  obtain ⟨w, -, hwsup⟩ := P.exists_fold_walk_le_mem p
  have hreps : P.rep s = s := by
    rw [← hP]
    exact P.rep_path_fix (Nat.zero_le _) (Nat.zero_le _)
  have hrepx : P.rep x = x := (P.mem_foldAlive.mp hx).2
  refine ⟨(w.copy hreps hrepx).bypass, SimpleGraph.Walk.bypass_isPath _, ?_, ?_⟩
  · exact length_eq_dist_of_isPath P.foldGraph_isAcyclic (SimpleGraph.Walk.bypass_isPath _)
  · intro k hk hmem
    have hsup : (w.copy hreps hrepx).bypass.support ⊆ w.support := by
      intro y hy
      have h1 : y ∈ (w.copy hreps hrepx).support :=
        SimpleGraph.Walk.support_bypass_subset_support _ hy
      simpa using h1
    have hmem' : (w.copy hreps hrepx).bypass.getVert k ∈ w.support :=
      hsup (SimpleGraph.Walk.getVert_mem_support _ k)
    obtain ⟨z, hz, hzr⟩ := hwsup _ hmem'
    obtain ⟨l, hlz, hl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
    have hz' : P.rep (p.getVert l) = (w.copy hreps hrepx).bypass.getVert k := by
      rw [hlz, hzr]
    exact P.rep_notMem_Delta Q hP hQ (hpΔ l hl) (hz' ▸ hmem)

/-- The geodesic property of `Q.foldState`, with the difference region written on the `Q` side. -/
theorem geod_fold_Q (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    GeodAvoid Q.foldState (Q.Delta P s) s :=
  geod_fold Q P hQ hP

end DiamPath


/-! ## 3. The geodesic property is preserved by a fold inside the common part -/

namespace DiamPath

variable {S : TreeState V}

/-- The folding map preserves the complement of a set disjoint from the diameter path. -/
theorem rep_notMem_of_path_notMem (Z : DiamPath S) {D : Set V} (hZ : ∀ i, Z.p i ∉ D) {x : V}
    (hx : x ∉ D) : Z.rep x ∉ D := by
  rcases h : Z.index x with _ | i
  · rw [Z.rep_of_index_none h]
    exact hx
  · rw [Z.rep_of_index_some h]
    exact hZ _

end DiamPath

/-- **A fold inside the "common part" preserves the geodesic property.**  If `Z` is a path of `T`
whose vertices avoid `D`, and the folding map of `Z` maps the complement of `D` into itself, then
the geodesic from `s` to a live vertex outside `D` can be pushed through `Z.rep` (its vertices stay
outside `D`) and shortened to a geodesic by `bypass`. -/
theorem GeodAvoid.fold {T : TreeState V} {D : Set V} {s : V} (h : GeodAvoid T D s)
    (Z : DiamPath T) (_hZ : ∀ i, Z.p i ∉ D) (hfix : ∀ x : V, x ∉ D → Z.rep x ∉ D)
    (hs : Z.p 0 = s) : GeodAvoid Z.foldState D s := by
  intro x hx hxD
  obtain ⟨hxT, hxfix⟩ := Z.mem_foldAlive.mp hx
  obtain ⟨p, hp, hplen, hpD⟩ := h x hxT hxD
  obtain ⟨w, -, hwsup⟩ := Z.exists_fold_walk_le_mem p
  have hreps : Z.rep s = s := by
    rw [← hs, Z.rep_path]
    exact congrArg Z.p (Fin.ext (by simp))
  refine ⟨(w.copy hreps hxfix).bypass, SimpleGraph.Walk.bypass_isPath _, ?_, ?_⟩
  · exact length_eq_dist_of_isPath Z.foldGraph_isAcyclic (SimpleGraph.Walk.bypass_isPath _)
  · intro k hk hmem
    have hsup : (w.copy hreps hxfix).bypass.support ⊆ w.support := by
      intro y hy
      have h1 : y ∈ (w.copy hreps hxfix).support :=
        SimpleGraph.Walk.support_bypass_subset_support _ hy
      simpa using h1
    have hmem' : (w.copy hreps hxfix).bypass.getVert k ∈ w.support :=
      hsup (SimpleGraph.Walk.getVert_mem_support _ k)
    obtain ⟨z, hz, hzr⟩ := hwsup _ hmem'
    obtain ⟨l, hlz, hl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
    have hz' : Z.rep (p.getVert l) = (w.copy hreps hxfix).bypass.getVert k := by
      rw [hlz, hzr]
    exact hfix _ (hpD l hl) (hz' ▸ hmem)

/-! ## 4. The invariant of the synchronised phase -/

namespace DiamPath

variable {S : TreeState V}

/-- **The invariant of the synchronised phase**, with the quotient map `σ` explicit.

`T₁` and `T₂` are common quotients of `S` along `P` and `Q`; `σ : V → V` is the composite of the
synchronised folds performed so far (with `σ = id` initially), and the two states are described as
the images of `P.foldState`, `Q.foldState` under `σ`, with the same witness description of their
edges.  The fields `geod₁`, `geod₂` are the geodesic property of §1–§3, the fields `leg₁`, `leg₂`
say that the two legs `p 0, …, p r, q (ℓ+1), …, q D` and `p 0, …, p r, p (ℓ+1), …, p D` are still
paths, so that both diameters are at least `2r`; `sigma_*` records how `σ` behaves on `Δ`, on the
common part and on the spine. -/
structure SyncCtx (P Q : DiamPath S) (s : V) (T₁ T₂ : TreeState V) (σ : V → V) : Prop
    extends Phase1Inv P Q T₁ T₂ s where
  /-- the geodesic property of the first state -/
  geod₁ : GeodAvoid T₁ (P.Delta Q s) s
  /-- the geodesic property of the second state -/
  geod₂ : GeodAvoid T₂ (P.Delta Q s) s
  /-- the leg of the first state is still a path -/
  leg₁ : SeqPath T₁ (P.legSeq Q) (2 * (P.D - P.meetIdx Q))
  /-- the leg of the second state is still a path -/
  leg₂ : SeqPath T₂ (Q.legSeq P) (2 * (P.D - P.meetIdx Q))
  /-- the live vertices of the first state are the `σ`-images of `P.foldState` -/
  alive₁ : ∀ w : V, w ∈ T₁.alive ↔ ∃ v ∈ P.foldState.alive, σ v = w
  /-- the live vertices of the second state are the `σ`-images of `Q.foldState` -/
  alive₂ : ∀ w : V, w ∈ T₂.alive ↔ ∃ v ∈ Q.foldState.alive, σ v = w
  /-- the edges of the first state are the images of the edges of `P.foldState` -/
  adjdesc₁ : ∀ u v : V, T₁.graph.Adj u v ↔ u ≠ v ∧ u ∈ T₁.alive ∧ v ∈ T₁.alive ∧
    ∃ a b, P.foldState.graph.Adj a b ∧ σ a = u ∧ σ b = v
  /-- the edges of the second state are the images of the edges of `Q.foldState` -/
  adjdesc₂ : ∀ u v : V, T₂.graph.Adj u v ↔ u ≠ v ∧ u ∈ T₂.alive ∧ v ∈ T₂.alive ∧
    ∃ a b, Q.foldState.graph.Adj a b ∧ σ a = u ∧ σ b = v
  /-- `σ` is idempotent -/
  sigma_idem : ∀ v : V, σ (σ v) = σ v
  /-- `σ` fixes the difference region -/
  sigma_delta : ∀ v : V, v ∈ P.Delta Q s → σ v = v
  /-- `σ` maps the common part into itself -/
  sigma_common : ∀ v : V, v ∉ P.Delta Q s → σ v ∉ P.Delta Q s
  /-- `σ` fixes the common prefix `p 0, …, p r` -/
  sigma_spine : ∀ k : ℕ, k ≤ P.D - P.meetIdx Q → σ (P.seq k) = P.seq k

namespace SyncCtx

variable {P Q : DiamPath S} {T₁ T₂ : TreeState V} {s : V} {σ : V → V}

/-- A live vertex of the first state is a fixed point of `σ`. -/
theorem sigma_fix₁ (h : SyncCtx P Q s T₁ T₂ σ) {x : V} (hx : x ∈ T₁.alive) : σ x = x := by
  obtain ⟨v, -, hv⟩ := (h.alive₁ x).mp hx
  rw [← hv, h.sigma_idem]

/-- A live vertex of the second state is a fixed point of `σ`. -/
theorem sigma_fix₂ (h : SyncCtx P Q s T₁ T₂ σ) {x : V} (hx : x ∈ T₂.alive) : σ x = x := by
  obtain ⟨v, -, hv⟩ := (h.alive₂ x).mp hx
  rw [← hv, h.sigma_idem]

/-- **Distance agreement on the common part.**  A live vertex of the first state outside `Δ` is at
the same distance from `s` in the two states: the geodesic of the first state avoids `Δ` by
`geod₁`, and reading it in the second state (possible outside `Δ`, by `Phase1Inv`) gives a walk of
the same length. -/
theorem dist_eq_on_common (h : SyncCtx P Q s T₁ T₂ σ) {v : V} (hv : v ∈ T₁.alive)
    (hvΔ : v ∉ P.Delta Q s) : T₁.graph.dist s v = T₂.graph.dist s v :=
  h.geod₁.dist_eq h.adj_iff hv hvΔ

/-- The same statement on the second state. -/
theorem dist_eq_on_common' (h : SyncCtx P Q s T₁ T₂ σ) {v : V} (hv : v ∈ T₂.alive)
    (hvΔ : v ∉ P.Delta Q s) : T₁.graph.dist s v = T₂.graph.dist s v :=
  h.dist_eq_on_common ((h.mem_iff v hvΔ).mpr hv) hvΔ

/-- **The diameter bound of the difference region**, in the form used by the phase: a live vertex of
`Δ` is at distance at most `2r` from `s`, so a vertex at distance more than `2r` lies in the common
part. -/
theorem notMem_delta_of_lt_dist (h : SyncCtx P Q s T₁ T₂ σ) {H : ℕ}
    (hH : 2 * (P.D - P.meetIdx Q) < H) {z : V} (hz : z ∈ T₁.alive)
    (hzd : T₁.graph.dist s z = H) : z ∉ P.Delta Q s :=
  fun hmem => absurd (h.delta_bound₁ z hmem hz) (by omega)

/-- Same on the second state. -/
theorem notMem_delta_of_lt_dist' (h : SyncCtx P Q s T₁ T₂ σ) {H : ℕ}
    (hH : 2 * (P.D - P.meetIdx Q) < H) {z : V} (hz : z ∈ T₂.alive)
    (hzd : T₂.graph.dist s z = H) : z ∉ P.Delta Q s :=
  fun hmem => absurd (h.delta_bound₂ z hmem hz) (by omega)

/-- **The invariant holds initially**, with `σ = id`: this is the pair
`(P.foldState, Q.foldState)` where the geodesic property is `geod_fold`, the legs are the two
`legSeq` paths, and all the `σ`-fields are trivial. -/
theorem init (hP : P.p 0 = s) (hQ : Q.p 0 = s) (_hs : IsDiamEnd S s)
    (hr : 1 ≤ P.D - P.meetIdx Q) : SyncCtx P Q s P.foldState Q.foldState id := by
  have h0 : P.p 0 = Q.p 0 := hP.trans hQ.symm
  have hmeet : P.meetIdx Q = Q.meetIdx P := P.meetIdx_comm Q h0
  have hD : P.D = Q.D := P.D_eq Q
  have hr' : 1 ≤ Q.D - Q.meetIdx P := by omega
  have hleg₁ : SeqPath P.foldState (P.legSeq Q) (2 * (P.D - P.meetIdx Q)) :=
    ⟨fun k hk => P.legSeq_mem Q hP hQ hr hk, fun k hk => P.legSeq_adj Q hP hQ hr k hk,
      fun k hk l hl h => P.legSeq_inj Q hP hQ hr k hk l hl h⟩
  have hleg₂ : SeqPath Q.foldState (Q.legSeq P) (2 * (Q.D - Q.meetIdx P)) :=
    ⟨fun k hk => Q.legSeq_mem P hQ hP hr' hk, fun k hk => Q.legSeq_adj P hQ hP hr' k hk,
      fun k hk l hl h => Q.legSeq_inj P hQ hP hr' k hk l hl h⟩
  refine
    { toPhase1Inv := P.phase1Inv_fold_of_dist_eq Q hP hQ fun v hv hvA =>
        P.dist_eq_on_common Q hP hQ hv hvA
      geod₁ := P.geod_fold Q hP hQ
      geod₂ := ?_
      leg₁ := hleg₁
      leg₂ := ?_
      alive₁ := ?_
      alive₂ := ?_
      adjdesc₁ := ?_
      adjdesc₂ := ?_
      sigma_idem := ?_
      sigma_delta := ?_
      sigma_common := ?_
      sigma_spine := ?_ }
  · rw [P.Delta_comm Q s h0]
    exact Q.geod_fold P hQ hP
  · rw [show 2 * (P.D - P.meetIdx Q) = 2 * (Q.D - Q.meetIdx P) by omega]
    exact hleg₂
  · intro w
    exact ⟨fun h => ⟨w, h, rfl⟩, fun ⟨v, hv, hvw⟩ => by rw [← hvw]; exact hv⟩
  · intro w
    exact ⟨fun h => ⟨w, h, rfl⟩, fun ⟨v, hv, hvw⟩ => by rw [← hvw]; exact hv⟩
  · intro u v
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, u, v, h, rfl, rfl⟩, fun h => by
      obtain ⟨-, -, -, a, b, hab, hau, hbv⟩ := h
      simp only [id_eq] at hau hbv
      subst hau
      subst hbv
      exact hab⟩
  · intro u v
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, u, v, h, rfl, rfl⟩, fun h => by
      obtain ⟨-, -, -, a, b, hab, hau, hbv⟩ := h
      simp only [id_eq] at hau hbv
      subst hau
      subst hbv
      exact hab⟩
  · intro v
    rfl
  · intro v _
    rfl
  · intro v hv
    simpa using hv
  · intro k _
    rfl

/-- **Obligation 4.3 (the synchronised step).**  A diameter path of the first state starting at `s`
whose vertices avoid the difference region `Δ` is *also* a diameter path of the second state, with
the same vertices: outside `Δ` the two states have the same live vertices and the same edges, and
distances from `s` agree there.  Folding both states along it is therefore a single synchronised
step of the phase. -/
theorem sync_diamPath (h : SyncCtx P Q s T₁ T₂ σ) (Z : DiamPath T₁) (hZs : Z.p 0 = s)
    (hZΔ : ∀ i, Z.p i ∉ P.Delta Q s) :
    ∃ Z₂ : DiamPath T₂, ∃ _hD : Z₂.D = Z.D,
      ∀ i : Fin (Z.D + 1), Z₂.p (Fin.cast (by omega) i) = Z.p i := by
  have hdist : T₁.graph.dist s (Z.p ⟨Z.D, Nat.lt_succ_self _⟩) = T₁.diam := by
    simpa [hZs] using Z.isDiam
  have hdiam : T₂.graph.dist s (Z.p ⟨Z.D, Nat.lt_succ_self _⟩) = T₂.diam := by
    rw [← h.dist_eq_on_common (Z.mem ⟨Z.D, Nat.lt_succ_self _⟩)
      (hZΔ ⟨Z.D, Nat.lt_succ_self _⟩), hdist, h.diam_eq]
  refine ⟨DiamPath.mk Z.D Z.p ?_ Z.inj ?_ ?_, rfl, ?_⟩
  · intro i
    exact (h.mem_iff _ (hZΔ i)).mp (Z.mem i)
  · intro i
    exact (h.adj_iff _ _ (hZΔ _) (hZΔ _)).mp (Z.adj i)
  · simpa [hZs] using hdiam
  · intro i
    rfl

end SyncCtx

end DiamPath

end OhtoaiTreeProof

/-! ## 5. Completion downstream

`SyncStep.lean` proves `SyncCtx.step` and `SyncCtx.reach_scale`, preserving this invariant without
adding fields. `SyncEndgame.lean` proves `legAt_rep_comp` and `SyncCtx.commonEndgame`, then assembles
`DiamPath.synchronized_exchange`.

The endgame does not require a commutation identity between a synchronized fold and an endgame
fold. Instead it compares the two composite maps on each original vertex. Outside the tail set
the initial representatives agree; their common image is either in the common part (which both
endgame maps fix) or is an off-path vertex in the difference region (fixed by all maps). A tail
vertex has one representative on the spine and one on the surviving tail, both fixed by `σ`;
the appropriate endgame fold identifies them. The existing fields of `SyncCtx` suffice.
-/
