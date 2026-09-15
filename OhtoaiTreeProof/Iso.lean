/-
# Isomorphism invariance of the folding process

This file formalizes the missing ingredient of `REF.md` Proposition 2
(`OhtoaiTreeProof.LValue_endpoint_independent`): the folding process is invariant under an
isomorphism of states, so that folding a diameter towards one of its endpoints gives the same
abstract quotient tree as folding it towards the other endpoint.

The main pieces are

* `StateIso` — two states are isomorphic when a permutation of the ambient type preserves
  liveness and adjacency (part 1);
* the basic theory of `StateIso`: composition, distance preservation (`StateIso.dist_eq`),
  diameter preservation (`StateIso.diam_eq`), transport of `IsDiamEnd`, and the transport of an
  arbitrary state along an isomorphism (`StateIso.transportState`);
* `DiamPath.transport` and the commutation of the folding map with the isomorphism
  (`DiamPath.rep_transport`), which gives the invariance of the folding process
  (`StateIso.foldStepAt`, `StateIso.foldSeqAt`, `StateIso.lValue_iff`) (part 2);
* the reversed diameter and `exists_stateIso_foldState_reverse` (part 3).
-/
import OhtoaiTreeProof.Cone
import OhtoaiTreeProof.PathExists

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Isomorphic states -/

/-- Two states are isomorphic when a permutation of the ambient type preserves liveness and
adjacency. -/
structure StateIso (S S' : TreeState V) where
  /-- the permutation of the ambient type -/
  e : V ≃ V
  /-- it preserves the set of live vertices -/
  alive_iff : ∀ v : V, v ∈ S.alive ↔ e v ∈ S'.alive
  /-- it preserves adjacency -/
  adj_iff : ∀ u v : V, S.graph.Adj u v ↔ S'.graph.Adj (e u) (e v)

namespace StateIso

variable {S S₁ S₂ S₃ : TreeState V}

/-! ### Composition -/

/-- The identity isomorphism of a state. -/
protected def refl (S : TreeState V) : StateIso S S where
  e := Equiv.refl V
  alive_iff := fun _ => Iff.rfl
  adj_iff := fun _ _ => Iff.rfl

/-- The inverse of an isomorphism of states. -/
protected def symm (h : StateIso S S₁) : StateIso S₁ S where
  e := h.e.symm
  alive_iff := fun v => by
    exact ((h.alive_iff (h.e.symm v)).trans (iff_of_eq (by rw [Equiv.apply_symm_apply]))).symm
  adj_iff := fun u v => by
    have h1 : S₁.graph.Adj u v ↔ S.graph.Adj (h.e.symm u) (h.e.symm v) := by
      rw [h.adj_iff (h.e.symm u) (h.e.symm v), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact h1

/-- The composite of two isomorphisms of states. -/
protected def trans (h₁ : StateIso S₁ S₂) (h₂ : StateIso S₂ S₃) : StateIso S₁ S₃ where
  e := h₁.e.trans h₂.e
  alive_iff := fun v => (h₁.alive_iff v).trans (h₂.alive_iff (h₁.e v))
  adj_iff := fun u v => (h₁.adj_iff u v).trans (h₂.adj_iff (h₁.e u) (h₁.e v))

@[simp] theorem symm_e (h : StateIso S S₁) : h.symm.e = h.e.symm := rfl

@[simp] theorem refl_e (S : TreeState V) : (StateIso.refl S).e = Equiv.refl V := rfl

theorem trans_e (h₁ : StateIso S₁ S₂) (h₂ : StateIso S₂ S₃) :
    (h₁.trans h₂).e = h₁.e.trans h₂.e := rfl

/-! ### The underlying graph isomorphism -/

/-- The graph isomorphism underlying an isomorphism of states. -/
noncomputable def graphIso (h : StateIso S S₁) : S.graph ≃g S₁.graph where
  toEquiv := h.e
  map_rel_iff' := fun {a b} => (h.adj_iff a b).symm

/-- The graph homomorphism underlying an isomorphism of states. -/
noncomputable def graphHom (h : StateIso S S₁) : S.graph →g S₁.graph :=
  h.graphIso.toHom

@[simp] theorem graphHom_apply (h : StateIso S S₁) (v : V) : h.graphHom v = h.e v := rfl

/-! ### Distance preservation -/

/-- The underlying graph homomorphism of the inverse. -/
noncomputable def symmGraphHom (h : StateIso S S₁) : S₁.graph →g S.graph :=
  h.symm.graphHom

/-- **An isomorphism of states preserves reachability.** -/
theorem reachable_iff (h : StateIso S S₁) (u v : V) :
    S.graph.Reachable u v ↔ S₁.graph.Reachable (h.e u) (h.e v) := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.map h.graphHom⟩
  · rintro ⟨w⟩
    refine ⟨(w.map h.symm.graphHom).copy ?_ ?_⟩
    · exact Equiv.symm_apply_apply h.e u
    · exact Equiv.symm_apply_apply h.e v

/-- An isomorphism of states does not increase distances (the image of a shortest walk is a walk
of the same length). -/
theorem dist_le_dist (h : StateIso S S₁) (u v : V) :
    S₁.graph.dist (h.e u) (h.e v) ≤ S.graph.dist u v := by
  by_cases hr : S.graph.Reachable u v
  · obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
    calc S₁.graph.dist (h.e u) (h.e v) ≤ (w.map h.graphHom).length := SimpleGraph.dist_le _
      _ = w.length := Walk.length_map h.graphHom w
      _ = S.graph.dist u v := hw
  · have hr' : ¬ S₁.graph.Reachable (h.e u) (h.e v) := by rwa [← h.reachable_iff]
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hr',
      SimpleGraph.dist_eq_zero_of_not_reachable hr]

/-- **An isomorphism of states preserves distances.** -/
theorem dist_eq (h : StateIso S S₁) (u v : V) :
    S.graph.dist u v = S₁.graph.dist (h.e u) (h.e v) := by
  refine le_antisymm ?_ (h.dist_le_dist u v)
  have := h.symm.dist_le_dist (h.e u) (h.e v)
  simpa using this

/-! ### Cardinality of the live set -/

/-- An isomorphism of states maps the live vertices onto the live vertices. -/
theorem alive_map (h : StateIso S S₁) : S.alive.map h.e.toEmbedding = S₁.alive := by
  ext v
  rw [Finset.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (h.alive_iff w).mp hw
  · intro hv
    exact ⟨h.e.symm v, (h.alive_iff (h.e.symm v)).mpr (by simpa using hv), by simp⟩

/-- An isomorphism of states preserves the number of live vertices. -/
theorem card_eq (h : StateIso S S₁) : S.alive.card = S₁.alive.card := by
  rw [← h.alive_map, Finset.card_map]

/-- An isomorphism of states preserves the diameter. -/
theorem diam_le (h : StateIso S S₁) : S.diam ≤ S₁.diam := by
  refine Finset.sup_le fun u hu => Finset.sup_le fun v hv => ?_
  calc S.graph.dist u v = S₁.graph.dist (h.e u) (h.e v) := h.dist_eq u v
    _ ≤ S₁.diam := S₁.dist_le_diam ((h.alive_iff u).mp hu) ((h.alive_iff v).mp hv)

/-- **An isomorphism of states preserves the diameter.** -/
theorem diam_eq (h : StateIso S S₁) : S.diam = S₁.diam :=
  le_antisymm h.diam_le h.symm.diam_le

/-! ### Diameter endpoints -/

/-- **An isomorphism of states preserves diameter endpoints.** -/
theorem isDiamEnd_iff (h : StateIso S S₁) (s : V) :
    IsDiamEnd S s ↔ IsDiamEnd S₁ (h.e s) := by
  constructor
  · rintro ⟨hs, y, hy, hd⟩
    exact ⟨(h.alive_iff s).mp hs, h.e y, (h.alive_iff y).mp hy, by
      rw [← h.dist_eq s y, hd, h.diam_eq]⟩
  · rintro ⟨hs, y, hy, hd⟩
    refine ⟨(h.alive_iff s).mpr hs, h.e.symm y, ?_, ?_⟩
    · exact (h.alive_iff (h.e.symm y)).mpr (by simpa using hy)
    · have h1 : S.graph.dist s (h.e.symm y) = S₁.graph.dist (h.e s) y := by
        simpa using h.dist_eq s (h.e.symm y)
      rw [h1, hd, h.diam_eq]

/-! ### Transporting a state along an isomorphism -/

/-- The graph isomorphism `T.graph ≃g T.graph.map h.e`. -/
noncomputable def mapIso (h : StateIso S S₁) (T : TreeState V) :
    T.graph ≃g T.graph.map h.e.toEmbedding where
  toEquiv := h.e
  map_rel_iff' := by
    intro a b
    rw [SimpleGraph.map_adj]
    constructor
    · rintro ⟨a', b', hab, ha, hb⟩
      rwa [h.e.injective ha, h.e.injective hb] at hab
    · intro hab
      exact ⟨a, b, hab, rfl, rfl⟩

/-- The graph homomorphism `T.graph →g T.graph.map h.e`. -/
noncomputable def mapHom (h : StateIso S S₁) (T : TreeState V) :
    T.graph →g T.graph.map h.e.toEmbedding :=
  (h.mapIso T).toHom

/-- **Transport of a state along an isomorphism**: the state obtained from `T` by renaming its
vertices along `h.e`. -/
noncomputable def transportState (h : StateIso S S₁) (T : TreeState V) : TreeState V where
  alive := T.alive.map h.e.toEmbedding
  graph := T.graph.map h.e.toEmbedding
  adj_alive := by
    intro u v huv
    rw [SimpleGraph.map_adj] at huv
    obtain ⟨a, b, hab, ha, hb⟩ := huv
    refine ⟨?_, ?_⟩
    · rw [← ha]; exact Finset.mem_map.mpr ⟨a, (T.adj_alive hab).1, rfl⟩
    · rw [← hb]; exact Finset.mem_map.mpr ⟨b, (T.adj_alive hab).2, rfl⟩
  connected := by
    intro u hu v hv
    rw [Finset.mem_map] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    obtain ⟨w⟩ := T.connected a ha b hb
    exact ⟨w.map (h.mapHom T)⟩
  acyclic := (h.mapIso T).isAcyclic_iff.mp T.acyclic

/-- **A state is isomorphic to its transport along an isomorphism.** -/
noncomputable def transportState_iso (h : StateIso S S₁) (T : TreeState V) :
    StateIso T (h.transportState T) where
  e := h.e
  alive_iff := fun v => by
    show v ∈ T.alive ↔ h.e.toEmbedding v ∈ T.alive.map h.e.toEmbedding
    simp
  adj_iff := fun u v => by
    show T.graph.Adj u v ↔ (T.graph.map h.e.toEmbedding).Adj (h.e u) (h.e v)
    exact ((h.mapIso T).map_adj_iff (v := u) (w := v)).symm

end StateIso

/-! ## 2. Invariance of the folding process -/

namespace DiamPath

variable {S S' : TreeState V}

/-- **Transport of a diameter path along an isomorphism of states.** -/
noncomputable def transport (h : StateIso S S') (P : DiamPath S) : DiamPath S' where
  D := P.D
  p := fun i => h.e (P.p i)
  mem := fun i => (h.alive_iff (P.p i)).mp (P.mem i)
  inj := fun i j hij => P.inj (h.e.injective hij)
  adj := fun i => (h.adj_iff _ _).mp (P.adj i)
  isDiam := by
    show S'.graph.dist (h.e (P.p 0)) (h.e (P.p P.last)) = S'.diam
    rw [← h.dist_eq, show S.graph.dist (P.p 0) (P.p P.last) = S.diam from P.isDiam, h.diam_eq]

@[simp] theorem transport_D (h : StateIso S S') (P : DiamPath S) :
    (P.transport h).D = P.D := rfl

@[simp] theorem transport_p (h : StateIso S S') (P : DiamPath S) (i : Fin (P.D + 1)) :
    (P.transport h).p i = h.e (P.p i) := rfl

/-- The folding map of the transported path, on the diameter. -/
theorem transport_rep_path (h : StateIso S S') (P : DiamPath S) (i : Fin (P.D + 1)) :
    (P.transport h).rep (h.e (P.p i)) =
      h.e (P.p ⟨min (i : ℕ) (P.D - (i : ℕ)), by have := i.isLt; omega⟩) :=
  ((show (P.transport h).rep (h.e (P.p i)) =
      (P.transport h).rep ((P.transport h).p i) from rfl).trans
    ((P.transport h).rep_path i)).trans rfl

/-- **The folding map commutes with the isomorphism.**  This is the key computation: the canonical
representative of the image of a vertex is the image of its canonical representative. -/
theorem rep_transport (h : StateIso S S') (P : DiamPath S) (v : V) :
    h.e (P.rep v) = (P.transport h).rep (h.e v) := by
  by_cases hv : ∃ i, P.p i = v
  · obtain ⟨i, rfl⟩ := hv
    rw [P.rep_path, P.transport_rep_path h i]
  · have hv' : ∀ i, P.p i ≠ v := fun i hi => hv ⟨i, hi⟩
    have h2 : (P.transport h).rep (h.e v) = h.e v := by
      rw [(P.transport h).rep_eq_self]
      intro i hi
      exact hv' i (h.e.injective hi)
    rw [P.rep_eq_self hv', h2]

/-- The live vertices of the folded tree are transported to the live vertices of the transported
folded tree. -/
theorem mem_foldAlive_transport (h : StateIso S S') (P : DiamPath S) (v : V) :
    v ∈ P.foldAlive ↔ h.e v ∈ (P.transport h).foldAlive := by
  simp only [mem_foldAlive]
  constructor
  · rintro ⟨hv, hfix⟩
    exact ⟨(h.alive_iff v).mp hv, by rw [← P.rep_transport h v, hfix]⟩
  · rintro ⟨hv, hfix⟩
    refine ⟨(h.alive_iff v).mpr hv, ?_⟩
    rw [← P.rep_transport h v] at hfix
    exact h.e.injective hfix

/-- Adjacency of the folded graph is transported along the isomorphism. -/
theorem foldGraph_adj_transport (h : StateIso S S') (P : DiamPath S) (u v : V) :
    P.foldGraph.Adj u v ↔ (P.transport h).foldGraph.Adj (h.e u) (h.e v) := by
  rw [foldGraph_adj, foldGraph_adj]
  constructor
  · rintro ⟨hne, hu, hv, x, y, hxy, hx, hy⟩
    exact ⟨fun hh => hne (h.e.injective hh), (P.mem_foldAlive_transport h u).mp hu,
      (P.mem_foldAlive_transport h v).mp hv, h.e x, h.e y, (h.adj_iff x y).mp hxy,
      by rw [← P.rep_transport h x, hx], by rw [← P.rep_transport h y, hy]⟩
  · rintro ⟨hne, hu, hv, x, y, hxy, hx, hy⟩
    refine ⟨fun hh => hne (congrArg h.e hh), (P.mem_foldAlive_transport h u).mpr hu,
      (P.mem_foldAlive_transport h v).mpr hv, h.e.symm x, h.e.symm y,
      (h.adj_iff (h.e.symm x) (h.e.symm y)).mpr (by simpa using hxy), ?_, ?_⟩
    · have h3 := P.rep_transport h (h.e.symm x)
      simp only [Equiv.apply_symm_apply] at h3
      rw [hx] at h3
      exact h.e.injective h3
    · have h3 := P.rep_transport h (h.e.symm y)
      simp only [Equiv.apply_symm_apply] at h3
      rw [hy] at h3
      exact h.e.injective h3

/-- **The folded states of isomorphic states are isomorphic.** -/
noncomputable def foldState_iso (h : StateIso S S') (P : DiamPath S) :
    StateIso P.foldState (P.transport h).foldState where
  e := h.e
  alive_iff := fun v => P.mem_foldAlive_transport h v
  adj_iff := fun u v => P.foldGraph_adj_transport h u v

end DiamPath

namespace StateIso

variable {S S' : TreeState V}

/-- **Invariance of the folding step.** -/
theorem foldStepAt (h : StateIso S S') {s : V} {S₁ : TreeState V} (hs : FoldStepAt s S S₁) :
    ∃ S₁' : TreeState V, FoldStepAt (h.e s) S' S₁' ∧ ∃ g : StateIso S₁ S₁', g.e = h.e := by
  obtain ⟨P, hP, rfl⟩ := hs
  refine ⟨(P.transport h).foldState, ⟨P.transport h, ?_, rfl⟩, P.foldState_iso h, rfl⟩
  show h.e (P.p 0) = h.e s
  rw [hP]

/-- **Invariance of the folding sequence.** -/
theorem foldSeqAt (h : StateIso S S') {s : V} {S₁ : TreeState V} {n : ℕ}
    (hs : FoldSeqAt s S S₁ n) :
    ∃ S₁' : TreeState V, FoldSeqAt (h.e s) S' S₁' n ∧ ∃ g : StateIso S₁ S₁', g.e = h.e := by
  induction hs generalizing S' with
  | refl _ => exact ⟨S', FoldSeqAt.refl S', h, rfl⟩
  | step hpos hstep hrest ih =>
      obtain ⟨U, hU, g, hg⟩ := h.foldStepAt hstep
      obtain ⟨W, hW, g', hg'⟩ := ih (S' := U) g
      rw [hg] at hW
      exact ⟨W, FoldSeqAt.step (by rw [← h.card_eq]; exact hpos) hU hW, g', hg'.trans hg⟩

/-- **Invariance of the value of the fixed-endpoint process.** -/
theorem lValue_imp (h : StateIso S S') {s : V} {n : ℕ} (hl : LValue S s n) :
    LValue S' (h.e s) n := by
  obtain ⟨S₁, hseq, hsingle⟩ := hl
  obtain ⟨S₁', hseq', g, -⟩ := h.foldSeqAt hseq
  refine ⟨S₁', hseq', ?_⟩
  show S₁'.alive.card ≤ 1
  rw [← g.card_eq]
  exact hsingle

/-- **Invariance of `LValue`.** -/
theorem lValue_iff (h : StateIso S S') (s : V) (n : ℕ) :
    LValue S s n ↔ LValue S' (h.e s) n := by
  constructor
  · intro hl
    exact h.lValue_imp hl
  · intro hl
    have h2 := h.symm.lValue_imp hl
    simpa using h2

end StateIso

/-! ## 3. Folding towards the two ends of a diameter -/

namespace DiamPath

variable {S : TreeState V}

/-- The reversed diameter path: `p_rev i = P.p (rev i)`, so that it starts at `P.p P.last`. -/
noncomputable def reverse (P : DiamPath S) : DiamPath S where
  D := P.D
  p := fun i => P.p (Fin.rev i)
  mem := fun i => P.mem (Fin.rev i)
  inj := fun _ _ hij => Fin.rev_injective (P.inj hij)
  adj := fun i => by
    show S.graph.Adj (P.p (Fin.rev (Fin.castSucc i))) (P.p (Fin.rev (Fin.succ i)))
    rw [Fin.rev_castSucc, Fin.rev_succ]
    exact (P.adj (Fin.rev i)).symm
  isDiam := by
    show S.graph.dist (P.p (Fin.rev (0 : Fin (P.D + 1)))) (P.p (Fin.rev (Fin.last P.D))) = S.diam
    rw [Fin.rev_zero, Fin.rev_last, SimpleGraph.dist_comm]
    exact show S.graph.dist (P.p 0) (P.p (Fin.last P.D)) = S.diam from P.isDiam

@[simp] theorem reverse_D (P : DiamPath S) : (P.reverse).D = P.D := rfl

@[simp] theorem reverse_p (P : DiamPath S) (i : Fin ((P.reverse).D + 1)) :
    P.reverse.p i = P.p (Fin.rev i) := rfl

/-- The first vertex of the reversed path is the last vertex of the path. -/
theorem reverse_p_zero (P : DiamPath S) : P.reverse.p 0 = P.p P.last := by
  show P.p (Fin.rev (0 : Fin (P.D + 1))) = P.p P.last
  rw [Fin.rev_zero]
  rfl

/-- The order-reversing permutation of the diameter, extended by the identity outside it. -/
noncomputable def reflect (P : DiamPath S) (v : V) : V :=
  match P.index v with
  | some i => P.p (Fin.rev i)
  | none => v

theorem reflect_of_index_eq_some (P : DiamPath S) {v : V} {i : Fin (P.D + 1)}
    (h : P.index v = some i) : P.reflect v = P.p (Fin.rev i) := by
  simp only [reflect, h]

theorem reflect_of_index_eq_none (P : DiamPath S) {v : V} (h : P.index v = none) :
    P.reflect v = v := by
  simp only [reflect, h]

/-- A vertex of the diameter is moved to its mirror image. -/
theorem reflect_path (P : DiamPath S) (i : Fin (P.D + 1)) :
    P.reflect (P.p i) = P.p (Fin.rev i) :=
  P.reflect_of_index_eq_some (P.index_eq_some rfl)

/-- The reflection map is an involution. -/
theorem reflect_involutive (P : DiamPath S) : Function.Involutive P.reflect := by
  intro v
  rcases hv : P.index v with _ | i
  · rw [P.reflect_of_index_eq_none hv, P.reflect_of_index_eq_none hv]
  · rw [P.reflect_of_index_eq_some hv, P.reflect_path, Fin.rev_rev, ← P.eq_of_index_eq_some hv]

/-- The reflection map preserves liveness. -/
theorem reflect_mem_alive (P : DiamPath S) (v : V) : P.reflect v ∈ S.alive ↔ v ∈ S.alive := by
  rcases hv : P.index v with _ | i
  · rw [P.reflect_of_index_eq_none hv]
  · rw [P.reflect_of_index_eq_some hv, ← P.eq_of_index_eq_some hv]
    exact ⟨fun _ => P.mem i, fun _ => P.mem (Fin.rev i)⟩

/-- The reflection map as a permutation of the ambient type. -/
noncomputable def reflectEquiv (P : DiamPath S) : V ≃ V :=
  Equiv.ofBijective P.reflect P.reflect_involutive.bijective

@[simp] theorem reflectEquiv_apply (P : DiamPath S) (v : V) : P.reflectEquiv v = P.reflect v := rfl

/-- If a vertex does not occur on the diameter then it is different from all `P.p i`. -/
theorem index_eq_none_iff (P : DiamPath S) {v : V} : P.index v = none ↔ ∀ i, P.p i ≠ v := by
  refine ⟨fun h i hi => ?_, P.index_eq_none⟩
  have h2 := P.index_eq_some hi
  rw [h] at h2
  exact absurd h2 (by simp)

/-- Folding along the reversed diameter, on the diameter: the canonical representative of `p i` is
the mirror image of `p (D - i)`'s representative. -/
theorem reverse_rep_path (P : DiamPath S) (i : Fin (P.D + 1)) :
    P.reverse.rep (P.p (Fin.rev i)) =
      P.p (Fin.rev ⟨min (i : ℕ) (P.D - (i : ℕ)), by have := i.isLt; omega⟩) :=
  P.reverse.rep_path i

/-- The reflection map does not change the canonical representative. -/
theorem rep_reflect (P : DiamPath S) (v : V) : P.rep (P.reflect v) = P.rep v := by
  rcases hv : P.index v with _ | i
  · rw [P.reflect_of_index_eq_none hv]
  · rw [P.reflect_of_index_eq_some hv, ← P.eq_of_index_eq_some hv, P.rep_path, P.rep_path]
    congr 1
    exact Fin.ext (by simp only [Fin.val_rev]; omega)

/-- **The folding map of the reversed diameter.**  The canonical representative of a vertex for the
reversed diameter is the mirror image of its representative for the original diameter. -/
theorem reverse_rep (P : DiamPath S) (v : V) : P.reverse.rep v = P.reflect (P.rep v) := by
  rcases hv : P.index v with _ | i
  · have hv' : ∀ k, P.p k ≠ v := P.index_eq_none_iff.mp hv
    rw [P.rep_eq_self hv', P.reflect_of_index_eq_none hv]
    refine P.reverse.rep_eq_self (fun k hk => ?_)
    exact hv' (Fin.rev k) (by rw [← hk]; rfl)
  · rw [← P.eq_of_index_eq_some hv, P.rep_path, P.reflect_path,
      show P.p i = P.p (Fin.rev (Fin.rev i)) from by rw [Fin.rev_rev],
      P.reverse_rep_path (Fin.rev i)]
    congr 1
    exact Fin.ext (by simp only [Fin.val_rev]; omega)

/-- The live vertices of the folded tree are the mirror images of the live vertices of the
folding along the reversed diameter. -/
theorem mem_foldAlive_reverse (P : DiamPath S) (v : V) :
    v ∈ P.foldAlive ↔ P.reflect v ∈ P.reverse.foldAlive := by
  simp only [mem_foldAlive]
  constructor
  · rintro ⟨hv, hfix⟩
    exact ⟨(P.reflect_mem_alive v).mpr hv, by rw [P.reverse_rep, P.rep_reflect, hfix]⟩
  · rintro ⟨hv, hfix⟩
    refine ⟨(P.reflect_mem_alive v).mp hv, ?_⟩
    rw [P.reverse_rep, P.rep_reflect] at hfix
    exact P.reflect_involutive.injective hfix

/-- Adjacency of the folded graph is transported by the reflection map. -/
theorem foldGraph_adj_reverse (P : DiamPath S) (u v : V) :
    P.foldGraph.Adj u v ↔ P.reverse.foldGraph.Adj (P.reflect u) (P.reflect v) := by
  rw [foldGraph_adj, foldGraph_adj]
  constructor
  · rintro ⟨hne, hu, hv, x, y, hxy, hx, hy⟩
    exact ⟨fun hh => hne (P.reflect_involutive.injective hh),
      (P.mem_foldAlive_reverse u).mp hu, (P.mem_foldAlive_reverse v).mp hv, x, y, hxy,
      by rw [P.reverse_rep, hx], by rw [P.reverse_rep, hy]⟩
  · rintro ⟨hne, hu, hv, x, y, hxy, hx, hy⟩
    refine ⟨fun hh => hne (congrArg P.reflect hh), (P.mem_foldAlive_reverse u).mpr hu,
      (P.mem_foldAlive_reverse v).mpr hv, x, y, hxy, ?_, ?_⟩
    · rw [P.reverse_rep] at hx
      exact P.reflect_involutive.injective hx
    · rw [P.reverse_rep] at hy
      exact P.reflect_involutive.injective hy

/-- **Folding along a diameter and folding along the reversed diameter give isomorphic states.**
The isomorphism is the reflection map of the diameter, extended by the identity outside it. -/
noncomputable def foldState_iso_reverse (P : DiamPath S) :
    StateIso P.foldState P.reverse.foldState where
  e := P.reflectEquiv
  alive_iff := fun v => P.mem_foldAlive_reverse v
  adj_iff := fun u v => P.foldGraph_adj_reverse u v

end DiamPath

/-- **The formal counterpart of `REF.md` Proposition 2.**  Folding along a diameter towards one of
its endpoints and folding along the same diameter towards the other endpoint give the same abstract
quotient tree: there is an isomorphism of the two folded states carrying `P.p 0` to `P.p P.last`. -/
theorem exists_stateIso_foldState_reverse {S : TreeState V} (P : DiamPath S) :
    ∃ h : StateIso P.foldState P.reverse.foldState, h.e (P.p 0) = P.p P.last :=
  ⟨P.foldState_iso_reverse, by
    show P.reflect (P.p 0) = P.p P.last
    rw [P.reflect_path, Fin.rev_zero]
    rfl⟩

/-- **The two ends of a diameter behave in the same way.**  Folding along the diameter `P` towards
its first endpoint `P.p 0` and folding along the same diameter towards its last endpoint
`P.p P.last` give states with the same complete folding lengths; this is the statement that
`REF.md` Proposition 2 uses. -/
theorem lValue_foldState_reverse {S : TreeState V} (P : DiamPath S) (n : ℕ) :
    LValue P.foldState (P.p 0) n ↔ LValue P.reverse.foldState (P.p P.last) n := by
  obtain ⟨h, hh⟩ := exists_stateIso_foldState_reverse P
  have h2 := h.lValue_iff (P.p 0) n
  rwa [hh] at h2

end OhtoaiTreeProof

/-! ## Axiom usage

Nothing in this file uses `sorry`, `axiom`, `native_decide` or `set_option maxHeartbeats`; the
following commands record the axioms the main results actually depend on (only the three standard
axioms of Lean/Mathlib, no `sorryAx`). -/
#print axioms OhtoaiTreeProof.StateIso.lValue_iff
#print axioms OhtoaiTreeProof.StateIso.foldSeqAt
#print axioms OhtoaiTreeProof.exists_stateIso_foldState_reverse
#print axioms OhtoaiTreeProof.lValue_foldState_reverse
