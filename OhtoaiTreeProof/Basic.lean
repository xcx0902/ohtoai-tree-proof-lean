/-
# Folding a tree along a diameter: definitions

This file sets up the combinatorial data of the folding process described in `REF.md`.

A **state** of the process is a tree whose vertex set is a finite subset `alive` of a fixed
ambient type `V` (the vertices outside `alive` are isolated).  Describing every tree occurring in
the process as a graph on the *same* type `V` lets us iterate the process without ever changing
the vertex type, which is what makes the statement "the number of operations is fixed" expressible
as a statement about a relation `FoldSeq` on states.

A chosen diameter of a state is recorded as a `DiamPath`: a list `p 0, …, p D` of vertices of
the state such that consecutive members are adjacent, the list is injective, and the two
endpoints are at distance `diam` from each other.

The folding operation is `DiamPath.foldState`.  It identifies the mirror-image vertices `p i`
and `p (D - i)` of the chosen diameter.  This is implemented through the canonical representative
map `DiamPath.rep` (which sends `p i` to `p (min i (D - i))` and fixes every other vertex), so
that the folded graph can again be written as a graph on `V`.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

-- The counting argument of `REF.md` §2 uses `SimpleGraph.fintypeEdgeSet`, whose `DecidableRel`
-- argument is supplied by classical logic.
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## States of the process -/

/-- A state of the folding process: a tree whose vertices are the elements of a finset
`alive`, all other vertices of the ambient type being isolated. -/
structure TreeState (V : Type*) [Fintype V] where
  /-- the vertices of the tree -/
  alive : Finset V
  /-- the graph, whose edges all join vertices of `alive` -/
  graph : SimpleGraph V
  /-- every edge joins two vertices of `alive` -/
  adj_alive : ∀ ⦃u v : V⦄, graph.Adj u v → u ∈ alive ∧ v ∈ alive
  /-- any two vertices of `alive` are joined by a walk -/
  connected : ∀ u ∈ alive, ∀ v ∈ alive, graph.Reachable u v
  /-- the graph has no cycle -/
  acyclic : graph.IsAcyclic

namespace TreeState

variable (S : TreeState V)

theorem adj_alive_left {u v : V} (h : S.graph.Adj u v) : u ∈ S.alive := (S.adj_alive h).1

theorem adj_alive_right {u v : V} (h : S.graph.Adj u v) : v ∈ S.alive := (S.adj_alive h).2

/-- In a state, two live vertices at distance zero are equal. -/
theorem dist_eq_zero_iff {u v : V} (hu : u ∈ S.alive) (hv : v ∈ S.alive) :
    S.graph.dist u v = 0 ↔ u = v :=
  (S.connected u hu v hv).dist_eq_zero_iff

/-- The *diameter* of a state: the largest distance between two of its vertices. -/
noncomputable def diam : ℕ :=
  S.alive.sup fun u => S.alive.sup fun v => S.graph.dist u v

theorem dist_le_diam {u v : V} (hu : u ∈ S.alive) (hv : v ∈ S.alive) :
    S.graph.dist u v ≤ S.diam :=
  le_trans (Finset.le_sup (f := fun v => S.graph.dist u v) hv)
    (Finset.le_sup (f := fun u => S.alive.sup fun v => S.graph.dist u v) hu)

/-- The diameter of a nonempty state is attained. -/
theorem exists_dist_eq_diam (h : S.alive.Nonempty) :
    ∃ u ∈ S.alive, ∃ v ∈ S.alive, S.graph.dist u v = S.diam := by
  obtain ⟨u, hu, hu'⟩ := Finset.exists_mem_eq_sup S.alive h
    (fun u => S.alive.sup fun v => S.graph.dist u v)
  obtain ⟨v, hv, hv'⟩ := Finset.exists_mem_eq_sup S.alive h (fun v => S.graph.dist u v)
  exact ⟨u, hu, v, hv, by rw [diam, hu', hv']⟩

end TreeState

/-! ## Diameters -/

/-- A *diameter* of a state, listed from one endpoint to the other.

`D` is the number of edges of the path, so that the path has `D + 1` vertices
`p 0, …, p D`. -/
structure DiamPath (S : TreeState V) where
  /-- number of edges of the diameter -/
  D : ℕ
  /-- the vertices of the diameter, in order -/
  p : Fin (D + 1) → V
  /-- all vertices of the diameter are live -/
  mem : ∀ i, p i ∈ S.alive
  /-- the diameter has no repeated vertex -/
  inj : Function.Injective p
  /-- consecutive vertices of the diameter are adjacent -/
  adj : ∀ i : Fin D, S.graph.Adj (p i.castSucc) (p i.succ)
  /-- the two endpoints are at distance exactly `diam` -/
  isDiam : S.graph.dist (p 0) (p ⟨D, Nat.lt_succ_self D⟩) = S.diam


/-! ## Two elementary walk lemmas -/

/-- A vertex of an edge of the graph belongs to the support of the graph. -/
theorem mem_support_of_mem_edgeSet {G : SimpleGraph V} {e : Sym2 V} (he : e ∈ G.edgeSet)
    {x : V} (hx : x ∈ e) : x ∈ G.support := by
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    rcases Sym2.mem_iff'.mp (Sym2.mem_iff_mem.mpr hx) with rfl | rfl
    · exact he.mem_support_left
    · exact he.mem_support_right

/-- If every edge of a walk has both endpoints in `s` and its start is in `s`, then every vertex
of the walk lies in `s`. -/
theorem Walk.support_subset_of_mem_edges {G : SimpleGraph V} {s : Set V} {u v : V}
    {p : G.Walk u v} (he : ∀ e ∈ p.edges, ∀ x ∈ e, x ∈ s) (hu : u ∈ s) :
    ∀ x ∈ p.support, x ∈ s := by
  intro x hx
  by_cases hnil : p.Nil
  · rw [SimpleGraph.Walk.nil_iff_support_eq.mp hnil] at hx
    exact (List.mem_singleton.mp hx) ▸ hu
  · obtain ⟨e, hep, hxe⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil).mp hx
    exact he e hep x hxe

/-! ## Edges of an induced graph

These are stated with `Set.ncard`/`Nat.card` only: the `Fintype` instances used by
`SimpleGraph.edgeFinset` for an induced graph are not the canonical ones for a set given as a
finset coercion, and forcing them to agree costs unbounded amounts of heartbeats. -/

theorem image_preimage_edgeSet {G : SimpleGraph V} {s : Set V} (h : G.support ⊆ s) :
    Sym2.map (Subtype.val : s → V) '' (Sym2.map (Subtype.val : s → V) ⁻¹' G.edgeSet)
      = G.edgeSet := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro e ⟨e', he', rfl⟩
    exact he'
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      have ha : a ∈ s := h (G.mem_support.mpr ⟨b, he⟩)
      have hb : b ∈ s := h (G.mem_support.mpr ⟨a, he.symm⟩)
      refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, ?_⟩
      · rw [Set.mem_preimage, Sym2.map_mk]
        exact he
      · rw [Sym2.map_mk]

/-- If the support of a graph is contained in `s`, then the induced graph on `s` has exactly as
many edges as the graph itself. -/
theorem ncard_edgeSet_induce {G : SimpleGraph V} {s : Set V} (h : G.support ⊆ s) :
    (G.induce s).edgeSet.ncard = G.edgeSet.ncard := by
  have hinj : Function.Injective (Sym2.map (Subtype.val : s → V)) :=
    Sym2.map.injective Subtype.val_injective
  have key := Set.ncard_image_of_injective (Sym2.map (Subtype.val : s → V) ⁻¹' G.edgeSet) hinj
  rw [image_preimage_edgeSet h] at key
  rw [key]
  congr 1
  ext e
  induction e using Sym2.ind with
  | h a b => simp only [Set.mem_preimage, Sym2.map_mk, SimpleGraph.mem_edgeSet,
      SimpleGraph.induce_adj]

namespace TreeState

variable (S : TreeState V)

theorem graph_support_subset_alive : S.graph.support ⊆ (↑S.alive : Set V) := by
  rintro v ⟨w, hw⟩
  exact (S.adj_alive hw).1

/-- The graph induced by a state on its live vertices is connected. -/
theorem induce_alive_connected (hne : S.alive.Nonempty) :
    (S.graph.induce (↑S.alive : Set V)).Connected := by
  obtain ⟨v0, hv0⟩ := hne
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ⟨⟨v0, hv0⟩⟩⟩
  obtain ⟨p⟩ := S.connected u.1 u.2 v.1 v.2
  have hsupp : ∀ x ∈ p.support, x ∈ (↑S.alive : Set V) :=
    Walk.support_subset_of_mem_edges
      (fun e he x hx => S.graph_support_subset_alive
        (mem_support_of_mem_edgeSet (p.edges_subset_edgeSet he) hx)) u.2
  exact ⟨(p.induce _ hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- The graph induced by a state on its live vertices is a tree. -/
theorem induce_alive_isTree (hne : S.alive.Nonempty) :
    (S.graph.induce (↑S.alive : Set V)).IsTree :=
  ⟨S.induce_alive_connected hne, S.acyclic.induce _⟩

/-- A state with `n` live vertices has exactly `n - 1` edges. -/
theorem edgeFinset_card_add_one (hne : S.alive.Nonempty) :
    S.graph.edgeFinset.card + 1 = S.alive.card := by
  have h1 : Nat.card (S.graph.induce (↑S.alive : Set V)).edgeSet + 1
      = Nat.card ↥(↑S.alive : Set V) :=
    (isTree_iff_connected_and_card.mp (S.induce_alive_isTree hne)).2
  have h2 : Nat.card (S.graph.induce (↑S.alive : Set V)).edgeSet = S.graph.edgeFinset.card := by
    have h2a : Nat.card (S.graph.induce (↑S.alive : Set V)).edgeSet = S.graph.edgeSet.ncard := by
      rw [Nat.card_coe_set_eq]
      exact ncard_edgeSet_induce S.graph_support_subset_alive
    have h2b : S.graph.edgeSet.ncard = S.graph.edgeFinset.card := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    rw [h2a, h2b]
  have h3 : Nat.card ↥(↑S.alive : Set V) = S.alive.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  omega

end TreeState

namespace DiamPath

variable {S : TreeState V} (P : DiamPath S)

/-- The last index of the diameter. -/
def last : Fin (P.D + 1) := ⟨P.D, Nat.lt_succ_self P.D⟩

@[simp] theorem last_val : (P.last : ℕ) = P.D := rfl

/-- The index at which a vertex occurs on the diameter, if it occurs at all. -/
noncomputable def index (v : V) : Option (Fin (P.D + 1)) :=
  if h : ∃ i, P.p i = v then some h.choose else none

theorem index_eq_some {v : V} {i : Fin (P.D + 1)} (hi : P.p i = v) : P.index v = some i := by
  unfold index
  split
  · rename_i h
    congr 1
    exact P.inj ((Exists.choose_spec (p := fun j => P.p j = v)
      (⟨i, hi⟩ : ∃ j, P.p j = v)).trans hi.symm)
  · rename_i h
    exact absurd ⟨i, hi⟩ h

theorem index_eq_none {v : V} (h : ∀ i, P.p i ≠ v) : P.index v = none := by
  unfold index
  split
  · rename_i h'
    exact absurd h'.choose_spec (h h'.choose)
  · rfl

/-- If `v` occurs on the diameter at index `i`, then indeed `v = p i`. -/
theorem eq_of_index_eq_some {v : V} {i : Fin (P.D + 1)} (h : P.index v = some i) :
    P.p i = v := by
  unfold index at h
  split at h
  · rename_i hh
    rw [Option.some.injEq] at h
    rw [← h]
    exact hh.choose_spec
  · exact absurd h (by simp)

/-- The canonical representative of the class of `v` after folding: the mirror image
`p i ↦ p (min i (D - i))` on the diameter, and the identity elsewhere. -/
noncomputable def rep (v : V) : V :=
  match P.index v with
  | some i => P.p ⟨min (i : ℕ) (P.D - (i : ℕ)), by have := i.isLt; omega⟩
  | none => v

theorem rep_of_index_some {v : V} {i : Fin (P.D + 1)} (h : P.index v = some i) :
    P.rep v = P.p ⟨min (i : ℕ) (P.D - (i : ℕ)), by have := i.isLt; omega⟩ := by
  simp only [rep, h]

theorem rep_of_index_none {v : V} (h : P.index v = none) : P.rep v = v := by
  simp only [rep, h]

/-- The folding map on the vertices of the diameter. -/
theorem rep_path (i : Fin (P.D + 1)) :
    P.rep (P.p i) = P.p ⟨min (i : ℕ) (P.D - (i : ℕ)), by have := i.isLt; omega⟩ :=
  P.rep_of_index_some (P.index_eq_some rfl)

/-- Off the diameter the folding map is the identity. -/
theorem rep_eq_self {v : V} (h : ∀ i, P.p i ≠ v) : P.rep v = v :=
  P.rep_of_index_none (P.index_eq_none h)

/-- The folded index never exceeds its mirror. -/
theorem min_le_sub (n : ℕ) : min n (P.D - n) ≤ P.D - min n (P.D - n) := by omega

/-- Vertices of the first half of the diameter are fixed by the folding map. -/
theorem rep_path_fix {n : ℕ} (hn : n ≤ P.D) (h2 : n ≤ P.D - n) :
    P.rep (P.p ⟨n, by omega⟩) = P.p ⟨n, by omega⟩ := by
  rw [P.rep_path]
  congr 1
  simp only [Fin.ext_iff]
  omega

/-- Folding is idempotent: canonical representatives are fixed by the folding map. -/
theorem rep_idem (v : V) : P.rep (P.rep v) = P.rep v := by
  rcases h : P.index v with _ | i
  · simp only [P.rep_of_index_none h]
  · rw [P.rep_of_index_some h]
    exact P.rep_path_fix (by have := i.isLt; omega) (P.min_le_sub i)

/-- A vertex is live iff its canonical representative is live. -/
theorem rep_mem_iff {v : V} : P.rep v ∈ S.alive ↔ v ∈ S.alive := by
  constructor
  · intro hv
    rcases h : P.index v with _ | i
    · rwa [P.rep_of_index_none h] at hv
    · rw [← P.eq_of_index_eq_some h]
      exact P.mem i
  · intro hv
    rcases h : P.index v with _ | i
    · rwa [P.rep_of_index_none h]
    · rw [P.rep_of_index_some h]
      exact P.mem _

theorem rep_mem {v : V} (hv : v ∈ S.alive) : P.rep v ∈ S.alive := P.rep_mem_iff.mpr hv

/-! ## The folded state -/

/-- The vertices of the folded tree: the fixed points of the folding map `rep` inside
`alive`.  These are the canonical representatives of the equivalence classes. -/
noncomputable def foldAlive : Finset V :=
  S.alive.filter fun v => P.rep v = v

theorem mem_foldAlive {v : V} : v ∈ P.foldAlive ↔ v ∈ S.alive ∧ P.rep v = v := by
  simp [foldAlive]

theorem foldAlive_subset : P.foldAlive ⊆ S.alive :=
  fun _ hv => (P.mem_foldAlive.mp hv).1

theorem rep_mem_foldAlive {v : V} (hv : v ∈ S.alive) : P.rep v ∈ P.foldAlive :=
  P.mem_foldAlive.mpr ⟨P.rep_mem hv, P.rep_idem v⟩

/-- A vertex of the diameter is a vertex of the folded tree exactly when it lies in the
first half of the diameter. -/
theorem path_mem_foldAlive {i : Fin (P.D + 1)} :
    P.p i ∈ P.foldAlive ↔ 2 * (i : ℕ) ≤ P.D := by
  rw [mem_foldAlive]
  refine ⟨fun h => ?_, fun h => ⟨P.mem i, ?_⟩⟩
  · have h' := h.2
    rw [P.rep_path] at h'
    have := P.inj h'
    simp only [Fin.ext_iff] at this
    omega
  · rw [P.rep_path]
    congr 1
    simp only [Fin.ext_iff]
    omega

/-- The graph of the folded tree: two live representatives are adjacent when they are the
images of the two endpoints of an edge of the current tree. -/
noncomputable def foldGraph : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ∈ P.foldAlive ∧ v ∈ P.foldAlive ∧
    ∃ x y, S.graph.Adj x y ∧ P.rep x = u ∧ P.rep y = v
  symm := ⟨fun _ _ ⟨hne, hu, hv, x, y, hxy, hx, hy⟩ =>
    ⟨hne.symm, hv, hu, y, x, hxy.symm, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem foldGraph_adj {u v : V} :
    P.foldGraph.Adj u v ↔ u ≠ v ∧ u ∈ P.foldAlive ∧ v ∈ P.foldAlive ∧
      ∃ x y, S.graph.Adj x y ∧ P.rep x = u ∧ P.rep y = v := Iff.rfl

theorem foldGraph_adj_subset {u v : V} (h : P.foldGraph.Adj u v) :
    u ∈ P.foldAlive ∧ v ∈ P.foldAlive :=
  ⟨h.2.1, h.2.2.1⟩

/-- The folding map sends the endpoints of an edge of the current tree to vertices of the
folded tree that are equal or adjacent. -/
theorem reachable_rep_of_adj {a b : V} (h : S.graph.Adj a b) :
    P.foldGraph.Reachable (P.rep a) (P.rep b) := by
  rcases eq_or_ne (P.rep a) (P.rep b) with heq | hne
  · exact ⟨SimpleGraph.Walk.nil.copy heq.symm rfl⟩
  · refine ⟨SimpleGraph.Walk.cons ?_ SimpleGraph.Walk.nil⟩
    exact ⟨hne, P.rep_mem_foldAlive (S.adj_alive h).1,
      P.rep_mem_foldAlive (S.adj_alive h).2, a, b, h, rfl, rfl⟩

/-- Folding does not destroy connectivity. -/
theorem fold_reachable {u v : V} (h : S.graph.Reachable u v) :
    P.foldGraph.Reachable (P.rep u) (P.rep v) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | cons hadj rest ih => exact (P.reachable_rep_of_adj hadj).trans ih

/-- The folding map sends the endpoints of an edge of the current tree to vertices of the folded
tree at distance at most one. -/
theorem exists_walk_rep_of_adj {a b : V} (h : S.graph.Adj a b) :
    ∃ w : P.foldGraph.Walk (P.rep a) (P.rep b), w.length ≤ 1 := by
  rcases eq_or_ne (P.rep a) (P.rep b) with heq | hne
  · exact ⟨SimpleGraph.Walk.nil.copy heq.symm rfl, by simp⟩
  · exact ⟨SimpleGraph.Walk.cons ⟨hne, P.rep_mem_foldAlive (S.adj_alive h).1,
      P.rep_mem_foldAlive (S.adj_alive h).2, a, b, h, rfl, rfl⟩ SimpleGraph.Walk.nil, le_rfl⟩

/-- Folding never lengthens a walk: the image of a walk of the current tree is a walk of the folded
tree, of at most the same length (steps which are folded onto a single vertex disappear). -/
theorem exists_fold_walk_le {u v : V} (w : S.graph.Walk u v) :
    ∃ w' : P.foldGraph.Walk (P.rep u) (P.rep v), w'.length ≤ w.length := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
  | cons hadj rest ih =>
      obtain ⟨w₁, h₁⟩ := P.exists_walk_rep_of_adj hadj
      obtain ⟨w₂, h₂⟩ := ih
      exact ⟨w₁.append w₂, by
        simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
        omega⟩

/-- **Folding does not increase distances.**  This is the metric content of "the folded tree is the
quotient of the current tree": the image of a geodesic is a walk of at most the same length, and the
distance of the folded graph is the length of a shortest walk. -/
theorem fold_dist_le {u v : V} (hu : u ∈ S.alive) (hv : v ∈ S.alive) :
    P.foldGraph.dist (P.rep u) (P.rep v) ≤ S.graph.dist u v := by
  obtain ⟨w, -, hw⟩ := (S.connected u hu v hv).exists_path_of_dist
  obtain ⟨w', hw'⟩ := P.exists_fold_walk_le w
  calc P.foldGraph.dist (P.rep u) (P.rep v) ≤ w'.length := SimpleGraph.dist_le w'
    _ ≤ w.length := hw'
    _ = S.graph.dist u v := hw

/-! ## The mirror involution on the edge indices of the diameter

Index the edges of the diameter by `Fin P.D`, the `i`-th edge being `s(p i, p (i+1))`.
Folding identifies `i` with `P.D - 1 - i`, so we collect the mirror pairs. -/

/-- The index of the edge mirroring the `i`-th edge of the diameter. -/
def mirror (i : Fin P.D) : Fin P.D := ⟨P.D - 1 - (i : ℕ), by omega⟩

@[simp] theorem mirror_val (i : Fin P.D) : (P.mirror i : ℕ) = P.D - 1 - (i : ℕ) := rfl

theorem mirror_involutive (i : Fin P.D) : P.mirror (P.mirror i) = i := by
  ext
  simp only [mirror_val]
  omega

/-- The `i`-th edge of the diameter, as an unordered pair of vertices. -/
def pe (i : Fin P.D) : Sym2 V := s(P.p i.castSucc, P.p i.succ)

theorem pe_mem_edgeFinset (i : Fin P.D) : P.pe i ∈ S.graph.edgeFinset :=
  S.graph.mem_edgeFinset.mpr (S.graph.mem_edgeSet.mpr (P.adj i))

theorem pe_inj : Function.Injective P.pe := by
  intro i j hij
  have key : ∀ a b : Fin (P.D + 1), P.p a = P.p b → (a : ℕ) = (b : ℕ) :=
    fun a b hab => by rw [P.inj hab]
  have h : s(P.p i.castSucc, P.p i.succ) = s(P.p j.castSucc, P.p j.succ) := hij
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' := key _ _ h1
    have h2' := key _ _ h2
    simp only [Fin.val_castSucc, Fin.val_succ] at h1' h2'
    ext
    omega
  · have h1' := key _ _ h1
    have h2' := key _ _ h2
    simp only [Fin.val_castSucc, Fin.val_succ] at h1' h2'
    ext
    omega

/-- The folded image of the `i`-th edge of the diameter, in explicit coordinates. -/
theorem map_rep_pe (i : Fin P.D) :
    Sym2.map P.rep (P.pe i) =
      s(P.p ⟨min (i : ℕ) (P.D - (i : ℕ)), by omega⟩,
        P.p ⟨min ((i : ℕ) + 1) (P.D - 1 - (i : ℕ)), by omega⟩) := by
  have h1 : P.rep (P.p i.castSucc) = P.p ⟨min (i : ℕ) (P.D - (i : ℕ)), by omega⟩ := by
    rw [P.rep_path]
    congr 1
  have h2 : P.rep (P.p i.succ) = P.p ⟨min ((i : ℕ) + 1) (P.D - 1 - (i : ℕ)), by omega⟩ := by
    rw [P.rep_path]
    congr 1
    simp only [Fin.mk.injEq, Fin.val_succ]
    omega
  rw [pe, Sym2.map_mk, h1, h2]

/-- Mirror edges of the diameter have the same folded image. -/
theorem map_rep_pe_mirror (i : Fin P.D) :
    Sym2.map P.rep (P.pe (P.mirror i)) = Sym2.map P.rep (P.pe i) := by
  rw [P.map_rep_pe (P.mirror i), P.map_rep_pe i]
  refine Sym2.eq_iff.mpr (Or.inr ⟨?_, ?_⟩) <;>
    · congr 1
      simp only [Fin.mk.injEq, mirror_val]
      omega

/-- The central edge of an odd diameter folds to a loop. -/
theorem isDiag_map_rep_pe_of_mirror_eq (i : Fin P.D) (h : P.mirror i = i) :
    (Sym2.map P.rep (P.pe i)).IsDiag := by
  have hi : (i : ℕ) = P.D - 1 - (i : ℕ) := by
    have := congrArg Fin.val h
    simp only [mirror_val] at this
    omega
  rw [P.map_rep_pe i, Sym2.mk_isDiag_iff]
  congr 1
  simp only [Fin.mk.injEq]
  omega

/-! ## The redundant edges of the diameter -/

/-- The indices of the second half of the diameter's edges: those are `D / 2` many, and each of
them is either the mirror of an edge of the first half (with the same folded image) or the
central edge (which folds to a loop). -/
def badIdx : Finset (Fin P.D) :=
  Finset.univ.filter fun i => P.D / 2 ≤ (i : ℕ)

theorem mem_badIdx {i : Fin P.D} : i ∈ P.badIdx ↔ P.D / 2 ≤ (i : ℕ) := by
  simp [badIdx]

/-- The corresponding set of edges of the current tree, which we remove before counting. -/
def badSet : Finset (Sym2 V) := P.badIdx.image P.pe

theorem pe_mem_badSet {i : Fin P.D} : P.pe i ∈ P.badSet ↔ i ∈ P.badIdx := by
  rw [badSet, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    obtain rfl : j = i := P.pe_inj hji
    exact hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem badSet_subset : P.badSet ⊆ S.graph.edgeFinset := by
  intro e he
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
  exact P.pe_mem_edgeFinset i

theorem card_badIdx : P.badIdx.card = P.D - P.D / 2 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin P.D))) (p := fun i : Fin P.D => P.D / 2 ≤ (i : ℕ))
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun i : Fin P.D => ¬ (P.D / 2 ≤ (i : ℕ))).card = P.D / 2 := by
    have he : (Finset.univ.filter fun i : Fin P.D => ¬ (P.D / 2 ≤ (i : ℕ)))
        = (Finset.univ : Finset (Fin (P.D / 2))).image
            (fun j : Fin (P.D / 2) => (⟨(j : ℕ), by omega⟩ : Fin P.D)) := by
      ext i
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨-, hi⟩
        exact ⟨⟨(i : ℕ), by omega⟩, Finset.mem_univ _, by ext; rfl⟩
      · rintro ⟨j, -, hj⟩
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hj]
        exact not_le.mpr j.isLt
    rw [he, Finset.card_image_of_injective _
        (fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)),
      Finset.card_univ, Fintype.card_fin]
  rw [badIdx]
  omega

theorem card_badSet : P.badSet.card = P.D - P.D / 2 := by
  rw [badSet, Finset.card_image_of_injective _ P.pe_inj, P.card_badIdx]

/-! ## The induced graph on the folded vertices -/

/-- The vertices of the folded tree, as a set. -/
def foldSet : Set V := ↑P.foldAlive

theorem foldGraph_support_subset : P.foldGraph.support ⊆ P.foldSet := by
  rintro v ⟨w, hw⟩
  exact (P.foldGraph_adj.mp hw).2.1

/-- The folded graph induced on the vertices of the folded tree. -/
noncomputable abbrev foldInduce : SimpleGraph P.foldSet := P.foldGraph.induce P.foldSet

/-! ## Counting the edges of the folded graph -/

/-- Every edge of the folded graph is the folded image of an edge of the current tree which is
not one of the `D - D / 2` redundant edges of the diameter described by `badSet`. -/
theorem foldGraph_edgeFinset_subset :
    P.foldGraph.edgeFinset ⊆ (S.graph.edgeFinset \ P.badSet).image (Sym2.map P.rep) := by
  intro q hq
  induction q using Sym2.ind with
  | h u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, P.foldGraph_adj] at hq
    obtain ⟨hne, -, -, x, y, hxy, hx, hy⟩ := hq
    have hxyE : s(x, y) ∈ S.graph.edgeFinset :=
      S.graph.mem_edgeFinset.mpr (S.graph.mem_edgeSet.mpr hxy)
    by_cases hbad : s(x, y) ∈ P.badSet
    · obtain ⟨i, hi, hipe⟩ := Finset.mem_image.mp hbad
      have hi2 : P.D / 2 ≤ (i : ℕ) := P.mem_badIdx.mp hi
      rcases eq_or_ne (P.mirror i) i with heq | hne'
      · -- the central edge of an odd diameter folds to a loop, which is not an edge
        exfalso
        have hdiag := P.isDiag_map_rep_pe_of_mirror_eq i heq
        rw [hipe, Sym2.map_mk, hx, hy] at hdiag
        exact hne (Sym2.mk_isDiag_iff.mp hdiag)
      · have hgood : ¬ (P.D / 2 ≤ (P.mirror i : ℕ)) := by
          have hlt : P.D - 1 - (i : ℕ) < (i : ℕ) := by
            have hle : P.D - 1 - (i : ℕ) ≤ (i : ℕ) := by omega
            have hne : P.D - 1 - (i : ℕ) ≠ (i : ℕ) := fun hh => hne' (Fin.ext hh)
            omega
          show ¬ (P.D / 2 ≤ P.D - 1 - (i : ℕ))
          omega
        refine Finset.mem_image.mpr
          ⟨P.pe (P.mirror i), Finset.mem_sdiff.mpr ⟨P.pe_mem_edgeFinset _, ?_⟩, ?_⟩
        · rw [P.pe_mem_badSet, P.mem_badIdx]
          exact hgood
        · rw [P.map_rep_pe_mirror i, hipe, Sym2.map_mk, hx, hy]
    · exact Finset.mem_image.mpr
        ⟨s(x, y), Finset.mem_sdiff.mpr ⟨hxyE, hbad⟩, by rw [Sym2.map_mk, hx, hy]⟩

/-- **Edge count.** Folding removes (at least) `⌈D/2⌉ = D - D/2` edges. -/
theorem card_foldGraph_edgeFinset :
    P.foldGraph.edgeFinset.card + (P.D - P.D / 2) ≤ S.graph.edgeFinset.card := by
  have h1 : P.foldGraph.edgeFinset.card
      ≤ ((S.graph.edgeFinset \ P.badSet).image (Sym2.map P.rep)).card :=
    Finset.card_le_card P.foldGraph_edgeFinset_subset
  have h2 : ((S.graph.edgeFinset \ P.badSet).image (Sym2.map P.rep)).card
      ≤ (S.graph.edgeFinset \ P.badSet).card := Finset.card_image_le
  have h3 : (S.graph.edgeFinset \ P.badSet).card + P.badSet.card = S.graph.edgeFinset.card :=
    Finset.card_sdiff_add_card_eq_card P.badSet_subset
  rw [P.card_badSet] at h3
  omega

/-! ## Counting the vertices of the folded tree -/

/-- The vertices of the diameter, as a finset. -/
def pathSet : Finset V := Finset.univ.image P.p

theorem pathSet_subset : P.pathSet ⊆ S.alive := by
  intro v hv
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
  exact P.mem i

theorem card_pathSet : P.pathSet.card = P.D + 1 := by
  rw [pathSet, Finset.card_image_of_injective _ P.inj, Finset.card_univ, Fintype.card_fin]

/-- Off the diameter, `rep` is the identity, so the vertices of the folded tree split into the
vertices outside the diameter and the vertices of the first half of the diameter. -/
theorem foldAlive_eq :
    P.foldAlive = (S.alive \ P.pathSet) ∪ (P.pathSet.filter fun v => P.rep v = v) := by
  ext v
  rw [P.mem_foldAlive, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hr⟩
    by_cases hvA : v ∈ P.pathSet
    · exact Or.inr ⟨hvA, hr⟩
    · exact Or.inl ⟨hv, hvA⟩
  · rintro (⟨hv, hvA⟩ | ⟨hvA, hr⟩)
    · refine ⟨hv, P.rep_eq_self fun i hi => hvA ?_⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    · exact ⟨P.pathSet_subset hvA, hr⟩

theorem pathSet_filter_card :
    (P.pathSet.filter fun v => P.rep v = v).card = P.D / 2 + 1 := by
  have he : (P.pathSet.filter fun v => P.rep v = v)
      = (Finset.univ.filter fun i : Fin (P.D + 1) => 2 * (i : ℕ) ≤ P.D).image P.p := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvA, hrv⟩ := Finset.mem_filter.mp hv
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hvA
      refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hi⟩
      subst hi
      exact (P.path_mem_foldAlive (i := i)).mp (P.mem_foldAlive.mpr ⟨P.mem i, hrv⟩)
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      rw [Finset.mem_filter] at hi
      refine Finset.mem_filter.mpr
        ⟨?_, (P.mem_foldAlive.mp ((P.path_mem_foldAlive (i := i)).mpr hi.2)).2⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  rw [he, Finset.card_image_of_injective _ P.inj]
  have h2 : (Finset.univ.filter fun i : Fin (P.D + 1) => 2 * (i : ℕ) ≤ P.D)
      = (Finset.univ.filter fun i : Fin (P.D + 1) => (i : ℕ) ≤ P.D / 2) := by
    refine Finset.filter_congr ?_
    intro i _
    omega
  rw [h2]
  have h3 : (Finset.univ.filter fun i : Fin (P.D + 1) => (i : ℕ) ≤ P.D / 2)
      = (Finset.univ : Finset (Fin (P.D / 2 + 1))).image
          (fun j : Fin (P.D / 2 + 1) => (⟨(j : ℕ), by omega⟩ : Fin (P.D + 1))) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hi⟩
      exact ⟨⟨(i : ℕ), by omega⟩, Finset.mem_univ _, by ext; rfl⟩
    · rintro ⟨j, -, hj⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hj]
      show (j : ℕ) ≤ P.D / 2
      omega
  rw [h3, Finset.card_image_of_injective _
      (fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)),
    Finset.card_univ, Fintype.card_fin]

/-- **Vertex count.** Folding removes exactly `⌈D/2⌉ = D - D/2` vertices: one from each mirror
pair of diameter vertices. -/
theorem card_alive_eq : S.alive.card = P.foldAlive.card + (P.D - P.D / 2) := by
  have hdisj : Disjoint (S.alive \ P.pathSet) (P.pathSet.filter fun v => P.rep v = v) :=
    Finset.disjoint_left.mpr fun v hv hv' => (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mp hv').1
  have h1 : (S.alive \ P.pathSet).card + P.pathSet.card = S.alive.card :=
    Finset.card_sdiff_add_card_eq_card P.pathSet_subset
  have h2 : P.foldAlive.card
      = (S.alive \ P.pathSet).card + (P.pathSet.filter fun v => P.rep v = v).card := by
    rw [P.foldAlive_eq, Finset.card_union_of_disjoint hdisj]
  rw [← h1, h2, P.card_pathSet, P.pathSet_filter_card]
  omega

/-! ## The folded graph is a tree -/

/-- The folded graph, restricted to the vertices of the folded tree, is connected. -/
theorem foldInduce_connected : P.foldInduce.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_,
    ⟨⟨P.p 0, (P.path_mem_foldAlive (i := 0)).mpr (by simp)⟩⟩⟩
  have hu : P.rep u.1 = u.1 := (P.mem_foldAlive.mp u.2).2
  have hv : P.rep v.1 = v.1 := (P.mem_foldAlive.mp v.2).2
  obtain ⟨w⟩ := P.fold_reachable
    (S.connected u.1 (P.mem_foldAlive.mp u.2).1 v.1 (P.mem_foldAlive.mp v.2).1)
  have hw := w.copy hu hv
  have hsupp : ∀ x ∈ hw.support, x ∈ P.foldSet :=
    Walk.support_subset_of_mem_edges
      (fun e he x hx => P.foldGraph_support_subset
        (mem_support_of_mem_edgeSet (hw.edges_subset_edgeSet he) hx)) u.2
  exact ⟨(hw.induce _ hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- **The folded graph on its vertex set is a tree.** -/
theorem foldInduce_isTree : P.foldInduce.IsTree := by
  refine isTree_iff_connected_and_card.mpr ⟨P.foldInduce_connected, ?_⟩
  have h1 : Nat.card P.foldInduce.edgeSet = P.foldGraph.edgeFinset.card := by
    have h1a : Nat.card P.foldInduce.edgeSet = P.foldGraph.edgeSet.ncard := by
      rw [Nat.card_coe_set_eq]
      exact ncard_edgeSet_induce P.foldGraph_support_subset
    have h1b : P.foldGraph.edgeSet.ncard = P.foldGraph.edgeFinset.card := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    rw [h1a, h1b]
  have h2 : Nat.card P.foldSet = P.foldAlive.card := by
    rw [Nat.card_coe_set_eq]
    show (↑P.foldAlive : Set V).ncard = P.foldAlive.card
    rw [Set.ncard_coe_finset]
  have hle : P.foldGraph.edgeFinset.card + 1 ≤ P.foldAlive.card := by
    have hE : S.graph.edgeFinset.card + 1 = S.alive.card :=
      S.edgeFinset_card_add_one ⟨P.p 0, P.mem 0⟩
    have he := P.card_foldGraph_edgeFinset
    have hv := P.card_alive_eq
    omega
  have h3 : Nat.card ↥P.foldSet ≤ Nat.card P.foldInduce.edgeSet + 1 :=
    P.foldInduce_connected.card_vert_le_card_edgeSet_add_one
  rw [h1, h2] at h3 ⊢
  omega

/-- **Folding a tree along a diameter again yields a tree.**  The folded graph has exactly
`|alive| - ⌈D/2⌉` vertices and `|alive| - 1 - ⌈D/2⌉` edges, hence is acyclic. -/
theorem foldGraph_isAcyclic : P.foldGraph.IsAcyclic := by
  intro v c hc
  have hv : v ∈ P.foldSet := by
    cases c with
    | nil => exact (hc.not_nil (by simp)).elim
    | cons hadj rest => exact (P.foldGraph_adj.mp hadj).2.1
  have hsupp : ∀ x ∈ c.support, x ∈ P.foldSet :=
    Walk.support_subset_of_mem_edges
      (fun e he x hx => P.foldGraph_support_subset
        (mem_support_of_mem_edgeSet (c.edges_subset_edgeSet he) hx)) hv
  have hcyc : (c.induce P.foldSet hsupp).IsCycle := by
    have h2 : ((c.induce P.foldSet hsupp).map
        (SimpleGraph.Embedding.induce P.foldSet).toHom).IsCycle := by
      rw [Walk.map_induce]
      exact hc
    exact Walk.IsCycle.of_map h2
  exact P.foldInduce_isTree.isAcyclic _ hcyc

/-- The state obtained by folding the current tree along the diameter `P`. -/
noncomputable def foldState : TreeState V where
  alive := P.foldAlive
  graph := P.foldGraph
  adj_alive := fun _ _ h => P.foldGraph_adj_subset h
  connected := fun u hu v hv => by
    obtain ⟨hu', huf⟩ := P.mem_foldAlive.mp hu
    obtain ⟨hv', hvf⟩ := P.mem_foldAlive.mp hv
    have h := P.fold_reachable (S.connected u hu' v hv')
    rwa [huf, hvf] at h
  acyclic := P.foldGraph_isAcyclic

end DiamPath

/-! ## The folding process -/

/-- One folding step: `S'` is obtained from `S` by folding along some diameter. -/
def FoldStep (S S' : TreeState V) : Prop := ∃ P : DiamPath S, S' = P.foldState

/-- `FoldSeq S S' n`: `S'` is obtained from `S` by `n` folding operations.  In a state with at
most one vertex the diameter is empty and folding would do nothing, so no step is taken from such
a state: the process stops exactly when a single vertex is left. -/
inductive FoldSeq : TreeState V → TreeState V → ℕ → Prop
  | refl (S : TreeState V) : FoldSeq S S 0
  | step {S S' S'' : TreeState V} {n : ℕ} (hpos : 2 ≤ S.alive.card) :
      FoldStep S S' → FoldSeq S' S'' n → FoldSeq S S'' (n + 1)

/-- A state consisting of a single vertex. -/
def IsSingle (S : TreeState V) : Prop := S.alive.card ≤ 1

/-! ## Diameter endpoints -/

/-- `s` is a diameter endpoint of the state `S` if it is a live vertex at distance `diam`
from some other live vertex. -/
def IsDiamEnd (S : TreeState V) (s : V) : Prop :=
  s ∈ S.alive ∧ ∃ y ∈ S.alive, S.graph.dist s y = S.diam

theorem IsDiamEnd.mem {S : TreeState V} {s : V} (h : IsDiamEnd S s) : s ∈ S.alive := h.1

theorem IsDiamEnd.ecc {S : TreeState V} {s : V} (h : IsDiamEnd S s) :
    ∃ y ∈ S.alive, S.graph.dist s y = S.diam := h.2

/-- The endpoints of a diameter path are diameter endpoints of the state. -/
theorem DiamPath.isDiamEnd_zero {S : TreeState V} (P : DiamPath S) :
    IsDiamEnd S (P.p 0) :=
  ⟨P.mem 0, P.p P.last, P.mem P.last, P.isDiam⟩

theorem DiamPath.isDiamEnd_last {S : TreeState V} (P : DiamPath S) :
    IsDiamEnd S (P.p P.last) :=
  ⟨P.mem P.last, P.p 0, P.mem 0, by rw [SimpleGraph.dist_comm]; exact P.isDiam⟩

/-- A nonempty state has a diameter endpoint. -/
theorem exists_isDiamEnd {S : TreeState V} (h : S.alive.Nonempty) : ∃ s, IsDiamEnd S s := by
  obtain ⟨u, hu, v, hv, hd⟩ := S.exists_dist_eq_diam h
  exact ⟨u, hu, v, hv, hd⟩

/-! ## Folding towards a fixed endpoint -/

/-- One folding step in which the fold is performed towards the fixed vertex `s`: the diameter
along which we fold starts at `s`, so that `s` is one of the two vertices being identified. -/
def FoldStepAt (s : V) (S S' : TreeState V) : Prop :=
  ∃ P : DiamPath S, P.p 0 = s ∧ S' = P.foldState

/-- `FoldSeqAt s S S' n`: `S'` is obtained from `S` by `n` folding steps, each of them performed
towards the fixed vertex `s`.  No step is taken from a state with at most one vertex, so the
sequence is *maximal*: it stops as soon as a single vertex is left. -/
inductive FoldSeqAt (s : V) : TreeState V → TreeState V → ℕ → Prop
  | refl (S : TreeState V) : FoldSeqAt s S S 0
  | step {S S' S'' : TreeState V} {n : ℕ} (hpos : 2 ≤ S.alive.card) :
      FoldStepAt s S S' → FoldSeqAt s S' S'' n → FoldSeqAt s S S'' (n + 1)

/-- `LValue S s n`: there is a complete folding process of `S` that always folds towards `s`,
performs exactly `n` operations, and ends with a single vertex. -/
def LValue (S : TreeState V) (s : V) (n : ℕ) : Prop :=
  ∃ S' : TreeState V, FoldSeqAt s S S' n ∧ IsSingle S'

end OhtoaiTreeProof
