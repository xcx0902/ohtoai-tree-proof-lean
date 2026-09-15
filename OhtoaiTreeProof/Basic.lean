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

/-- The folded graph is acyclic, so that the folded state is again a tree.  The proof is the
edge- and vertex-counting argument of `REF.md` §2, see `OhtoaiTreeProof.FoldTree`. -/
theorem foldGraph_isAcyclic : P.foldGraph.IsAcyclic := by
  sorry

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
