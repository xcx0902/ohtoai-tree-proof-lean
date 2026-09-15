import OhtoaiTreeProof.Basic

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

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

namespace TreeState

variable (S : TreeState V)

theorem graph_support_subset_alive : S.graph.support ⊆ (↑S.alive : Set V) := by
  rintro v ⟨w, hw⟩
  exact (S.adj_alive hw).1

/-- The graph induced by a state on its live vertices is connected. -/
theorem induce_alive_connected (hne : S.alive.Nonempty) :
    (S.graph.induce (↑S.alive : Set V)).Connected := by
  refine ⟨fun u v => ?_, ⟨S.alive.min' hne, Finset.min'_mem _ hne⟩⟩
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
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact SimpleGraph.card_edgeFinset_induce_of_support_subset S.graph_support_subset_alive
  have h3 : Nat.card ↥(↑S.alive : Set V) = S.alive.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  omega

end TreeState

namespace DiamPath

variable {S : TreeState V} (P : DiamPath S)

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
abbrev foldInduce : SimpleGraph P.foldSet := P.foldGraph.induce P.foldSet

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
  refine ⟨fun u v => ?_, ⟨P.p 0, (P.path_mem_foldAlive (i := 0)).mpr (by omega)⟩⟩
  have hu : P.rep u.1 = u.1 := (P.mem_foldAlive.mp u.2).2
  have hv : P.rep v.1 = v.1 := (P.mem_foldAlive.mp v.2).2
  obtain ⟨w⟩ := P.fold_reachable
    (S.connected u.1 (P.mem_foldAlive.mp u.2).1 v.1 (P.mem_foldAlive.mp v.2).1)
  have hw := w.copy hu.symm hv.symm
  have hsupp : ∀ x ∈ hw.support, x ∈ P.foldSet :=
    Walk.support_subset_of_mem_edges
      (fun e he x hx => P.foldGraph_support_subset
        (mem_support_of_mem_edgeSet (hw.edges_subset_edgeSet he) hx)) u.2
  exact ⟨(hw.induce _ hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- **The folded graph on its vertex set is a tree.** -/
theorem foldInduce_isTree : P.foldInduce.IsTree := by
  refine isTree_iff_connected_and_card.mpr ⟨P.foldInduce_connected, ?_⟩
  have h1 : Nat.card P.foldInduce.edgeSet = P.foldGraph.edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact SimpleGraph.card_edgeFinset_induce_of_support_subset P.foldGraph_support_subset
  have h2 : Nat.card P.foldSet = P.foldAlive.card := by
    rw [Nat.card_coe_set_eq]
    show (↑P.foldAlive : Set V).ncard = P.foldAlive.card
    rw [Set.ncard_coe_finset]
  have hE : S.graph.edgeFinset.card + 1 = S.alive.card :=
    S.edgeFinset_card_add_one ⟨P.p 0, P.mem 0⟩
  have he := P.card_foldGraph_edgeFinset
  have hv := P.card_alive_eq
  rw [h1, h2]
  omega

/-- **Folding a tree along a diameter again yields a tree.**  The folded graph has exactly
`|alive| - ⌈D/2⌉` vertices and `|alive| - 1 - ⌈D/2⌉` edges, hence is acyclic. -/
theorem foldGraph_isAcyclic' : P.foldGraph.IsAcyclic := by
  intro v c hc
  have hv : v ∈ P.foldSet := by
    cases c with
    | nil => exact absurd rfl hc.not_nil
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

end DiamPath

end OhtoaiTreeProof
