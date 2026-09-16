/-
# REF.md §7: auxiliary closure and degenerate-case lemmas

This file studies a sufficient path-avoidance condition `DeltaClosed`, records its consequences
in `SyncInv`, and proves equality of the first-fold states when the initial diameters coincide.
It also packages some immediate endgame cases with their nondegeneracy hypotheses.

The full synchronised induction is proved in `SyncStep.lean`, using `SyncCtx` from `Sync.lean`.
That invariant records avoiding geodesics directly, together with the surviving legs and the
composite quotient map; it does not depend on an unproved `DeltaClosed` preservation statement.
`SyncEndgame.lean` supplies the final map comparison and the unconditional exchange theorem.
-/
import OhtoaiTreeProof.Phase2
import OhtoaiTreeProof.Phase1
import OhtoaiTreeProof.ExchangeLemma5
import OhtoaiTreeProof.ExchangeProof
import OhtoaiTreeProof.Cone
import OhtoaiTreeProof.Iso
import OhtoaiTreeProof.Progress

set_option linter.unusedSectionVars false
set_option linter.ambiguousOpen false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The difference region is closed away from `s`

`P.Delta Q s` is the union of the subtrees of `S` hanging off the two tails `p (ℓ+1), …, p D`,
`q (ℓ+1), …, q D` (away from `s`).  A union of subtrees hanging away from `s` is closed under
"moving one step away from `s`": if `v` lies in such a subtree and `w` is the neighbour of `v` that
is farther from `s`, then the path from `s` to `w` still passes through the tail vertex that
witnessed `v ∈ Δ`, so `w ∈ Δ` too.  This closure is the only structural property of `Δ` used by the
synchronised phase: it says that a path leading to a vertex *outside* `Δ` never enters `Δ`, hence
the far part of the tree — in particular every diameter ending far from `s` — is literally the same
in the two states. -/

/-- `D` is *closed away from `s`* in the state `T`: every neighbour `w` of a vertex `v ∈ D` that is
one step farther from `s` than `v` belongs to `D` as well. -/
def DeltaClosed (T : TreeState V) (D : Set V) (s : V) : Prop :=
  ∀ ⦃v w : V⦄, v ∈ T.alive → w ∈ T.alive → v ∈ D → T.graph.Adj v w →
    T.graph.dist s w = T.graph.dist s v + 1 → w ∈ D

/-- The vertices of a walk are live as soon as its start is. -/
theorem getVert_mem_alive {T : TreeState V} {s w : V} (hs : s ∈ T.alive) (p : T.graph.Walk s w)
    (k : ℕ) : p.getVert k ∈ T.alive :=
  T.support_subset_alive hs p _ (SimpleGraph.Walk.getVert_mem_support p k)

/-- **A geodesic of a tree that ends outside a set closed away from its start never enters the
set.**  Applied to the difference region `Δ`, this is `REF.md` §7's observation that "all vertices
at distance more than `2r` from `s`, and the paths leading to them, are the same in the two
trees". -/
theorem notMem_of_deltaClosed {T : TreeState V} {D : Set V} {s w : V} (hcl : DeltaClosed T D s)
    (hs : s ∈ T.alive) (_hw : w ∈ T.alive) (hwD : w ∉ D) {p : T.graph.Walk s w} (hp : p.IsPath) :
    ∀ k ≤ p.length, p.getVert k ∉ D := by
  intro k hk
  by_contra hkD
  have hstep : ∀ l, l < p.length → p.getVert l ∈ D → p.getVert (l + 1) ∈ D := by
    intro l hl hmem
    have h1 : T.graph.dist s (p.getVert (l + 1)) = l + 1 :=
      dist_getVert_eq T.acyclic hp (by omega)
    have h2 : T.graph.dist s (p.getVert l) = l := dist_getVert_eq T.acyclic hp (by omega)
    exact hcl (getVert_mem_alive hs p l) (getVert_mem_alive hs p (l + 1)) hmem
      (p.adj_getVert_succ hl) (by omega)
  have key : ∀ l, k ≤ l → l ≤ p.length → p.getVert l ∈ D := by
    intro l hkl
    induction l, hkl using Nat.le_induction with
    | base => intro _; exact hkD
    | succ l hkl ih => intro hl; exact hstep l (by omega) (ih (by omega))
  have hfin : p.getVert p.length ∈ D := key p.length hk (le_refl p.length)
  rw [SimpleGraph.Walk.getVert_length p] at hfin
  exact hwD hfin

/-! ## 2. The invariant of the synchronised phase

`Phase1Inv` (`Phase2.lean`) says that the two states agree outside `Δ` and that every live vertex of
`Δ` is within `2r` of `s`.  The synchronised phase needs one more property of `Δ`, namely that it is
closed away from `s` in both states: this is what turns "the far endpoint `z` of a diameter of `T₁`
is not in `Δ`" into "the whole path from `s` to `z` avoids `Δ`", and hence makes that path literally
the same in `T₂`.  `SyncInv` is `Phase1Inv` together with that closure. -/

namespace DiamPath

variable {S : TreeState V}

/-- The common length `r = D - ℓ` of the two tails of the diameters `P` and `Q`. -/
noncomputable def tailLen (P Q : DiamPath S) : ℕ := P.D - P.meetIdx Q

theorem tailLen_eq (P Q : DiamPath S) : P.tailLen Q = P.D - P.meetIdx Q := rfl

/-- **The invariant of the synchronised phase**: `Phase1Inv` plus the descent property of the
difference region in both states. -/
structure SyncInv (P Q : DiamPath S) (T₁ T₂ : TreeState V) (s : V) : Prop
    extends Phase1Inv P Q T₁ T₂ s where
  /-- the difference region is closed away from `s` in the first state -/
  closed₁ : DeltaClosed T₁ (P.Delta Q s) s
  /-- the difference region is closed away from `s` in the second state -/
  closed₂ : DeltaClosed T₂ (P.Delta Q s) s

namespace SyncInv

variable {P Q : DiamPath S} {T₁ T₂ : TreeState V} {s : V}

theorem notMem_Delta_of_lt_dist (hinv : SyncInv P Q T₁ T₂ s) {z : V} (hz : z ∈ T₁.alive)
    (hfar : 2 * (P.D - P.meetIdx Q) < T₁.graph.dist s z) : z ∉ P.Delta Q s :=
  fun hΔ => absurd (hinv.delta_bound₁ z hΔ hz) (by omega)

theorem notMem_Delta_of_lt_dist' (hinv : SyncInv P Q T₁ T₂ s) {z : V} (hz : z ∈ T₂.alive)
    (hfar : 2 * (P.D - P.meetIdx Q) < T₂.graph.dist s z) : z ∉ P.Delta Q s :=
  fun hΔ => absurd (hinv.delta_bound₂ z hΔ hz) (by omega)

/-- **The synchronised phase's key geometric fact.**  If the diameter of `T₁` is longer than `2r`,
then the whole diameter path starting at `s` avoids the difference region: the far endpoint is
outside `Δ` (`delta_bound₁`), and by the descent property no vertex of the path leading to it can be
inside `Δ`.  Consequently that path is a path of `T₂` as well (`exists_commonDiamPath`). -/
theorem notMem_Delta_of_diam (hinv : SyncInv P Q T₁ T₂ s) (Z : DiamPath T₁) (hZ : Z.p 0 = s)
    (hD : 2 * (P.D - P.meetIdx Q) < Z.D) : ∀ k ≤ Z.D, Z.seq k ∉ P.Delta Q s := by
  have hdist : ∀ k ≤ Z.D, T₁.graph.dist s (Z.seq k) = k := by
    intro k hk
    rw [← hZ, ← Z.seq_zero]
    exact dist_eq_of_seq T₁.acyclic (q := Z.seq) (n := k)
      (fun j hj => Z.seq_adj j (by omega))
      (fun j hj l hl h => Z.seq_inj j (by omega) l (by omega) h)
  have hfar : Z.seq Z.D ∉ P.Delta Q s := by
    refine hinv.notMem_Delta_of_lt_dist (Z.seq_mem Z.D) ?_
    rw [hdist Z.D (le_refl Z.D)]
    omega
  intro i hiD
  by_contra hi
  have key : ∀ l, i ≤ l → l ≤ Z.D → Z.seq l ∈ P.Delta Q s := by
    intro l hil
    induction l, hil using Nat.le_induction with
    | base => intro _; exact hi
    | succ l hil ih =>
        intro hl
        refine hinv.closed₁ (Z.seq_mem l) (Z.seq_mem (l + 1)) (ih (by omega))
          (Z.seq_adj l (by omega)) ?_
        rw [hdist (l + 1) (by omega), hdist l (by omega)]
  have hmem : Z.seq Z.D ∈ P.Delta Q s := key Z.D hiD (le_refl Z.D)
  exact hfar hmem

/-- **The same distances on the common part.**  Outside the difference region the two states have
the same distance from `s`: the geodesic from `s` to such a vertex avoids `Δ` (closure), so it is a
geodesic of both states.  This is the distance form of the agreement of the two states on `C`. -/
theorem dist_eq_of_notMem_Delta (hinv : SyncInv P Q T₁ T₂ s) {v : V} (hv : v ∈ T₁.alive)
    (hΔ : v ∉ P.Delta Q s) : T₁.graph.dist s v = T₂.graph.dist s v := by
  obtain ⟨q, hqpath, hqlen⟩ := (T₁.connected s hinv.end₁.mem v hv).exists_path_of_dist
  have hqΔ : ∀ k ≤ q.length, q.getVert k ∉ P.Delta Q s :=
    notMem_of_deltaClosed hinv.closed₁ hinv.end₁.mem hv hΔ hqpath
  have hadj : ∀ k < q.length, T₂.graph.Adj (q.getVert k) (q.getVert (k + 1)) := by
    intro k hk
    exact (hinv.adj_iff _ _ (hqΔ k (by omega)) (hqΔ (k + 1) (by omega))).mp
      (q.adj_getVert_succ hk)
  have hinj : ∀ k ≤ q.length, ∀ l ≤ q.length, q.getVert k = q.getVert l → k = l :=
    fun k hk l hl h => hqpath.getVert_injOn hk hl h
  have h2 := dist_eq_of_seq T₂.acyclic hadj hinj
  rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length] at h2
  exact (h2.trans hqlen).symm

/-- The same statement, read in the second state. -/
theorem dist_eq_of_notMem_Delta' (hinv : SyncInv P Q T₁ T₂ s) {v : V} (hv : v ∈ T₂.alive)
    (hΔ : v ∉ P.Delta Q s) : T₂.graph.dist s v = T₁.graph.dist s v := by
  obtain ⟨q, hqpath, hqlen⟩ := (T₂.connected s hinv.end₂.mem v hv).exists_path_of_dist
  have hqΔ : ∀ k ≤ q.length, q.getVert k ∉ P.Delta Q s :=
    notMem_of_deltaClosed hinv.closed₂ hinv.end₂.mem hv hΔ hqpath
  have hadj : ∀ k < q.length, T₁.graph.Adj (q.getVert k) (q.getVert (k + 1)) := by
    intro k hk
    exact (hinv.adj_iff _ _ (hqΔ k (by omega)) (hqΔ (k + 1) (by omega))).mpr
      (q.adj_getVert_succ hk)
  have hinj : ∀ k ≤ q.length, ∀ l ≤ q.length, q.getVert k = q.getVert l → k = l :=
    fun k hk l hl h => hqpath.getVert_injOn hk hl h
  have h1 := dist_eq_of_seq T₁.acyclic hadj hinj
  rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length] at h1
  exact (h1.trans hqlen).symm

/-- **A far diameter of `T₁` is a diameter of `T₂` with the same vertices.**  This is the object
folded simultaneously in the synchronised phase. -/
theorem exists_commonDiamPath (hinv : SyncInv P Q T₁ T₂ s) (Z : DiamPath T₁) (hZ : Z.p 0 = s)
    (hD : 2 * (P.D - P.meetIdx Q) < Z.D) :
    ∃ (Z₂ : DiamPath T₂) (h : Z₂.D = Z.D),
      ∀ i : Fin (Z.D + 1), Z₂.p (Fin.cast (congrArg Nat.succ h.symm) i) = Z.p i := by
  have hΔ := hinv.notMem_Delta_of_diam Z hZ hD
  have hΔ' : ∀ i : Fin (Z.D + 1), Z.p i ∉ P.Delta Q s := fun i => by
    rw [← Z.seq_val i]; exact hΔ (i : ℕ) (by have := i.isLt; omega)
  have hlast : T₂.graph.dist s (Z.p Z.last) = T₂.diam := by
    rw [← hinv.dist_eq_of_notMem_Delta (Z.mem Z.last) (hΔ' Z.last)]
    rw [← hZ]
    exact Z.isDiam.trans hinv.diam_eq
  refine ⟨⟨Z.D, Z.p, (fun i => (hinv.mem_iff _ (hΔ' i)).mp (Z.mem i)), Z.inj,
    (fun i => (hinv.adj_iff _ _ (hΔ' i.castSucc) (hΔ' i.succ)).mp (Z.adj i)), ?_⟩, rfl, ?_⟩
  · rw [hZ]
    exact hlast
  · intro i
    rfl

end SyncInv

/-- **A live vertex of `Δ` never lies on the `P`-diameter.**  If `v = p i` were live in
`P.foldState` and in `Δ`, then `v` would survive the fold (`2 * i ≤ D`) while the description of `Δ`
on the diameter (`seq_mem_Delta_iff`) forces `i > ℓ`; but `2 * r ≤ D` gives `ℓ ≥ D / 2`, a
contradiction.  Consequently `P.rep` is the identity on `Δ ∩ P.foldAlive`, which is the form in
which the closure of `Δ` in `P.foldState` will be proved. -/
theorem notMem_pathSet_of_mem_Delta_foldAlive (P Q : DiamPath S) {s : V} (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) {v : V} (hvA : v ∈ P.foldAlive) (hv : v ∈ P.Delta Q s) :
    v ∉ P.pathSet := by
  intro hvP
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hvP
  have hiD : (i : ℕ) ≤ P.D := by have := i.isLt; omega
  have hvi : v = P.seq (i : ℕ) := by rw [P.seq_val i]; exact hi.symm
  have hℓ : P.meetIdx Q < (i : ℕ) := (P.seq_mem_Delta_iff Q hP hQ hiD).mp (hvi ▸ hv)
  have hfix : P.rep (P.seq (i : ℕ)) = P.seq (i : ℕ) := by
    rw [← hvi]; exact (P.mem_foldAlive.mp hvA).2
  rw [P.rep_seq hiD] at hfix
  have hik : (i : ℕ) ≤ P.D - (i : ℕ) := by
    have hminD : min (i : ℕ) (P.D - (i : ℕ)) ≤ P.D := by omega
    have h := P.seq_inj (min (i : ℕ) (P.D - (i : ℕ))) hminD (i : ℕ) hiD hfix
    omega
  have htw := P.two_mul_tail_le Q hP hQ
  have hl := P.meetIdx_le Q
  omega

/-! ## 3. The synchronised step

While the common diameter `H` of the two states is larger than `2r`, a diameter of `T₁` starting at
`s` has its far endpoint outside `Δ`, so the whole path avoids `Δ` (§2) and is a path of `T₂` with
the same vertices.  `exists_sync_step` collects both objects: the path `Z` of `T₁` and its copy `Z₂`
in `T₂`, which are then folded simultaneously. -/

/-- **`Δ` is closed away from `s` in `S` itself.**  At the level of the tree `S` the closure of the
difference region is a consequence of the definition of `Δ` and the triangle inequality: if the path
from `s` to `w` leaves `v` on the side away from `s`, then the tail vertex witnessing `v ∈ Δ`
witnesses `w ∈ Δ` as well. -/
theorem mem_Delta_of_dist_eq_add {P Q : DiamPath S} {s v w : V} (hs : s ∈ S.alive)
    (hvS : v ∈ S.alive) (hv : v ∈ P.Delta Q s)
    (h : S.graph.dist s w = S.graph.dist s v + S.graph.dist v w) : w ∈ P.Delta Q s := by
  obtain ⟨t, ht, hdt⟩ := hv
  rcases P.mem_tailSet.mp ht with ⟨i, hi, hiD, rfl⟩ | ⟨j, hj, hjD, rfl⟩
  · have htA : P.seq i ∈ S.alive := P.seq_mem i
    have h1 : S.graph.dist s w ≤ S.graph.dist s (P.seq i) + S.graph.dist (P.seq i) w :=
      (S.connected s hs (P.seq i) htA).dist_triangle_left w
    have h2 : S.graph.dist (P.seq i) w ≤ S.graph.dist (P.seq i) v + S.graph.dist v w :=
      (S.connected (P.seq i) htA v hvS).dist_triangle_left w
    exact ⟨P.seq i, P.mem_tailSet.mpr (Or.inl ⟨i, hi, hiD, rfl⟩), by omega⟩
  · have htA : Q.seq j ∈ S.alive := Q.seq_mem j
    have h1 : S.graph.dist s w ≤ S.graph.dist s (Q.seq j) + S.graph.dist (Q.seq j) w :=
      (S.connected s hs (Q.seq j) htA).dist_triangle_left w
    have h2 : S.graph.dist (Q.seq j) w ≤ S.graph.dist (Q.seq j) v + S.graph.dist v w :=
      (S.connected (Q.seq j) htA v hvS).dist_triangle_left w
    exact ⟨Q.seq j, P.mem_tailSet.mpr (Or.inr ⟨j, hj, hjD, rfl⟩), by omega⟩

/-- A state of positive diameter has a pair of common diameter paths from any diameter endpoint:
take the same diameter path twice. -/
theorem commonEndgame_self (T : TreeState V) {s : V} (hs : IsDiamEnd T s) (hpos : 1 ≤ T.diam) :
    CommonEndgame T T s := by
  obtain ⟨Z, hZ⟩ := exists_diamPath_at T hs
  have hD : 1 ≤ Z.D := by rw [← Z.diam_eq_D]; exact hpos
  exact ⟨Z, Z, hD, hD, hZ, hZ, rfl⟩

/-- **The case `r = 0` of the headline: the two diameters coincide.**  If `ℓ = D` the two tails are
empty, so the two folding maps agree (`rep_eq_of_not_mem_tailSet` applied to the empty tail set) and
the two folded states are literally equal.  Both processes then stay equal (`m = 0`), and one
diameter path of that state starting at `s` serves as both `Z₁` and `Z₂`. -/
theorem foldState_eq_of_tail_eq_zero (P Q : DiamPath S) {s : V} (hP : P.p 0 = s) (hQ : Q.p 0 = s)
    (h0 : P.D - P.meetIdx Q = 0) : P.foldState = Q.foldState := by
  have hℓ : P.meetIdx Q = P.D := by have := P.meetIdx_le Q; omega
  have hrep : ∀ x : V, P.rep x = Q.rep x := fun x =>
    P.rep_eq_of_not_mem_tailSet Q hP hQ (fun hx => by
      rcases P.mem_tailSet.mp hx with ⟨i, hi, hiD, -⟩ | ⟨j, hj, hjD, -⟩ <;> omega)
  refine TreeState.ext ?_ ?_
  · show P.foldAlive = Q.foldAlive
    ext x
    rw [P.mem_foldAlive, Q.mem_foldAlive, hrep x]
  · show P.foldGraph = Q.foldGraph
    ext u v
    simp only [P.foldGraph_adj, Q.foldGraph_adj, P.mem_foldAlive, Q.mem_foldAlive, hrep]

/-- **The `r = 0` instance of the headline statement**: with `m = 0` and both states equal to
`P.foldState = Q.foldState`, `CommonEndgame` reduces to the existence of one diameter path of
positive length starting at `s`, which is the nondegeneracy hypothesis `1 ≤ P.foldState.diam`. -/
theorem exists_commonEndgame_of_diam_of_tail_eq_zero (P Q : DiamPath S) {s : V} (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) (h0 : P.D - P.meetIdx Q = 0) (hpos : 1 ≤ P.foldState.diam) :
    ∃ m T₁ T₂, FoldSeqAt s P.foldState T₁ m ∧ FoldSeqAt s Q.foldState T₂ m ∧
      CommonEndgame T₁ T₂ s := by
  have hstate := P.foldState_eq_of_tail_eq_zero Q hP hQ h0
  have hself : CommonEndgame P.foldState P.foldState s :=
    commonEndgame_self P.foldState (by rw [← hP]; exact isDiamEnd_foldState P) hpos
  refine ⟨0, P.foldState, Q.foldState, FoldSeqAt.refl _, FoldSeqAt.refl _, ?_⟩
  rw [show Q.foldState = P.foldState from hstate.symm]
  exact hself

variable {P Q : DiamPath S} {T₁ T₂ : TreeState V} {s : V}

/-- **The synchronised step.**  While the common diameter `H` of the two states is larger than `2r`,
there is a diameter `Z` of `T₁` starting at `s` whose vertices avoid the difference region, and the
same vertex sequence is a diameter of `T₂`.  Folding both states along `Z` is the synchronised step
of `REF.md` §7; the two resulting states are `Z.foldState` and `Z₂.foldState`. -/
theorem exists_sync_step (hinv : SyncInv P Q T₁ T₂ s) (hH : 2 * (P.D - P.meetIdx Q) < T₁.diam) :
    ∃ (Z : DiamPath T₁) (Z₂ : DiamPath T₂) (h : Z₂.D = Z.D),
      Z.p 0 = s ∧ Z.D = T₁.diam ∧
        (∀ i : Fin (Z.D + 1), Z₂.p (Fin.cast (congrArg Nat.succ h.symm) i) = Z.p i) ∧
        (∀ k ≤ Z.D, Z.seq k ∉ P.Delta Q s) := by
  obtain ⟨Z, hZ⟩ := exists_diamPath_at T₁ hinv.end₁
  have hZdiam : Z.D = T₁.diam := Z.diam_eq_D.symm
  have hfar : 2 * (P.D - P.meetIdx Q) < Z.D := by rw [hZdiam]; exact hH
  obtain ⟨Z₂, hD, hp⟩ := hinv.exists_commonDiamPath Z hZ hfar
  exact ⟨Z, Z₂, hD, hZ, hZdiam, hp, hinv.notMem_Delta_of_diam Z hZ hfar⟩

/-- **The `H = 2 r` case of the headline statement** (the synchronised phase is empty): both folded
states are at once at the endgame, and `ExchangeProof.endgame_of_diam` folds them onto a common
state.  This is the `m = 0` instance of the statement proved in this file; the remaining case is the
synchronised phase proper (`2 * r < T₁.diam`). -/
theorem exists_commonEndgame_of_diam_of_diam_eq (P Q : DiamPath S) {s : V} (hP : P.p 0 = s)
    (hQ : Q.p 0 = s) (hr : 1 ≤ P.D - P.meetIdx Q)
    (hdiam : P.foldState.diam = Q.foldState.diam)
    (hH : P.foldState.diam = 2 * (P.D - P.meetIdx Q)) :
    ∃ m T₁ T₂, FoldSeqAt s P.foldState T₁ m ∧ FoldSeqAt s Q.foldState T₂ m ∧
      CommonEndgame T₁ T₂ s :=
  ⟨0, P.foldState, Q.foldState, FoldSeqAt.refl _, FoldSeqAt.refl _,
    endgame_of_diam P Q hP hQ hr hH (by rw [← hdiam]; exact hH)
      (P.meetIdx_comm Q (hP.trans hQ.symm)) (P.D_eq Q)⟩

/-! ## 4. Degenerate cases and the completed synchronised proof

An unconditional claim that the two first-fold states eventually admit a common *further fold*
is false: folding a single edge already leaves a singleton, from which no legal fold exists.
The immediate endgame lemmas above therefore include nondegeneracy hypotheses.

`DiamPath.synchronized_exchange` is expressed instead through equal-length completions.
For coincident diameters it uses `foldState_eq_of_tail_eq_zero`, including singleton results.
For positive tail length it uses `SyncCtx.reach_scale` and `SyncCtx.commonEndgame`.
The former terminates by live vertex count while preserving legs of length `2r`; the latter
compares the full composite maps `psi₁ ∘ sigma ∘ P.rep` and `psi₂ ∘ sigma ∘ Q.rep`, not merely
the visible tails. These results are proved in `SyncStep.lean` and `SyncEndgame.lean`. -/

end DiamPath

end OhtoaiTreeProof
