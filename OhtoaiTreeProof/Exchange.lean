/-
# The two structural lemmas of `REF.md`, and the reductions they support

This file isolates the two structural statements that the whole proof rests on, states them
faithfully, and derives from them

* `LValue_unique` — `REF.md` Proposition 1 (§8): the length of the fixed-endpoint process is
  independent of the choices made, and
* `Phi_exists` — the fixed-endpoint process always terminates (so that the value `Phi` of a state
  is well defined).

The two structural statements are

* **Lemma 3** (`REF.md` §5), `isDiamEnd_foldState`: folding towards a diameter endpoint `s` keeps
  `s` a diameter endpoint of the folded tree, and
* **Lemma 5** (`REF.md` §7), `exchange`: from the two trees `T_x`, `T_y` obtained by folding
  towards `s` along two different diameters, the same number of further folds towards `s` leads to
  the same rooted tree.

Lemma 3 is proved in `OhtoaiTreeProof/Cone.lean` (from the height bound of Lemma 1 and the cone
lemma of Lemma 2, `REF.md` §3–§5); the only `sorry` left here is Lemma 5.
-/
import OhtoaiTreeProof.Cone
import OhtoaiTreeProof.PathExists
import OhtoaiTreeProof.Progress

set_option linter.unusedSectionVars false

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Lemma 5 of `REF.md`: the delayed exchange lemma -/

/-- **REF.md Lemma 5 (§7, delayed exchange lemma).**  Let `s` be a diameter endpoint, and let
`T_x`, `T_y` be the trees obtained by folding towards `s` along two diameters starting at `s`.
Then, continuing to fold only towards `s`, the two trees can be brought to the same rooted tree
after the same number of operations.

`REF.md` proves this by writing the two diameters as a common path `s = p 0, …, p ℓ = w` followed
by two tails `w = a 0, …, a r = x` and `w = b 0, …, b r = y` of equal length (`ℓ = D - r`, since
both are diameters): after folding along one of them the vertex `a t` sits at depth `r - t`, i.e.
it is identified with `p (r - t)`, and the two trees differ only inside the ball of radius `r`
around `w` — a ball that is destroyed by the first `r` further folds, all of which act on both
trees in the same way. -/
theorem exchange {S : TreeState V} {s : V} (hs : IsDiamEnd S s) (P Q : DiamPath S)
    (hP : P.p 0 = s) (hQ : Q.p 0 = s) :
    ∃ n : ℕ, LValue P.foldState s n ∧ LValue Q.foldState s n := by
  sorry

/-! ## Proposition 1 of `REF.md`: uniqueness for a fixed endpoint -/

/-- **REF.md Proposition 1 (§8).**  When one always folds towards a fixed diameter endpoint `s`,
the number of operations needed to reach a single vertex is independent of the choices made.

The proof is the induction on the number of vertices described in `REF.md` §8: two processes
differing in their first step have, by the exchange Lemma 5, completions of the same length from
the two possible first-fold results; the induction hypothesis (applied to those smaller trees,
which are legitimate states by Lemma 3) identifies the lengths of the remainders. -/
theorem LValue_unique : ∀ (N : ℕ) (S S₁ S₂ : TreeState V) (s : V) (n m : ℕ),
    S.alive.card ≤ N → IsDiamEnd S s → FoldSeqAt s S S₁ n → FoldSeqAt s S S₂ m →
    IsSingle S₁ → IsSingle S₂ → n = m := by
  intro N
  induction N with
  | zero =>
      intro S S₁ S₂ s n m hcard hs h₁ h₂ hs₁ hs₂
      exact absurd (Finset.card_pos.mpr ⟨s, hs.1⟩) (by omega)
  | succ N ih =>
      intro S S₁ S₂ s n m hcard hs h₁ h₂ hs₁ hs₂
      cases h₁ with
      | refl =>
          cases h₂ with
          | refl => rfl
          | step hpos _ _ =>
              have hs₁' : S.alive.card ≤ 1 := hs₁
              omega
      | step hpos hstep hrest =>
          cases h₂ with
          | refl =>
              have hs₂' : S.alive.card ≤ 1 := hs₂
              omega
          | step hpos₂ hstep₂ hrest₂ =>
              obtain ⟨P, hP, rfl⟩ := hstep
              obtain ⟨Q, hQ, rfl⟩ := hstep₂
              obtain ⟨k, hkP, hkQ⟩ := exchange hs P Q hP hQ
              obtain ⟨S₁', hS₁', hsingle₁⟩ := hkP
              obtain ⟨S₂', hS₂', hsingle₂⟩ := hkQ
              have hcardP : P.foldState.alive.card ≤ N := by
                have := FoldStep.card_lt (S := S) (S' := P.foldState) ⟨P, rfl⟩ hpos
                omega
              have hcardQ : Q.foldState.alive.card ≤ N := by
                have := FoldStep.card_lt (S := S) (S' := Q.foldState) ⟨Q, rfl⟩ hpos
                omega
              have hEndP : IsDiamEnd P.foldState s := by
                rw [← hP]; exact isDiamEnd_foldState P
              have hEndQ : IsDiamEnd Q.foldState s := by
                rw [← hQ]; exact isDiamEnd_foldState Q
              have e₁ := ih P.foldState S₁ S₁' s _ k hcardP hEndP hrest hS₁' hs₁ hsingle₁
              have e₂ := ih Q.foldState S₂ S₂' s _ k hcardQ hEndQ hrest₂ hS₂' hs₂ hsingle₂
              omega

/-! ## The value of a state is well defined -/

/-- The fixed-endpoint process always terminates: from any state with at least two vertices there
is a diameter endpoint `s` and a complete process folding towards `s`.  This is the induction on
the number of vertices: one fold towards any diameter endpoint `s` removes at least the vertex at
the far end of the diameter (`DiamPath.foldState_card_lt`), and by Lemma 3 the image of `s` is
still a diameter endpoint, so the process can be continued on the smaller tree. -/
theorem LValue_exists_of_isDiamEnd : ∀ (N : ℕ) (S : TreeState V) (s : V),
    S.alive.card ≤ N → IsDiamEnd S s → ∃ n : ℕ, LValue S s n := by
  intro N
  induction N with
  | zero =>
      intro S s hcard hs
      exact absurd (Finset.card_pos.mpr ⟨s, hs.1⟩) (by omega)
  | succ N ih =>
      intro S s hcard hs
      by_cases hsingle : S.alive.card ≤ 1
      · exact ⟨0, S, FoldSeqAt.refl S, hsingle⟩
      · have hpos : 2 ≤ S.alive.card := by omega
        obtain ⟨P, hP⟩ := exists_diamPath_at S hs
        have hlt : P.foldState.alive.card ≤ N := by
          have := FoldStep.card_lt (S := S) (S' := P.foldState) ⟨P, rfl⟩ hpos
          omega
        have hEnd : IsDiamEnd P.foldState s := by
          rw [← hP]; exact isDiamEnd_foldState P
        obtain ⟨n', S'', hseq, hsingle'⟩ := ih P.foldState s hlt hEnd
        exact ⟨n' + 1, S'', FoldSeqAt.step hpos ⟨P, hP, rfl⟩ hseq, hsingle'⟩

theorem Phi_exists (S : TreeState V) (h : ¬S.alive.card ≤ 1) :
    ∃ s : V, IsDiamEnd S s ∧ ∃ n : ℕ, LValue S s n := by
  have hne : S.alive.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨s, hs⟩ := exists_isDiamEnd hne
  exact ⟨s, hs, LValue_exists_of_isDiamEnd S.alive.card S s le_rfl hs⟩

end OhtoaiTreeProof
