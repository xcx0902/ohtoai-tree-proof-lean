import OhtoaiTreeProof.MainTheorem

/-! These checks fail the build if the proof chain acquires any additional axiom.
The module-wide check also covers auxiliary declarations unused by the main theorem. -/

run_cmd do
  let env ← Lean.getEnv
  let mut checked := 0
  for (name, _) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      if (`OhtoaiTreeProof).isPrefixOf env.allImportedModuleNames[idx.toNat]! then
        checked := checked + 1
        for axiomName in ← Lean.collectAxioms name do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "{name} depends on unexpected axiom {axiomName}"
  if checked == 0 then
    throwError "No project declarations were found for the axiom audit"

/-- info: 'OhtoaiTreeProof.exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OhtoaiTreeProof.exchange

/-- info: 'OhtoaiTreeProof.LValue_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OhtoaiTreeProof.LValue_unique

/-- info: 'OhtoaiTreeProof.Phi_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OhtoaiTreeProof.Phi_step

/-- info: 'OhtoaiTreeProof.fold_count_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OhtoaiTreeProof.fold_count_unique

/-- info: 'OhtoaiTreeProof.fold_count_unique_of_isTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OhtoaiTreeProof.fold_count_unique_of_isTree

/-- info: 'OhtoaiTreeProof.exists_complete_foldSeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OhtoaiTreeProof.exists_complete_foldSeq

/-- info: 'OhtoaiTreeProof.exists_complete_foldSeq_of_isTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OhtoaiTreeProof.exists_complete_foldSeq_of_isTree

/-! Model boundary checks: prefixes are allowed, but singleton operations are not counted. -/

open OhtoaiTreeProof

example {V : Type*} [Fintype V] [DecidableEq V] (S : TreeState V) (s : V) :
    FoldSeqAt s S S 0 := .refl S

example {V : Type*} [Fintype V] [DecidableEq V] {S S' : TreeState V}
    (hs : IsSingle S) (n : ℕ) : ¬ FoldSeq S S' (n + 1) := by
  intro h
  cases h with
  | step hpos _ _ => unfold IsSingle at hs; omega

example {V : Type*} [Fintype V] [DecidableEq V] {S S' : TreeState V} {n : ℕ}
    (h : FoldSeq S S' n) (hne : S.alive.Nonempty) : n < S.alive.card := by
  have := h.card_add_length_le
  have := Finset.card_pos.mpr (h.alive_nonempty hne)
  omega
