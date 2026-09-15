import OhtoaiTreeProof.MainTheorem

/-! These checks fail the build if the proof chain acquires any additional axiom. -/

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
