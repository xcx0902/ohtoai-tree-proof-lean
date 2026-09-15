/-
Executable entry point for the `ohtoai-tree-proof` project.

The mathematical content lives in the library `OhtoaiTreeProof`; see `REF.md` for the
statement being formalized and `README.md` for the current status of the formalization.
-/
import OhtoaiTreeProof

open OhtoaiTreeProof

def main : IO Unit := do
  IO.println "ohtoai-tree-proof: formalization of the tree-folding theorem of REF.md."
  IO.println ""
  IO.println "Statement formalized (OhtoaiTreeProof.fold_count_unique):"
  IO.println "  For a tree G, every maximal sequence of folds along a diameter,"
  IO.println "  run until the tree has a single vertex, has the same length."
  IO.println ""
  IO.println "See README.md for the correspondence with the lemmas of REF.md."
