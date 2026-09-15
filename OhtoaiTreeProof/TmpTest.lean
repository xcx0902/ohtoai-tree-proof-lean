import OhtoaiTreeProof.Basic

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace OhtoaiTreeProof

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

example (S : TreeState V) (e : Sym2 V) : e ∈ S.graph.edgeFinset ↔ e ∈ S.graph.edgeSet :=
  S.graph.mem_edgeFinset

end OhtoaiTreeProof
