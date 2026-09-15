import OhtoaiTreeProof.Basic

set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

namespace OhtoaiTreeProof
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace DiamPath
variable {S : TreeState V} (P : DiamPath S)

def mirror (i : Fin P.D) : Fin P.D := ⟨P.D - 1 - (i : ℕ), by omega⟩

@[simp] theorem mirror_val (i : Fin P.D) : (P.mirror i : ℕ) = P.D - 1 - (i : ℕ) := rfl

example (i : Fin P.D) (hi2 : P.D / 2 ≤ (i : ℕ)) (hne' : P.mirror i ≠ i) :
    ¬ (P.D / 2 ≤ (P.mirror i : ℕ)) := by
  have hlt : P.D - 1 - (i : ℕ) < (i : ℕ) := by
    have hle : P.D - 1 - (i : ℕ) ≤ (i : ℕ) := by omega
    have hne : P.D - 1 - (i : ℕ) ≠ (i : ℕ) := fun hh => hne' (Fin.ext hh)
    omega
  show ¬ (P.D / 2 ≤ P.D - 1 - (i : ℕ))
  omega

end DiamPath
end OhtoaiTreeProof
