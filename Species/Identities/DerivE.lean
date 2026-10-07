import Mathlib.Logic.Equiv.Fin.Rotate
import Species.Operations.Operations
import Species.Instances.Instances
import Species.Basic

namespace Species

def deriv_E {U: Type} [Finite U] : Deriv E U ≃ E U where
  toFun     x := ⟨⟩
  invFun    x := ⟨⟩
  right_inv x := rfl
  left_inv    := by unfold Species.Deriv; intro x; simp

end Species
