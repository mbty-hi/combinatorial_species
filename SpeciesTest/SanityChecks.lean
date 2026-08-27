import Species.Operations.Operations
import Species.Instances.Instances
import Species.Basic

open Species

variable {F G : Type -> Type} [Species F] [Species G] {U: Type} [Finite U]

def deriv_E: Deriv E U ≃ E U where
  toFun     x := ⟨⟩
  invFun    x := ⟨⟩
  right_inv x := rfl
  left_inv    := by unfold Species.Deriv; intro x; simp

-- TODO
/- def deriv_Cycle_is_LinearOrder: Deriv C U ≃ L U where -/
/-   toFun := sorry -/
/-   invFun      := sorry -/
/-   right_inv   := by sorry -/
/-   left_inv    := by sorry -/
