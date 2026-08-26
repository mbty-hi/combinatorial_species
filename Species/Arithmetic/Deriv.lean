import Species.Basic
import Species.Operations.Deriv
import Species.Operations.Add
import Species.Operations.Mul

namespace Species

variable {U: Type} [Fintype U] {F G: Type → Type} [Species F] [Species G]

def leibniz_add : Deriv (add F G) U ≃ add (Deriv F) (Deriv G) U where
  toFun := by
    unfold Deriv add; rintro (f | g)
    . left; exact f
    . right; exact g
  invFun := by
    unfold Deriv add; rintro (f | g)
    . left; exact f
    . right; exact g
  left_inv  := by simp [Function.LeftInverse, Deriv, add]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, Deriv, add]

/- def leibniz_mul : Deriv (mul F G) U ≃ add (mul (Deriv F) G) (mul F (Deriv G)) U where -/
/-   toFun := by -/
/-     unfold Deriv add mul; rintro ⟨d, f, g⟩ -/
/-     . left; exact f -/
/-     . right; exact g -/
/-   invFun := by -/
/-     unfold Deriv add; rintro (f | g) -/
/-     . left; exact f -/
/-     . right; exact g -/
/-   left_inv  := by simp [Function.LeftInverse, Deriv, add] -/
/-   right_inv := by simp [Function.RightInverse, Function.LeftInverse, Deriv, add] -/

end Species
