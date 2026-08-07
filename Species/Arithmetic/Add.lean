import Species.Basic
import Species.Operations.Add
import Species.Instances.One
import Species.Instances.Zero

namespace Species
  def add_zero (S: Type → Type) U : (Species.add S SZero) U ≃ S U where
    toFun
      | .inl s => s
      | .inr e => nomatch e
    invFun := fun s => .inl s
    left_inv  := by simp [Function.LeftInverse]; rintro (_ | x); simp; nomatch x
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
end Species
