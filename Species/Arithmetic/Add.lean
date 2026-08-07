import Species.Basic
import Species.Operations.Add
import Species.Instances.One
import Species.Instances.Zero

namespace Species
  def add_zero (S: Type → Type) U : (Species.add S SZero) U ≃ S U where
    toFun
      | .inl x => x
      | .inr x => nomatch x
    invFun    := .inl
    left_inv  := by simp [Function.LeftInverse]; rintro (_ | x); simp; nomatch x
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]

  def zero_add (S: Type → Type) U : (Species.add SZero S) U ≃ S U where
    toFun
      | .inl x => nomatch x
      | .inr x => x
    invFun    := .inr
    left_inv  := by simp [Function.LeftInverse]; rintro (x | _); nomatch x; simp
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
end Species
