import Species.Basic
import Species.Operations.Add
import Species.Instances.One
import Species.Instances.Zero

namespace AddArith
  def add_zero (S: Type → Type) U : (Species.add S SZero) U ≃ S U where
    toFun
      | .inl s => s
      | .inr e => nomatch e
    invFun := fun s => .inl s
    left_inv := by
      unfold Function.LeftInverse; simp
      intros sa
      match sa with
      | .inl x => simp
      | .inr => 
    right_inv := sorry
end AddArith
