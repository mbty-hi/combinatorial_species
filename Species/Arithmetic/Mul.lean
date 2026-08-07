import Species.Basic
import Species.Operations.Mul
import Species.Instances.One
import Species.Instances.Zero

namespace Species
  def one_mul (S: Type → Type) U : (Species.mul SOne S) U ≃ S U where
    toFun := by
      unfold mul
      unfold SOne
      rintro ⟨d,fst,snd⟩
      have h : { u // d u = false } = U := by sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry
end Species
