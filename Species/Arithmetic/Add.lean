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

  def add_assoc (F G H: Type → Type) U : (Species.add (Species.add F G) H) U
  ≃ (Species.add F (Species.add G H)) U where
    toFun := by
      unfold add
      rintro ((foo | bar) | baz)
      . exact (Sum.inl foo)
      . exact (Sum.inr (Sum.inl bar))
      . exact (Sum.inr (Sum.inr baz))

    invFun := by
      unfold add
      rintro (foo | bar | baz)
      . exact (Sum.inl (Sum.inl foo))
      . exact (Sum.inl (Sum.inr bar))
      . exact (Sum.inr baz)
    left_inv := by rintro ((foo | bar) | baz) <;> simp
    right_inv := by rintro (foo | bar | baz) <;> simp

  def add_comm (F G : Type → Type) U : Species.add F G U ≃ Species.add G F U where
    toFun := by
      unfold add
      rintro (foo | bar)
      . exact Sum.inr foo
      . exact Sum.inl bar
    invFun := by
      unfold add
      rintro (foo | bar)
      . exact Sum.inr foo
      . exact Sum.inl bar
    left_inv := by rintro (foo | bar) <;> simp
    right_inv := by rintro (foo | bar) <;> simp
end Species
