import Species.Basic
import Species.Operations.Add
import Species.Instances.One
import Species.Instances.Zero

namespace Species

variable {U: Type} [Fintype U] {F G H: Type → Type} [Species F] [Species G] [Species H]

def add_zero : (Add F Zero) U ≃ F U where
  toFun
    | .inl x => x
    | .inr x => nomatch x
  invFun    := .inl
  left_inv  := by simp [Function.LeftInverse]; rintro (_ | x); simp; nomatch x
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

def zero_add : (Add Zero F) U ≃ F U where
  toFun
    | .inl x => nomatch x
    | .inr x => x
  invFun    := .inr
  left_inv  := by simp [Function.LeftInverse]; rintro (x | _); nomatch x; simp
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

def add_assoc : (Add (Add F G) H) U ≃ (Add F (Add G H)) U where
  toFun := by
    unfold Add
    rintro ((foo | bar) | baz)
    . exact (Sum.inl foo)
    . exact (Sum.inr (Sum.inl bar))
    . exact (Sum.inr (Sum.inr baz))
  invFun := by
    unfold Add
    rintro (foo | bar | baz)
    . exact (Sum.inl (Sum.inl foo))
    . exact (Sum.inl (Sum.inr bar))
    . exact (Sum.inr baz)
  left_inv  := by rintro ((foo | bar) | baz) <;> simp
  right_inv := by rintro ( foo | bar  | baz) <;> simp

def add_comm : Add F G U ≃ Add G F U where
  toFun := by
    unfold Add
    rintro (foo | bar)
    . exact Sum.inr foo
    . exact Sum.inl bar
  invFun := by
    unfold Add
    rintro (foo | bar)
    . exact Sum.inr foo
    . exact Sum.inl bar
  left_inv  := by rintro (foo | bar) <;> simp
  right_inv := by rintro (foo | bar) <;> simp

end Species
