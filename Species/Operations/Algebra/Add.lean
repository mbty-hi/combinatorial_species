import Species.Basic
import Species.Operations.Add
import Species.Instances.One
import Species.Instances.Zero

/- TODO in this folder: isomorphism instead of mere equiv -/

namespace Species

variable {U: Type} [Fintype U] {F G H: Type → Type} [Species F] [Species G] [Species H]

def addZero : (Add F Zero) U ≃ F U where
  toFun
    | .inl x => x
    | .inr x => nomatch x
  invFun    := .inl
  left_inv  := by rintro (_ | x); rfl; nomatch x
  right_inv := by simp only [Function.RightInverse, Function.LeftInverse, implies_true]

def zeroAdd : (Add Zero F) U ≃ F U where
  toFun
    | .inl x => nomatch x
    | .inr x => x
  invFun    := .inr
  left_inv  := by rintro (x | _); nomatch x; rfl
  right_inv := by simp only [Function.RightInverse, Function.LeftInverse, implies_true]

def addAssoc : (Add (Add F G) H) U ≃ (Add F (Add G H)) U where
  toFun := by
    unfold Add
    rintro ((foo | bar) | baz)
    · exact (Sum.inl foo)
    · exact (Sum.inr (Sum.inl bar))
    · exact (Sum.inr (Sum.inr baz))
  invFun := by
    unfold Add
    rintro (foo | bar | baz)
    · exact (Sum.inl (Sum.inl foo))
    · exact (Sum.inl (Sum.inr bar))
    · exact (Sum.inr baz)
  left_inv  := by rintro ((foo | bar) | baz) <;> rfl
  right_inv := by rintro ( foo | bar  | baz) <;> rfl

def addComm : Add F G U ≃ Add G F U where
  toFun := by
    unfold Add
    rintro (foo | bar)
    · exact Sum.inr foo
    · exact Sum.inl bar
  invFun := by
    unfold Add
    rintro (foo | bar)
    · exact Sum.inr foo
    · exact Sum.inl bar
  left_inv  := by rintro (foo | bar) <;> rfl
  right_inv := by rintro (foo | bar) <;> rfl

end Species
