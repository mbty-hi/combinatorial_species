module

public import Species.Basic
public import Species.Isomorphism
public import Species.Operations.Add
public import Species.Instances.One
public import Species.Instances.Zero

@[expose] public section

namespace Species

variable {U: Type} [Fintype U] {F G H: Type → Type} [Species F] [Species G] [Species H]

def addZeroEquiv : (Add F Zero) U ≃ F U where
  toFun
    | .inl x => x
    | .inr x => nomatch x
  invFun      := .inl
  left_inv    := by rintro (_ | x); rfl; nomatch x
  right_inv _ := rfl

def addZero : Iso (Add F Zero) F where
  equiv      U   := addZeroEquiv
  naturality σ s := by rcases s with fu | z; rfl; nomatch z

def zeroAddEquiv : (Add Zero F) U ≃ F U where
  toFun
    | .inl x => nomatch x
    | .inr x => x
  invFun      := .inr
  left_inv    := by rintro (x | _); nomatch x; rfl
  right_inv _ := rfl

def zeroAdd : Iso (Add Zero F) F where
  equiv      U   := zeroAddEquiv
  naturality σ s := by rcases s with z | fu; nomatch z; rfl

def addAssocEquiv : (Add (Add F G) H) U ≃ (Add F (Add G H)) U where
  toFun := by
    unfold Add
    rintro ((fu | gu) | hu)
    · exact (Sum.inl fu)
    · exact (Sum.inr (Sum.inl gu))
    · exact (Sum.inr (Sum.inr hu))
  invFun := by
    unfold Add
    rintro (fu | gu | hu)
    · exact (Sum.inl (Sum.inl fu))
    · exact (Sum.inl (Sum.inr gu))
    · exact (Sum.inr hu)
  left_inv  := by rintro ((fu | gu) | hu)  <;> rfl
  right_inv := by rintro ( fu | (gu | hu)) <;> rfl

def addAssoc : Iso (Add (Add F G) H) (Add F (Add G H)) where
  equiv      U   := addAssocEquiv
  naturality σ s := by rcases s with (fu | gu) | hu <;> rfl

def addCommEquiv : Add F G U ≃ Add G F U where
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

def addComm : Iso (Add F G) (Add G F) where
  equiv      U   := addCommEquiv
  naturality σ s := by cases s <;> rfl

end Species
end
