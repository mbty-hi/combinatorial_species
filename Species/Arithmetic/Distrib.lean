import Species.Basic
import Species.Operations.Add
import Species.Operations.Mul
import Species.Instances.One
import Species.Instances.Zero

namespace Species

def left_distrib {F G H: Type → Type} [Species F] [Species G] [Species H] {U} [Finite U] :
Species.mul F (Species.add G H) U ≃ Species.add (Species.mul F G) (Species.mul F H) U where
  toFun := by
    unfold add mul
    simp
    rintro ⟨d,⟨Fstrut, (Gstrut | Hstrut)⟩⟩
    case inl => constructor; exact ⟨d,Fstrut,Gstrut⟩
    case inr => apply Sum.inr; exact ⟨d,Fstrut,Hstrut⟩
  invFun := by
    unfold add mul
    simp
    rintro (⟨d, Fstrut, Gstrut⟩ | ⟨d, Fstrut, Hstrut⟩)
    case inl => exact ⟨d,Fstrut, Sum.inl Gstrut⟩
    case inr => exact ⟨d,Fstrut, Sum.inr Hstrut⟩
  left_inv := by
    unfold add mul
    rintro ⟨d,Fstrut,(Gstrut | Hstrut)⟩
    <;> simp
  right_inv := by
    unfold add mul
    rintro ⟨d,Fstrut, Gstrut⟩
    <;> simp

def right_distrib {F G H: Type → Type} [Species F] [Species G] [Species H] {U} [Finite U] :
Species.mul (Species.add F G) H U ≃ Species.add (Species.mul F H) (Species.mul G H) U where
  toFun := by
    unfold add mul
    rintro ⟨d, (Fstrut | Gstrut), Hstrut⟩
    case inl => constructor; exact ⟨d, Fstrut, Hstrut⟩
    case inr => apply Sum.inr; exact ⟨d, Gstrut, Hstrut⟩
  invFun := by
    unfold add mul
    simp
    rintro (⟨d,Fsturt, Hstrut⟩ | ⟨d,Gsturt, Hstrut⟩)
    case inl => exact ⟨d, Sum.inl Fsturt, Hstrut⟩
    case inr => exact ⟨d, Sum.inr Gsturt, Hstrut⟩
  left_inv := by
    unfold add mul
    simp
    rintro ⟨d, (Fstrut | Gstrut), Hsturt⟩
    <;> simp
  right_inv := by
    unfold add mul
    simp
    rintro (⟨d,Fstrut, Hstrut⟩ | ⟨d, Gstrut, Hstrut⟩)
    <;> simp

end Species
