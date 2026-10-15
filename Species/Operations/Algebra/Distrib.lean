module

public import Species.Basic
public import Species.Operations.Add
public import Species.Operations.Mul
public import Species.Instances.One
public import Species.Instances.Zero

@[expose] public section

namespace Species

def leftDistrib {F G H: Type → Type} [Species F] [Species G] [Species H] {U} [Finite U]
: Mul F (Add G H) U ≃ Add (Mul F G) (Mul F H) U where
  toFun := by
    unfold Add Mul; simp
    rintro ⟨d,⟨f, (g | h)⟩⟩
    case inl => apply Sum.inl; exact ⟨d, f, g⟩
    case inr => apply Sum.inr; exact ⟨d, f, h⟩
  invFun := by
    unfold Add Mul; simp
    rintro (⟨d, f, g⟩ | ⟨d, f, h⟩)
    case inl => exact ⟨d, f, Sum.inl g⟩
    case inr => exact ⟨d, f, Sum.inr h⟩
  left_inv  := by unfold Add Mul; rintro ⟨d, f, (g | h)⟩ <;> simp
  right_inv := by unfold Add Mul; rintro ⟨d, f, g⟩ <;> simp

def rightDistrib {F G H: Type → Type} [Species F] [Species G] [Species H] {U} [Finite U]
: Mul (Add F G) H U ≃ Add (Mul F H) (Mul G H) U where
  toFun := by
    unfold Add Mul; rintro ⟨d, (f | g), h⟩
    case inl => apply Sum.inl; exact ⟨d, f, h⟩
    case inr => apply Sum.inr; exact ⟨d, g, h⟩
  invFun := by
    unfold Add Mul; simp; rintro (⟨d, f, h⟩ | ⟨d, g, h⟩)
    case inl => exact ⟨d, Sum.inl f, h⟩
    case inr => exact ⟨d, Sum.inr g, h⟩
  left_inv  := by unfold Add Mul; simp; rintro ⟨d, (Fstrut | Gstrut), Hsturt⟩ <;> simp
  right_inv := by unfold Add Mul; simp; rintro (⟨d, f, h⟩ | ⟨d, g, h⟩) <;> simp

end Species
end
