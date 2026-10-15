module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Species.Operations.Operations
public import Species.Isomorphism
public import Species.Instances.Instances
public import Species.Basic

@[expose] public section

namespace Species

def deriv_E_bij {U: Type} [Finite U] : Deriv E U ≃ E U where
  toFun     x := ⟨⟩
  invFun    x := ⟨⟩
  right_inv x := rfl
  left_inv    := by unfold Species.Deriv; intro x; simp

def deriv_E_iso {U: Type} [Finite U] : Iso (Deriv E) E where
  equiv      _   := deriv_E_bij
  naturality _ _ := rfl

end Species
end
