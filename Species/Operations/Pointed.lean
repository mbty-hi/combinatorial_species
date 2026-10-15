module

public import Species.Basic
public import Species.Computable
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section

namespace Species

def Pointed (F : Type → Type) (U : Type) : Type := U × F U

namespace Pointed

variable {F : Type → Type} [Species F] {U : Type}

section Display

/-- Display as `(•point, struct)`. -/
instance instRepr [Repr U] [Repr (F U)] : Repr (Pointed F U) where
  reprPrec x _ := "(•" ++ repr x.1 ++ ", " ++ repr x.2 ++ ")"

/-- Order: point first, then structure. -/
instance instLinearOrder [LinearOrder U] [LinearOrder (F U)] : LinearOrder (Pointed F U) :=
  LinearOrder.lift' (fun x : U × F U => toLex x) toLex.injective

end Display

instance instSpecies : Species (Pointed F) where
  finite := by
    intros U _; unfold Pointed
    have _ := Species.finite (F := F) (U := U)
    infer_instance
  transport      := fun {U V} _ _ σ x       => (σ x.1, Species.transport σ x.2)
  id_transport   := fun {U} _ f             => by simp only [Equiv.refl_apply , id_transport  ]; rfl
  comp_transport := fun {U V W} _ _ _ σ τ f => by simp only [Equiv.trans_apply, comp_transport]; rfl

instance instComputableSpecies {F : Type → Type} [ComputableSpecies F]
: ComputableSpecies (Pointed F) where
  fintype := fun {U} _  => show Fintype (U × F U) from inferInstance
  decEq := by
    intros U _; unfold Pointed
    haveI _ := ComputableSpecies.decEq (F := F) (U := U)
    infer_instance

end Pointed
end Species
end
