import Species.Basic
import Mathlib.Data.Fintype.Perm

namespace Species

def X (U : Type) := Fin 1 ≃ U

instance instFintypeX {U} [Fintype U] [DecidableEq U] : Fintype (X U) :=
  inferInstanceAs (Fintype (Fin 1 ≃ U))
instance instSubsingletonX {U} : Subsingleton (X U) :=
  inferInstanceAs (Subsingleton (Fin 1 ≃ U))

/- Display related instances -/
instance instReprX {U} [Repr U] : Repr (X U) where reprPrec x _ := reprPrec (x.1 0) 0
instance instLinearOrderX {U} : LinearOrder (X U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesX : Species X where
  finite         := inferInstance
  transport      := fun σ e => e.trans σ
  id_transport   := by intro _ _ e; rfl
  comp_transport := by intro _ _ _ _ _ _ σ τ e; unfold X at *; simp [Equiv.trans_assoc]

instance instSpeciesCompX : SpeciesComp X where
  fintype := inferInstance
  decEq   := inferInstance

end Species
