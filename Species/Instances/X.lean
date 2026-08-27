import Species.Basic
import Mathlib.Data.Fintype.Perm

namespace Species

def SX (U : Type) := Fin 1 ≃ U

instance instFintypeSX {U} [Fintype U] [DecidableEq U] : Fintype (SX U) :=
  inferInstanceAs (Fintype (Fin 1 ≃ U))
instance instSubsingletonSX {U} : Subsingleton (SX U) :=
  inferInstanceAs (Subsingleton (Fin 1 ≃ U))

/- Display related instances -/
instance instReprSX {U} [Repr U] : Repr (SX U) where
  reprPrec x _ := reprPrec (x.1 0) 0
instance instLinearOrderSX {U} : LinearOrder (SX U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSX : Species SX where
  finite         := inferInstance
  transport      := fun σ e => e.trans σ
  id_transport   := by intro _ e; simp
  comp_transport := by intro _ _ _ σ τ e; simp [Equiv.trans_assoc]

instance instSpeciesCompSX : SpeciesComp SX where
  fintype := inferInstance
  decEq   := inferInstance

end Species
