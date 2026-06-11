import Species.Basic
import Mathlib.Data.Fintype.Perm

abbrev SX (U: Type) := Fin 1 ≃ U

/- Display related instances -/
instance instReprSX        {U} [Repr U] : Repr (SX U) where reprPrec x _ := reprPrec (x 0) 0
instance instLinearOrderSX {U} : LinearOrder (SX U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSX : Species SX where
  fintype         := inferInstance
  transport       := fun σ e => e.trans σ
  transport_trans := by intro _ _ _ σ τ e; simp [Equiv.trans_assoc]
  transport_id    := by intro _ e; simp
