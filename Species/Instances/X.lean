import Species.Basic
import Mathlib.Data.Fintype.Perm

def SX (α : Type) := Fin 1 ≃ α

instance instFintypeSX {α} [Fintype α] [DecidableEq α] : Fintype (SX α) :=
  inferInstanceAs (Fintype (Fin 1 ≃ α))
instance instSubsingletonSX {α} : Subsingleton (SX α) :=
  inferInstanceAs (Subsingleton (Fin 1 ≃ α))

/- Display related instances -/
instance instReprSX {α} [Repr α] : Repr (SX α) where
  reprPrec x _ := reprPrec (x.1 0) 0
instance instLinearOrderSX {α} : LinearOrder (SX α) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSX : Species SX where
  fintype         := inferInstance
  transport       := fun σ e => e.trans σ
  transport_trans := by intro _ _ _ σ τ e; simp [Equiv.trans_assoc]
  transport_id    := by intro _ e; simp
