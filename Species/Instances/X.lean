import Species.Basic
import Mathlib.Data.Fintype.Perm

abbrev SX (U : Type) := Fin 1 ≃ U

instance SXSpecies : Species SX where
  fintype         := inferInstance
  transport       := fun σ e => e.trans σ
  transport_trans := by intro _ _ _ σ τ e; simp [Equiv.trans_assoc]
  transport_id    := by intro _ e; simp
