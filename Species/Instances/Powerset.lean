import Species.Basic
import Mathlib.Data.Fintype.Powerset -- for the Fintype instance

abbrev SPowerset : Type → Type := Finset

instance SPowersetSpecies : Species SPowerset where
  fintype         := inferInstance
  transport       := fun σ s => s.map σ.toEmbedding
  transport_trans := by intro _ _ _ σ τ f; simp [Finset.map_map]
  transport_id    := by intro _ f; simp
