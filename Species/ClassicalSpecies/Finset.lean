import Mathlib.Data.Finset.Basic
import Species.Basic

instance FinsetSpecies: @Species Finset where
  structures := fun ls => {ls}
  transport  := by
    intro U V σ s
    have σ_emb : U ↪ V := σ
    apply (Finset.map σ_emb s)
  transport_trans := by intro U V W σ τ su; simp [Finset.map_map]
  transport_id    := by intro U su; simp
