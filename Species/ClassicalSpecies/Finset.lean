import Mathlib.Data.Finset.Basic
import Species.Basic

instance FinsetSpecies: @Species Finset where
  structures := fun ls => {ls}
  transport := by
    intro U V σ σ_bij fu
    have ⟨inj, surj⟩ := σ_bij
    have σ_emb : U ↪ V := by
      apply Function.Embedding.mk
      apply inj
    apply (Finset.map σ_emb fu)
  transport_trans := by
    intro U V W σ τ σ_bij τ_bij fu
    unfold Function.Bijective.comp
    have ⟨σ_inj, σ_surj⟩ := σ_bij
    have ⟨τ_inj, τ_surj⟩ := τ_bij
    simp; rw [Finset.map_map]; simp
  transport_id := by
    intro U fu
    unfold Function.bijective_id; simp
