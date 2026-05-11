import Species.Basic

structure SSingleton {U: Type} where
  value : U
open SSingleton

instance SingletonSpecies: @Species @SSingleton where
  structures      := fun labels => labels.map ⟨SSingleton.mk, fun a₁ a₂ h => by simp at h; exact h⟩
  transport       := fun σ s    => ⟨σ s.value⟩
  transport_trans := by simp
  transport_id    := by simp
