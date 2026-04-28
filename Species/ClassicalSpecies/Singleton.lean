import Species.Basic

structure SSingleton {U: Type} where
  value : U
open SSingleton

instance SingletonSpecies: @Species @SSingleton where
  structures      := fun labels => labels.map ⟨SSingleton.mk, fun a₁ a₂ h => by simp at h; exact h⟩
  transport       := by intros _ _ σ _ ssing_u; exact ⟨σ ssing_u.value⟩
  transport_trans := by simp
  transport_id    := by simp
