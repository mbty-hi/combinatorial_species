import Species.Basic

instance SetSpecies: @Species Set where
  structures := fun ls => {↑ls}
  transport := by
    intro U V σ σ_bij fu
    apply (Set.image σ fu)
  transport_trans := by
    intro U V W σ τ σ_bij τ_bij f
    simp; rw [Set.image_image]
  transport_id := by simp
