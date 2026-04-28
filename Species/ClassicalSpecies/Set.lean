import Species.Basic

instance SetSpecies: @Species Set where
  structures      := fun ls => {↑ls}
  transport       := by intro _ _ σ _ fu; apply (Set.image σ fu)
  transport_trans := by simp [Set.image_image]
  transport_id    := by simp
