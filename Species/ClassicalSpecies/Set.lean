import Species.Basic

instance SetSpecies: @Species Set where
  structures      := fun ls  => {↑ls}
  transport       := fun σ s => σ '' s
  transport_trans := by simp [Set.image_image]
  transport_id    := by simp
