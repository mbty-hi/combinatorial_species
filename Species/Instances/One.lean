import Species.Basic

abbrev SOne (U : Type) : Type := U → Empty

instance SOneSpecies : Species SOne where
  fintype         := inferInstance
  transport       := fun σ f v => f (σ.symm v)
  transport_trans := fun _ _ _ => Subsingleton.elim _ _
  transport_id    := fun _     => Subsingleton.elim _ _
