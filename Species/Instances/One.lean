import Species.Basic

abbrev SOne (U: Type) : Type := U → Empty

/- Display related instances -/
instance instReprSOne        {U} [Repr U] : Repr (SOne U) where reprPrec _ _ := "•"
instance instLinearOrderSOne {U} : LinearOrder (SOne U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSOne: Species SOne where
  fintype         := inferInstance
  transport       := fun σ f v => f (σ.symm v)
  transport_trans := fun _ _ _ => Subsingleton.elim _ _
  transport_id    := fun _     => Subsingleton.elim _ _
