import Species.Basic

def SOne (α : Type) : Type := α → Empty

instance instFintypeSOne {α} [Fintype α] [DecidableEq α] : Fintype (SOne α) :=
  inferInstanceAs (Fintype (α → Empty))
instance instSubsingletonSOne {α} : Subsingleton (SOne α) :=
  inferInstanceAs (Subsingleton (α → Empty))

/- Display related instances -/
instance instReprSOne        {α} [Repr α] : Repr (SOne α) where reprPrec _ _ := "•"
instance instLinearOrderSOne {α} : LinearOrder (SOne α) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSOne : Species SOne where
  fintype         := inferInstance
  transport       := fun σ f v => f (σ.symm v)
  transport_trans := fun _ _ _ => Subsingleton.elim _ _
  transport_id    := fun _     => Subsingleton.elim _ _
