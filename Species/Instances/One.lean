import Species.Basic

def SOne (U : Type) : Type := U → Empty

instance instFintypeSOne {U} [Fintype U] [DecidableEq U] : Fintype (SOne U) :=
  inferInstanceAs (Fintype (U → Empty))
instance instSubsingletonSOne {U} : Subsingleton (SOne U) :=
  inferInstanceAs (Subsingleton (U → Empty))

/- Display related instances -/
instance instReprSOne        {U} [Repr U] : Repr (SOne U) where reprPrec _ _ := "•"
instance instLinearOrderSOne {U} : LinearOrder (SOne U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSOne : Species SOne where
  finite         := inferInstance
  transport      := fun σ f v => f (σ.symm v)
  id_transport   := fun _     => Subsingleton.elim _ _
  comp_transport := fun _ _ _ => Subsingleton.elim _ _

instance instSpeciesCompSOne : SpeciesComp SOne where
  fintype := inferInstance
  decEq   := inferInstance
