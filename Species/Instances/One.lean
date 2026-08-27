import Species.Basic

namespace Species

def One (U : Type) : Type := U → Empty

instance instFintypeOne {U} [Fintype U] [DecidableEq U] : Fintype (One U) :=
  inferInstanceAs (Fintype (U → Empty))
instance instSubsingletonOne {U} : Subsingleton (One U) :=
  inferInstanceAs (Subsingleton (U → Empty))

/- Display related instances -/
instance instReprOne        {U} [Repr U] : Repr (One U) where reprPrec _ _ := "•"
instance instLinearOrderOne {U} : LinearOrder (One U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesOne : Species One where
  finite         := inferInstance
  transport      := fun σ f v => f (σ.symm v)
  id_transport   := fun _     => Subsingleton.elim _ _
  comp_transport := fun _ _ _ => Subsingleton.elim _ _

instance instSpeciesCompOne : SpeciesComp One where
  fintype := inferInstance
  decEq   := inferInstance

end Species
