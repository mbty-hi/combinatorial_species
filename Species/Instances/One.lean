module

public import Species.Basic
public import Species.Computable

@[expose] public section

namespace Species

def One (U : Type) : Type := U → Empty

namespace One

instance instFintype {U} [Fintype U] [DecidableEq U] : Fintype (One U) :=
  inferInstanceAs (Fintype (U → Empty))
instance instSubsingleton {U} : Subsingleton (One U) :=
  inferInstanceAs (Subsingleton (U → Empty))

/- Display related instances -/
instance instRepr        {U} [Repr U] : Repr (One U) where reprPrec _ _ := "•"
instance instLinearOrder {U} : LinearOrder (One U) := .ofSubsingleton

/- Species instance -/
instance instSpecies : Species One where
  finite         := inferInstance
  transport      := fun σ f v => f (σ.symm v)
  id_transport   := fun _     => Subsingleton.elim _ _
  comp_transport := fun _ _ _ => Subsingleton.elim _ _

instance instComputableSpecies : ComputableSpecies One where
  fintype := inferInstance
  decEq   := inferInstance

end One
end Species
end
