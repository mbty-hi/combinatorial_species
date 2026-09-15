import Species.Basic

namespace Species

inductive Zero (α : Type) where

/- Display related instances -/
instance instReprZero         {U} [Repr U] : Repr (Zero U) where reprPrec z _ := nomatch z
instance instSubsingletonZero {U} : Subsingleton (Zero U) := ⟨fun a => nomatch a⟩
instance instLinearOrderZero  {U} : LinearOrder (Zero U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesZero : Species Zero where
  finite         := inferInstance
  transport      := fun _   empty => nomatch empty
  id_transport   := fun     empty => nomatch empty
  comp_transport := fun _ _ empty => nomatch empty

instance instSpeciesCompZero : SpeciesComp Zero where
  fintype := ⟨∅, fun x => nomatch x⟩
  decEq   := inferInstance

end Species
