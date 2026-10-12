import Species.Basic
import Species.Computable

namespace Species

inductive Zero (U : Type) where

namespace Zero

/- Display related instances -/
instance instIsEmpty     {U} : IsEmpty (Zero U) := ⟨fun x => nomatch x⟩
instance instRepr        {U} [Repr U] : Repr (Zero U) where reprPrec z _ := nomatch z
instance instLinearOrder {U} : LinearOrder (Zero U) := .ofSubsingleton

/- Species instance -/
instance instSpecies : Species Zero where
  finite         := inferInstance
  transport      := fun _   empty => nomatch empty
  id_transport   := fun     empty => nomatch empty
  comp_transport := fun _ _ empty => nomatch empty

instance instComputableSpecies : ComputableSpecies Zero where
  fintype := ⟨∅, fun x => nomatch x⟩
  decEq   := inferInstance

end Zero

end Species
