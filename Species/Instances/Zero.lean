import Species.Basic

namespace Species

inductive SZero (α : Type) where
open SZero

/- Display related instances -/
instance instReprSZero         {U} [Repr U] : Repr (SZero U) where reprPrec z _ := nomatch z
instance instSubsingletonSZero {U} : Subsingleton (SZero U) := ⟨fun a => nomatch a⟩
instance instLinearOrderSZero  {U} : LinearOrder (SZero U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSZero : Species SZero where
  finite         := inferInstance
  transport      := fun _   empty => nomatch empty
  id_transport   := fun     empty => nomatch empty
  comp_transport := fun _ _ empty => nomatch empty

instance instSpeciesCompSZero : SpeciesComp SZero where
  fintype := ⟨∅, fun x => nomatch x⟩
  decEq   := inferInstance

end Species
