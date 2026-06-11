import Species.Basic

inductive SZero (U: Type) where
open SZero

/- Display related instances -/
instance instReprSZero         {U} [Repr U] : Repr (SZero U) where reprPrec z _ := nomatch z
instance instSubsingletonSZero {U} : Subsingleton (SZero U) := ⟨fun a => nomatch a⟩
instance instLinearOrderSZero  {U} : LinearOrder (SZero U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSZero : Species SZero where
  fintype         := ⟨∅, fun x => nomatch x⟩
  transport       := fun _   empty => nomatch empty
  transport_trans := fun _ _ empty => nomatch empty
  transport_id    := fun     empty => nomatch empty
