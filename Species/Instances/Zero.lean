import Species.Basic

inductive SZero (α : Type) where
open SZero

/- Display related instances -/
instance instReprSZero         {α} [Repr α] : Repr (SZero α) where reprPrec z _ := nomatch z
instance instSubsingletonSZero {α} : Subsingleton (SZero α) := ⟨fun a => nomatch a⟩
instance instLinearOrderSZero  {α} : LinearOrder (SZero α) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSZero : Species SZero where
  fintype         := ⟨∅, fun x => nomatch x⟩
  transport       := fun _   empty => nomatch empty
  transport_trans := fun _ _ empty => nomatch empty
  transport_id    := fun     empty => nomatch empty
