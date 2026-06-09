import Species.Basic

inductive SZero (U: Type) where
open SZero

instance SZeroSpecies : Species SZero where
  fintype         := ⟨∅, fun x => nomatch x⟩
  transport       := fun _   empty => nomatch empty
  transport_trans := fun _ _ empty => nomatch empty
  transport_id    := fun     empty => nomatch empty
