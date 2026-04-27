import Species.Basic

inductive SEmpty (U: Type) where

instance EmptySpecies: @Species SEmpty where
  structures      := fun _ => {}
  transport       := fun _ empty => nomatch empty
  transport_trans := fun _ _ _ _ _ _ _ empty => nomatch empty
  transport_id    := fun _ empty => nomatch empty
