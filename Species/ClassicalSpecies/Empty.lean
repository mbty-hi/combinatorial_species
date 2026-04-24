import Species.Basic

inductive SEmpty (U: Type) where

instance EmptySpecies: @Species SEmpty where
  structures := fun labels => {}
  transport := by intros; contradiction
  transport_trans := by intros; contradiction
  transport_id := by intros; contradiction
