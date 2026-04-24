import Species.Basic

inductive SEmptySet (U: Type) where | SEmptySetC
open SEmptySet

instance EmptySetSpecies: @Species SEmptySet where
  structures := fun ls => {SEmptySetC}
  transport := by intros; apply SEmptySetC
  transport_trans := by simp
  transport_id := by simp
