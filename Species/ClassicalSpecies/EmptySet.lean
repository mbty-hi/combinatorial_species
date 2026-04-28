import Species.Basic

inductive SEmptySet (U: Type) where | SEmptySetC
open SEmptySet

instance EmptySetSpecies: @Species SEmptySet where
  structures      := fun _   => {SEmptySetC}
  transport       := fun _ _ => SEmptySetC
  transport_trans := by simp
  transport_id    := by simp
