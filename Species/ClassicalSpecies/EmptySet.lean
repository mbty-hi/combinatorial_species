import Species.Basic

inductive SEmptySet (U: Type) where | SEmptySetC
open SEmptySet

instance EmptySetSpecies: @Species SEmptySet where
  structures      := fun _   => {SEmptySetC}
  transport       := fun _ _ => SEmptySetC
  transport_trans := fun _ _ _ => rfl
  transport_id    := fun _ => rfl
