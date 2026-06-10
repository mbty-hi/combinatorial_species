import Species.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Fintype.WithTopBot

namespace Species

variable {F: Type → Type} [Species F]

def Deriv (F : Type → Type) (U : Type) : Type := F (WithBot U)

instance instSpeciesDeriv : Species (Deriv F) where
  fintype := fun {U} [LabelType U] =>
    show Fintype (F (WithBot U)) from inferInstance

  transport {U V} _ _ σ := Species.transport (F := F) (Equiv.withBotCongr σ)

  transport_trans := fun {U V W} _ _ _ σ τ f => by
    simp [Species.transport_trans]

  transport_id := fun {U} _ f => by
    simp [Species.transport_id]


end Species
