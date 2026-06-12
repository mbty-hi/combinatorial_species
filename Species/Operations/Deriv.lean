import Species.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Fintype.WithTopBot

namespace Species

variable {F : Type → Type} [Species F]

abbrev WithHole (α : Type) := WithBot α -- Defined this way to allow for custom Repr
def Deriv (F : Type → Type) (α : Type) : Type := F (WithHole α)

/- Display related instances -/
instance instReprWithHole {α : Type} [Repr α] : Repr (WithHole α) where
  reprPrec x _ :=
    match x with
    | none => "⋆"
    | some x => repr x
instance instReprDeriv {F : Type → Type} {α : Type} [Repr (F (WithHole α))] : Repr (Deriv F α) :=
  inferInstanceAs (Repr (F (WithHole α)))

instance instLinearOrderDeriv {F : Type → Type} {α : Type} [LinearOrder (F (WithHole α))]
: LinearOrder (Deriv F α) :=
  inferInstanceAs (LinearOrder (F (WithHole α)))

/- Species instance -/
instance instSpeciesDeriv : Species (Deriv F) where
  fintype         := fun {α} [LabelType α]   => show Fintype (F (WithBot α)) from inferInstance
  transport       := fun {α β} _ _ σ         => Species.transport (F := F) (Equiv.withBotCongr σ)
  transport_trans := fun {α β γ} _ _ _ σ τ f => by simp [Species.transport_trans]
  transport_id    := fun {α} _ f             => by simp [Species.transport_id]

end Species
