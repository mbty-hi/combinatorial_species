import Species.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Fintype.WithTopBot

namespace Species

variable {F : Type → Type} [Species F]

abbrev WithHole (U : Type) := WithBot U -- Defined this way to allow for custom Repr
def Deriv (F : Type → Type) (U : Type) : Type := F (WithHole U)

/- Display related instances -/
instance instReprWithHole {U : Type} [Repr U] : Repr (WithHole U) where
  reprPrec x _ :=
    match x with
    | none => "⋆"
    | some x => repr x
instance instReprDeriv {F : Type → Type} {U : Type} [Repr (F (WithHole U))] : Repr (Deriv F U) :=
  inferInstanceAs (Repr (F (WithHole U)))

instance instLinearOrderDeriv {F : Type → Type} {U : Type} [LinearOrder (F (WithHole U))]
: LinearOrder (Deriv F U) :=
  inferInstanceAs (LinearOrder (F (WithHole U)))

/- Species instance -/
instance instSpeciesDeriv : Species (Deriv F) where
  finite := by
    intros U _; unfold Deriv
    haveI := Species.finite (F := F) (U := WithHole U)
    infer_instance
  transport       := fun {U V} _ _ σ         => Species.transport (F := F) (Equiv.withBotCongr σ)
  transport_trans := fun {U V W} _ _ _ σ τ f => by simp [Species.transport_trans]
  transport_id    := fun {U} _ f             => by simp [Species.transport_id]

instance instSpeciesCompDeriv [SpeciesComp F] : SpeciesComp (Deriv F) where
  fintype := fun {U} [LabelType U] => show Fintype (F (WithBot U)) from inferInstance
  decEq   := by
    intros U _ _ _; unfold Deriv
    haveI := SpeciesComp.decEq (F := F) (U := WithHole U)
    infer_instance

end Species
