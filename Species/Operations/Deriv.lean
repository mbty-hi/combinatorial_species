import Species.Basic
import Mathlib.Order.WithBot
import Mathlib.Data.Fintype.WithTopBot

namespace Species

variable {F : Type → Type} [Species F]

/- We don't use `Option` directly as we need a `LinearOrder` instance.
   This used to be defined as `abbrev WithHole (U : Type) := WithBot U`, but it lead to atrocious
   issues with reduction after update (`Option` and `WithBot` kept conflicting). `WithBot` really
   should work out of the box and I don't understand why it is defined in such a way as to include
   funny side-effects.
   The `LinearOrder` instance is defined manually below. -/
structure WithHole (U : Type) where
  val : Option U
deriving DecidableEq
def Deriv (F : Type → Type) (U : Type) : Type := F (WithHole U)

namespace WithHole
variable {U V W : Type}

def equivOption : WithHole U ≃ Option U where
  toFun       := WithHole.val
  invFun      := WithHole.mk
  left_inv  _ := rfl
  right_inv _ := rfl

instance instBotWithHole : Bot (WithHole U) := ⟨⟨none⟩⟩
def coe (u : U) : WithHole U := ⟨some u⟩

instance instLinearOrderWithHole [LinearOrder U] : LinearOrder (WithHole U) :=
  LinearOrder.lift' (β := WithBot U)
    (fun x => (x.val : WithBot U))
    (fun ⟨val_a⟩ ⟨val_b⟩ h => by simp at *; assumption)

instance instFiniteWithHole [Finite U] : Finite (WithHole U) :=
  Finite.of_injective WithHole.val (fun ⟨val_a⟩ ⟨val_b⟩ h => by simp at *; assumption)

instance instFintypeWithHole [Fintype U] : Fintype (WithHole U) :=
  Fintype.ofEquiv (Option U) equivOption.symm

def transport (σ : U ≃ V) : WithHole U ≃ WithHole V where
  toFun  x  := ⟨x.val.map σ⟩
  invFun x  := ⟨x.val.map σ.symm⟩
  left_inv  := by rintro ⟨_ | u⟩ <;> simp
  right_inv := by rintro ⟨_ | u⟩ <;> simp

@[simp] theorem transport_refl : transport (Equiv.refl U) = Equiv.refl (WithHole U) :=
  Equiv.ext fun x => by cases x with | mk val => cases val <;> rfl

@[simp] theorem transport_trans (σ : U ≃ V) (τ : V ≃ W)
: transport (σ.trans τ) = (transport σ).trans (transport τ) :=
  Equiv.ext fun x => by cases x with | mk val => cases val <;> rfl

end WithHole

/- Display related instances -/
instance instReprWithHole {U : Type} [Repr U] : Repr (WithHole U) where
  reprPrec x _ :=
    match x.val with
    | none   => "⋆"
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
    have := Species.finite (F := F) (U := WithHole U)
    infer_instance
  transport      := fun {U V} _ _ σ         => Species.transport (F := F) (WithHole.transport σ)
  id_transport   := fun {U} _ f             => by unfold Deriv at *; simp [Species.id_transport]
  comp_transport := fun {U V W} _ _ _ σ τ f => by unfold Deriv at *; simp [Species.comp_transport]

instance instSpeciesCompDeriv {F : Type → Type} [SpeciesComp F] : SpeciesComp (Deriv F) where
  fintype := fun {U} [LabelType U] => show Fintype (F (WithHole U)) from inferInstance
  decEq   := by
    intros U _ _ _; unfold Deriv at *
    haveI := SpeciesComp.decEq (F := F) (U := WithHole U)
    infer_instance

end Species
