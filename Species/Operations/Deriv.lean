module

public import Species.Basic
public import Species.Computable
public import Mathlib.Order.WithBot
public import Mathlib.Data.Fintype.WithTopBot

@[expose] public section

namespace Species

/- We don't use `Option` directly as we need a `LinearOrder` instance.
   This used to be defined as `abbrev WithHole (U : Type) := WithBot U`, but it lead to atrocious
   issues with reduction after update (`Option` and `WithBot` kept conflicting). `WithBot` really
   should work out of the box and I don't understand why it is defined in such a way as to include
   funny side-effects.
   The `LinearOrder` instance is defined manually below. -/
structure WithHole (U : Type) where
  val : Option U
deriving DecidableEq

namespace WithHole
variable {U V W : Type}

def equivOption : WithHole U ≃ Option U where
  toFun       := WithHole.val
  invFun      := WithHole.mk
  left_inv  _ := rfl
  right_inv _ := rfl

instance instBot : Bot (WithHole U) := ⟨⟨none⟩⟩
def coe (u : U) : WithHole U := ⟨some u⟩

instance instLinearOrder [LinearOrder U] : LinearOrder (WithHole U) :=
  LinearOrder.lift' (β := WithBot U)
    (fun x => (x.val : WithBot U))
    (fun ⟨val_a⟩ ⟨val_b⟩ h => by simp only [mk.injEq] at *; assumption)

instance instFinite [Finite U] : Finite (WithHole U) :=
  Finite.of_injective
    WithHole.val (fun ⟨val_a⟩ ⟨val_b⟩ h => by simp only [mk.injEq] at *; assumption)

instance instFintype [Fintype U] : Fintype (WithHole U) :=
  Fintype.ofEquiv (Option U) equivOption.symm

def transport (σ : U ≃ V) : WithHole U ≃ WithHole V where
  toFun  x := ⟨x.val.map σ⟩
  invFun x := ⟨x.val.map σ.symm⟩
  left_inv := by
    rintro ⟨_ | u⟩ <;> simp only [Option.map_none, Option.map_some, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨_ | u⟩ <;> simp only [Option.map_none, Option.map_some, Equiv.apply_symm_apply]

@[simp] theorem transport_refl : transport (Equiv.refl U) = Equiv.refl (WithHole U) :=
  Equiv.ext fun x => by cases x with | mk val => cases val <;> rfl

@[simp] theorem transport_trans (σ : U ≃ V) (τ : V ≃ W)
: transport (σ.trans τ) = (transport σ).trans (transport τ) :=
  Equiv.ext fun x => by cases x with | mk val => cases val <;> rfl

lemma coe_val_eq {x : WithHole U} {u : U} (h : x.val = some u) : WithHole.coe u = x := by
  cases x with
  | mk ou => cases h; rfl

lemma coe_injective : Function.Injective (WithHole.coe (U := U)) := by
  intro a b h; cases h; rfl

instance instRepr {U : Type} [Repr U] : Repr (WithHole U) where
  reprPrec x _ :=
    match x.val with
    | none   => "⋆"
    | some x => repr x

end WithHole

def Deriv (F : Type → Type) (U : Type) : Type := F (WithHole U)

namespace Deriv

variable {F : Type → Type} [Species F] {U V : Type} [Finite U] [Finite V]

section Display

instance instRepr [Repr (F (WithHole U))] : Repr (Deriv F U) :=
  inferInstanceAs (Repr (F (WithHole U)))

instance instLinearOrder [LinearOrder (F (WithHole U))] : LinearOrder (Deriv F U) :=
  inferInstanceAs (LinearOrder (F (WithHole U)))

end Display

instance instSpecies : Species (Deriv F) where
  finite       := fun {U} _       => by unfold Deriv; infer_instance
  transport    := fun {U V} _ _ σ => Species.transport (F := F) (WithHole.transport σ)
  id_transport := fun {U} _ f     => by
    unfold Deriv at *; simp only [WithHole.transport_refl, id_transport]
  comp_transport := fun {U V W} _ _ _ σ τ f => by
    unfold Deriv at *; simp only [WithHole.transport_trans, comp_transport]

instance instComputableSpecies {F : Type → Type} [ComputableSpecies F]
: ComputableSpecies (Deriv F) where
  fintype := fun {U} [LabelType U] => show Fintype (F (WithHole U)) from inferInstance
  decEq   := fun {U} _ _ _         => by unfold Deriv at *; infer_instance

@[simp] lemma transport_eq (σ : U ≃ V) (x : Deriv F U) :
  transport σ x = transport (WithHole.transport σ) x
:= rfl

end Deriv
end Species
end
