import Species.Basic
import Mathlib.SetTheory.Cardinal.Finite

def Restrict (F : Type → Type) (k : ℕ) (α : Type) : Type :=
  { _x : F α // Nat.card α = k }

instance instFintypeRestrict {F} [Species F] (k : ℕ) {α} [LabelType α] : Fintype (Restrict F k α) :=
  Fintype.ofEquiv
    {x : F α // Fintype.card α = k}
    (Equiv.subtypeEquivRight fun _ => by rw [Nat.card_eq_fintype_card])

/- Display related instances -/
instance instReprRestrict {F} {k : ℕ} {α} [Repr (F α)] : Repr (Restrict F k α) where
  reprPrec x prec := reprPrec x.1 prec

instance instLinearOrderRestrict {F} {k : ℕ} {α} [LinearOrder (F α)]
: LinearOrder (Restrict F k α) :=
  LinearOrder.lift' Subtype.val Subtype.val_injective

/- Species instance -/
instance RestrictSpecies (F : Type → Type) [Species F] (k : ℕ) : Species (Restrict F k) where
  fintype         := inferInstance
  transport       := fun σ x => ⟨Species.transport σ x.1, by rw [← Nat.card_congr σ]; exact x.2⟩
  transport_trans := fun σ τ x => Subtype.ext (Species.transport_trans σ τ x.1)
  transport_id    := fun x     => Subtype.ext (Species.transport_id x.1)
