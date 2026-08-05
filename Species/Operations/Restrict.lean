import Species.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Fintype.Sigma

def Restrict (F : Type → Type) (k : ℕ) (U : Type) : Type :=
  { _x : F U // Nat.card U = k }

/- Display related instances -/
instance instReprRestrict {F} {k : ℕ} {U} [Repr (F U)] : Repr (Restrict F k U) where
  reprPrec x prec := reprPrec x.1 prec

instance instLinearOrderRestrict {F} {k : ℕ} {U} [LinearOrder (F U)]
: LinearOrder (Restrict F k U) :=
  LinearOrder.lift' Subtype.val Subtype.val_injective

/- Species instance -/
instance RestrictSpecies (F : Type → Type) [Species F] (k : ℕ) : Species (Restrict F k) where
  finite          := by
    intros U _; unfold Restrict
    haveI : Finite (F U) := Species.finite
    infer_instance
  transport       := fun σ x => ⟨Species.transport σ x.1, by rw [← Nat.card_congr σ]; exact x.2⟩
  transport_trans := fun σ τ x => Subtype.ext (Species.transport_trans σ τ x.1)
  transport_id    := fun x     => Subtype.ext (Species.transport_id x.1)

instance instFintypeRestrict {F} [SpeciesComp F] (k : ℕ) {U} [LabelType U]
: Fintype (Restrict F k U) :=
  Fintype.ofEquiv
    {x : F U // Fintype.card U = k}
    (Equiv.subtypeEquivRight fun _ => by rw [Nat.card_eq_fintype_card])

instance RestrictCompSpecies (F : Type → Type) [SpeciesComp F] (k : ℕ) : SpeciesComp (Restrict F k) where
  fintype := inferInstance
  decEq   := by
    intros U _ _ _; unfold Restrict
    haveI := SpeciesComp.decEq (F := F) (U := U)
    infer_instance
