module

public import Species.Basic
public import Species.Computable
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace Species

def Restrict (F : Type → Type) (k : ℕ) (U : Type) : Type :=
  { _x : F U // Nat.card U = k }

namespace Restrict

section Display

instance instRepr {F} {k : ℕ} {U} [Repr (F U)] : Repr (Restrict F k U) where
  reprPrec x prec := reprPrec x.1 prec

instance instLinearOrder {F} {k : ℕ} {U} [LinearOrder (F U)]
: LinearOrder (Restrict F k U) :=
  LinearOrder.lift' Subtype.val Subtype.val_injective

end Display

instance instSpecies (F : Type → Type) [Species F] (k : ℕ) : Species (Restrict F k) where
  finite          := by
    intros U _; unfold Restrict
    have _ : Finite (F U) := Species.finite
    infer_instance
  transport      := fun σ x => ⟨Species.transport σ x.1, by rw [← Nat.card_congr σ]; exact x.2⟩
  id_transport   := fun x     => Subtype.ext (Species.id_transport x.1)
  comp_transport := fun σ τ x => Subtype.ext (Species.comp_transport σ τ x.1)

instance instFintype {F} [ComputableSpecies F] (k : ℕ) {U} [LabelType U]
: Fintype (Restrict F k U) :=
  Fintype.ofEquiv
    {x : F U // Fintype.card U = k}
    (Equiv.subtypeEquivRight fun _ => by rw [Nat.card_eq_fintype_card])

instance instCompSpecies (F : Type → Type) [ComputableSpecies F] (k : ℕ)
: ComputableSpecies (Restrict F k) where
  fintype := inferInstance
  decEq   := by
    intros U _; unfold Restrict
    haveI _ := ComputableSpecies.decEq (F := F) (U := U)
    infer_instance

end Restrict
end Species
end
