import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Species.Computable
import Species.Basic

namespace Species

/-- `(fₙ)~` : number of isomorphism types of `F`-structures on `[n]` -/
noncomputable def tgsCoeff (F : Type → Type) [Species F] (n : ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (F (Fin n)))

/-- `F~(x) = Σ ((fₙ)∼ * xⁿ)` -/
noncomputable def tgs (F : Type → Type) [Species F] : PowerSeries ℚ :=
  PowerSeries.mk fun n => (tgsCoeff F n)

end Species

namespace ComputableSpecies

/-- Computable `(fₙ)~`via Burnside -/
def tgsCoeff (F : Type → Type) [ComputableSpecies F] (n : ℕ) : ℕ :=
  (∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter fun f : F (Fin n) => σ • f = f).card) / n.factorial

/-- The computable `(fₙ)~` matches its noncomputable counterpart -/
lemma tgsCoeff_eq (F : Type → Type) [ComputableSpecies F] (n : ℕ)
: tgsCoeff F n = Species.tgsCoeff F n := by
  classical
  unfold tgsCoeff Species.tgsCoeff
  -- our filtered count is the size of `fixedBy`
  have hfix :
    ∀ σ : Equiv.Perm (Fin n),
    (Finset.univ.filter fun f : F (Fin n) => σ • f = f).card
    = Fintype.card (MulAction.fixedBy (F (Fin n)) σ)
  := by intro σ; rw [← Fintype.card_subtype]; exact Fintype.card_congr (Equiv.refl _)
  -- Burnside: Σ |Fix σ| = |orbits| * n!, then divide by n!
  rw [
    Finset.sum_congr rfl (fun σ _ => hfix σ),
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group,
    Fintype.card_perm, Fintype.card_fin, Nat.mul_div_cancel _ (Nat.factorial_pos n)
  ]
  exact Nat.card_eq_fintype_card.symm

end ComputableSpecies
