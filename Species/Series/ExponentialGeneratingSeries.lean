module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.RingTheory.PowerSeries.Basic
public import Species.Basic
public import Species.Computable

@[expose] public section

namespace Species

/-- `fₙ` : number of F-structures on an n-element label set := `|F[n]|` -/
noncomputable def egsCoeff (F : Type → Type) [Species F] (n : ℕ) : ℕ := Nat.card (F (Fin n))

/-- `F(x) = Σ (fₙ * xⁿ/(n!))` -/
noncomputable def egs (F : Type → Type) [Species F] : PowerSeries ℚ :=
  PowerSeries.mk fun n => (egsCoeff F n : ℚ) / n.factorial

end Species

namespace ComputableSpecies

/-- Computable `fₙ` -/
def egsCoeff (F : Type → Type) [ComputableSpecies F] (n : ℕ) : ℕ := Fintype.card (F (Fin n))

/-- The computable `fₙ` matches its noncomputable counterpart -/
lemma egsCoeff_eq (F : Type → Type) [ComputableSpecies F] (n : ℕ)
: egsCoeff F n = Species.egsCoeff F n :=
  Nat.card_eq_fintype_card.symm

end ComputableSpecies
end
