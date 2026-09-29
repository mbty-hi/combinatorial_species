import Species.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PowerSeries.Basic

namespace Species

/-- `fₙ` : number of F-structures on an n-element label set := `|F[n]|` -/
noncomputable def egsCoeff (F : Type → Type) [Species F] (n : ℕ) : ℕ := Nat.card (F (Fin n))

/-- `F(x) = Σ (fₙ * xⁿ/(n!))` -/
noncomputable def egs (F : Type → Type) [Species F] : PowerSeries ℚ :=
  PowerSeries.mk fun n => (egsCoeff F n : ℚ) / n.factorial

end Species

namespace SpeciesComp

/-- Computable `fₙ` -/
def egsCoeff (F : Type → Type) [SpeciesComp F] (n : ℕ) : ℕ := Fintype.card (F (Fin n))

/-- The computable `fₙ` matches its noncomputable counterpart -/
lemma egsCoeff_eq (F : Type → Type) [SpeciesComp F] (n : ℕ)
: egsCoeff F n = Species.egsCoeff F n :=
  Nat.card_eq_fintype_card.symm

end SpeciesComp
