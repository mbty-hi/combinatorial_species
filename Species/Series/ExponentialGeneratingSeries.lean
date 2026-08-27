import Species.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace Species

/- TODO smthg with Finite.card as well -/

/- fₙ : number of F-structures on an n-element label set := |F[n]| -/
def EGS_coeff (F : Type → Type) [SpeciesComp F] (n : ℕ) : ℕ := Fintype.card (F (Fin n))

/- F(x) = Σ (fₙ * xⁿ/(n!)). Non computable! -/
noncomputable def EGS (F : Type → Type) [SpeciesComp F] : PowerSeries ℚ :=
  PowerSeries.mk fun n => (EGS_coeff F n : ℚ) / n.factorial

end Species
