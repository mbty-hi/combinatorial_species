import Species.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/- fₙ : number of F-structures on an n-element label set := |F[n]| -/
def EGS_coeff (F : Type → Type) [Species F] (n : ℕ) : ℕ := Fintype.card (F (Fin n))

/- F(x) = Σ (fₙ * xⁿ/(n!)). Non computable! -/
noncomputable def EGS (F : Type → Type) [Species F] : PowerSeries ℚ :=
  PowerSeries.mk fun n => (EGS_coeff F n : ℚ) / n.factorial
