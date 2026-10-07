import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown

/-- `Σ xⁿ = (1 − x)⁻¹` -/
lemma mk_one_eq_inv : (PowerSeries.mk fun _ => (1 : ℚ)) = (1 - PowerSeries.X)⁻¹ := by
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  have h := PowerSeries.invUnitsSub_mul_sub (1 : ℚˣ)
  convert h using 2 <;> ext n <;> simp [PowerSeries.coeff_invUnitsSub]
