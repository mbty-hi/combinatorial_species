module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.WellKnown

@[expose] public section

/-- `Σ xⁿ = (1 − x)⁻¹`. -/
lemma mk_one_eq_inv : (PowerSeries.mk fun _ => (1 : ℚ)) = (1 - PowerSeries.X)⁻¹ := by
  rw [
    PowerSeries.eq_inv_iff_mul_eq_one (
      by simp only [
        map_sub, PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X, sub_zero, ne_eq,
        one_ne_zero, not_false_eq_true
      ]
    )
  ]
  have h := PowerSeries.invUnitsSub_mul_sub (1 : ℚˣ)
  convert h using 2 <;> ext n
  · simp only [PowerSeries.coeff_mk, PowerSeries.coeff_invUnitsSub, one_pow, divp_one]
  · simp only [map_sub, PowerSeries.coeff_one, Units.val_one, map_one]

end
