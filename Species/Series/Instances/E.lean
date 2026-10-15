module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Species.Series.ExponentialGeneratingSeries
public import Species.Series.TypeGeneratingSeries
public import Species.Series.Utils
public import Species.Instances.E

@[expose] public section

namespace Species

section EGS

lemma card_E (n : ℕ) : Nat.card (E (Fin n)) = 1 := Nat.card_of_subsingleton ⟨⟩

theorem egs_E : egs E = PowerSeries.exp ℚ := by
  ext n
  simp only [
    egs, egsCoeff, Nat.card_eq_fintype_card, PowerSeries.coeff_mk, PowerSeries.coeff_exp,
    Algebra.algebraMap_self, one_div, map_inv₀, map_natCast
  ]
  rw [Fintype.card_eq_nat_card, card_E]; simp only [Nat.cast_one, one_div]

end EGS

section TGS

lemma tgsCoeff_E (n : ℕ) : tgsCoeff E n = 1 := by exact Nat.card_of_subsingleton ⟦⟨⟩⟧

theorem tgs_E : tgs E = (1 - PowerSeries.X)⁻¹ := by
  simp only [tgs, tgsCoeff_E, Nat.cast_one, ← mk_one_eq_inv]

end TGS
end Species
end
