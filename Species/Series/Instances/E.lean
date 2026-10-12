import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries
import Species.Series.Utils
import Species.Instances.E

namespace Species

section EGS

lemma card_E (n : ℕ) : Nat.card (E (Fin n)) = 1 := Nat.card_of_subsingleton ⟨⟩

theorem egs_E : egs E = PowerSeries.exp ℚ := by
  ext n; simp [egs, egsCoeff]; rw [Fintype.card_eq_nat_card, card_E]; simp

end EGS

section TGS

lemma tgsCoeff_E (n : ℕ) : tgsCoeff E n = 1 := by exact Nat.card_of_subsingleton ⟦⟨⟩⟧

theorem tgs_E : tgs E = (1 - PowerSeries.X)⁻¹ := by simp [← mk_one_eq_inv, tgs, tgsCoeff_E]

end TGS

end Species
