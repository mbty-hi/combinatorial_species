import Species.Instances.One
import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries

namespace Species

section EGS

lemma card_One (n : ℕ) : Nat.card (One (Fin n)) = if n = 0 then 1 else 0 := by
  simp only [One]; cases n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_unique, ↓reduceIte]
  · simp only [
      Nat.card_eq_fintype_card, Fintype.card_eq_zero,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte
    ]

theorem egs_One : egs One = 1 := by
  ext n
  simp only [egs, egsCoeff, Nat.card_eq_fintype_card, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rw [Fintype.card_eq_nat_card, card_One]
  split_ifs <;> simp; lia

end EGS

section TGS

lemma tgsCoeff_One (n : ℕ) : tgsCoeff One n = if n = 0 then 1 else 0 := by
  simp only [tgsCoeff, One]; cases n
  · simp only [Nat.card_eq_fintype_card, Fintype.card_unique, ↓reduceIte]
  · simp only [Nat.card_of_isEmpty, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]

theorem tgs_One : tgs One = 1 := by
  ext n; simp only [tgs, tgsCoeff_One]
  simp only [
    Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, PowerSeries.coeff_mk, PowerSeries.coeff_one
  ]

end TGS

end Species
