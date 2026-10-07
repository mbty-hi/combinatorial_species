import Species.Instances.One
import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries

namespace Species

section EGS

lemma card_One (n : ℕ) : Nat.card (One (Fin n)) = if n = 0 then 1 else 0 := by
  simp [One]; cases n <;> simp

theorem egs_One : egs One = 1 := by
  ext n; simp [egs, egsCoeff]; rw [Fintype.card_eq_nat_card, card_One]
  split_ifs <;> simp; lia

end EGS

section TGS

lemma tgsCoeff_One (n : ℕ) : tgsCoeff One n = if n = 0 then 1 else 0 := by
  simp [tgsCoeff, One]; cases n <;> simp

theorem tgs_One : tgs One = 1 := by ext n; simp only [tgs, tgsCoeff_One]; simp

end TGS

end Species
