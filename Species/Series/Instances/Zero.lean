module

public import Species.Instances.Zero
public import Species.Series.ExponentialGeneratingSeries
public import Species.Series.TypeGeneratingSeries

@[expose] public section

namespace Species

section EGS

theorem egs_Zero : egs Zero = 0 := by
  ext n
  simp only [
    egs, egsCoeff, Nat.card_eq_fintype_card, Fintype.card_eq_zero, CharP.cast_eq_zero, zero_div,
    PowerSeries.coeff_mk, map_zero
  ]

end EGS

section TGS

lemma tgsCoeff_Zero (n : ℕ) : tgsCoeff Zero n = 0 := by
  unfold tgsCoeff; exact Nat.card_of_isEmpty

theorem tgs_Zero : tgs Zero = 0 := by
  ext n; simp only [tgs, tgsCoeff_Zero, CharP.cast_eq_zero, PowerSeries.coeff_mk, map_zero]

end TGS
end Species
end
