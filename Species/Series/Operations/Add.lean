import Species.Operations.Add
import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries

namespace Species

section EGS

lemma egsCoeff_add (F G : Type → Type) [Species F] [Species G] (n : ℕ)
: egsCoeff (Add F G) n = egsCoeff F n + egsCoeff G n :=
  Nat.card_sum

theorem egs_add (F G : Type → Type) [Species F] [Species G] : egs (Add F G) = egs F + egs G := by
  ext n; simp only [egs, egsCoeff_add, Nat.cast_add, add_div, PowerSeries.coeff_mk, map_add]

end EGS

end Species
