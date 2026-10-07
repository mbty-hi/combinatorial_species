import Species.Operations.Add
import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries

namespace Species

section EGS

lemma egsCoeff_add (F G : Type → Type) [Species F] [Species G] (n : ℕ)
: egsCoeff (Add F G) n = egsCoeff F n + egsCoeff G n :=
  Nat.card_sum

theorem egs_add (F G : Type → Type) [Species F] [Species G] : egs (Add F G) = egs F + egs G := by
  ext n; simp [egs, egsCoeff_add, add_div]

end EGS

end Species
