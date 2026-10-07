import Species.Instances.Zero
import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries

namespace Species

section EGS

theorem egs_Zero : egs Zero = 0 := by ext n; simp [egs, egsCoeff]

end EGS

section TGS

lemma tgsCoeff_Zero (n : ℕ) : tgsCoeff Zero n = 0 := by
  unfold tgsCoeff
  have _ : IsEmpty (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (Zero (Fin n))) :=
    inferInstanceAs (IsEmpty (Quotient _))
  exact Nat.card_of_isEmpty

theorem tgs_Zero : tgs Zero = 0 := by ext n; simp [tgs, PowerSeries.coeff_mk, tgsCoeff_Zero]

end TGS

end Species
