import Species.Basic
import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries
import Species.Series.Utils
import Mathlib.Data.Finset.Sort
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.SetTheory.Cardinal.Finite
import Init.Data.Format.Basic

namespace Species

/- Note that we do not store labels explicitly. Assuming that the type this is applied to is a
   `LabelType` (which it should be), we can easily recover them anyway. -/
structure E (U : Type) : Type -- empty, one inhabitant: ⟨⟩

instance {U} : Subsingleton (E U) := ⟨fun _ _ => rfl⟩
instance {U} : DecidableEq  (E U) := fun _ _ => isTrue rfl
instance {U} : Fintype      (E U) := Fintype.ofSubsingleton ⟨⟩

/- Display related instances -/
instance instReprE {U} [Repr U] [LabelType U] : Repr (E U) where
  reprPrec _ _ :=
    "{" ++ Std.Format.joinSep ((Finset.univ : Finset U).sort (· ≤ ·) |>.map repr) ", " ++ "}"
instance instLinearOrderE {U} : LinearOrder (E U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesE : Species E where
  finite         := inferInstance
  transport      := fun _ _   => ⟨⟩
  id_transport   := fun _     => Subsingleton.elim _ _
  comp_transport := fun _ _ _ => rfl

instance instSpeciesCompE : SpeciesComp E where
  fintype := inferInstance
  decEq   := inferInstance

/- Series -/

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
