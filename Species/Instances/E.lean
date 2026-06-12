import Species.Basic
import Mathlib.Data.Finset.Sort
import Init.Data.Format.Basic

/- Note that we do not store labels explicitly. Assuming that the type this is applied to is a
   `LabelType` (which it should be), we can easily recover them anyway. -/
structure SE (α : Type) : Type -- empty, one inhabitant: ⟨⟩

instance {α} : Subsingleton (SE α) := ⟨fun _ _ => rfl⟩
instance {α} : DecidableEq (SE α)  := fun _ _ => isTrue rfl
instance {α} : Fintype (SE α)      := Fintype.ofSubsingleton ⟨⟩

/- Display related instances -/
instance instReprSE {α} [Repr α] [LabelType α] : Repr (SE α) where
  reprPrec _ _ :=
    "{" ++ Std.Format.joinSep ((Finset.univ : Finset α).sort (· ≤ ·) |>.map repr) ", " ++ "}"
instance instLinearOrderSE {α} : LinearOrder (SE α) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSE : Species SE where
  fintype         := inferInstance
  transport       := fun _ _   => ⟨⟩
  transport_trans := fun _ _ _ => rfl
  transport_id    := fun _     => Subsingleton.elim _ _
