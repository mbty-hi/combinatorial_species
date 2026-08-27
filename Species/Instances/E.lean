import Species.Basic
import Mathlib.Data.Finset.Sort
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

end Species
