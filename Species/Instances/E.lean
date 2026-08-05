import Species.Basic
import Mathlib.Data.Finset.Sort
import Init.Data.Format.Basic

/- Note that we do not store labels explicitly. Assuming that the type this is applied to is a
   `LabelType` (which it should be), we can easily recover them anyway. -/
structure SE (U : Type) : Type -- empty, one inhabitant: ⟨⟩

instance {U} : Subsingleton (SE U) := ⟨fun _ _ => rfl⟩
instance {U} : DecidableEq  (SE U) := fun _ _ => isTrue rfl
instance {U} : Fintype      (SE U) := Fintype.ofSubsingleton ⟨⟩

/- Display related instances -/
instance instReprSE {U} [Repr U] [LabelType U] : Repr (SE U) where
  reprPrec _ _ :=
    "{" ++ Std.Format.joinSep ((Finset.univ : Finset U).sort (· ≤ ·) |>.map repr) ", " ++ "}"
instance instLinearOrderSE {U} : LinearOrder (SE U) := .ofSubsingleton

/- Species instance -/
instance instSpeciesSE : Species SE where
  finite          := inferInstance
  transport       := fun _ _   => ⟨⟩
  transport_trans := fun _ _ _ => rfl
  transport_id    := fun _     => Subsingleton.elim _ _

instance instSpeciesCompSE : SpeciesComp SE where
  fintype := inferInstance
  decEq   := inferInstance
