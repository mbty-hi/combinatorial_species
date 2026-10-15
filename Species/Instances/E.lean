module

public import Species.Basic
public import Species.Computable
public import Mathlib.Data.Finset.Sort
public import Mathlib.SetTheory.Cardinal.Finite
public import Init.Data.Format.Basic

@[expose] public section

namespace Species

/- Note that we do not store labels explicitly. Assuming that the type this is applied to is a
   `LabelType` (which it should be), we can easily recover them anyway. -/
structure E (U : Type) : Type -- empty, one inhabitant: ⟨⟩

namespace E

instance instSubSingleton {U} : Subsingleton (E U) := ⟨fun _ _ => rfl⟩
instance instDecidableEq  {U} : DecidableEq  (E U) := fun _ _ => isTrue rfl
instance instFintype      {U} : Fintype      (E U) := Fintype.ofSubsingleton ⟨⟩

/- Display related instances -/
instance instRepr {U} [Repr U] [LabelType U] : Repr (E U) where
  reprPrec _ _ :=
    "{" ++ Std.Format.joinSep ((Finset.univ : Finset U).sort (· ≤ ·) |>.map repr) ", " ++ "}"
instance instLinearOrder {U} : LinearOrder (E U) := .ofSubsingleton

/- Species instance -/
instance instSpecies : Species E where
  finite         := inferInstance
  transport      := fun _ _   => ⟨⟩
  id_transport   := fun _     => Subsingleton.elim _ _
  comp_transport := fun _ _ _ => rfl

instance instComputableSpecies : ComputableSpecies E where
  fintype := inferInstance
  decEq   := inferInstance

end E
end Species
end
