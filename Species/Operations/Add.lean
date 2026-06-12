import Species.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sum.Order

namespace Species

variable {F G: Type → Type} [Species F] [Species G]

def add (F G: Type → Type) (U: Type) : Type := F U ⊕ G U

/- Display related instances -/
instance instReprAdd {F G : Type → Type} {U : Type} [Repr (F U)] [Repr (G U)]
: Repr ((add F G) U) where
  reprPrec x _ := match x with
    | .inl a => "L" ++ repr a
    | .inr b => "R" ++ repr b
instance instLinearOrderAdd {F G: Type → Type} {U: Type} [LinearOrder (F U)] [LinearOrder (G U)]
: LinearOrder ((add F G) U) :=
  inferInstanceAs (LinearOrder (F U ⊕ₗ G U))

/- Species instance -/
instance instSpeciesAdd : Species (add F G) where
  fintype               := fun {U} [LabelType U] => show Fintype (F U ⊕ G U) from inferInstance
  transport {U V} _ _ σ := Sum.map (transport σ) (transport σ)
  transport_trans       := fun {U V W} _ _ _ σ τ f => by cases f <;> simp [Species.transport_trans]
  transport_id          := fun {U} _ f => by cases f <;> simp [Species.transport_id]

end Species
