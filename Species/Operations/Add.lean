import Species.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sum.Order

namespace Species

variable {F G : Type → Type} [Species F] [Species G]

def add (F G : Type → Type) (α : Type) : Type := F α ⊕ G α

/- Display related instances -/
instance instReprAdd {F G : Type → Type} {α : Type} [Repr (F α)] [Repr (G α)]
: Repr ((add F G) α) where
  reprPrec x _ := match x with
    | .inl a => "L" ++ repr a
    | .inr b => "R" ++ repr b
instance instLinearOrderAdd {F G : Type → Type} {α : Type} [LinearOrder (F α)] [LinearOrder (G α)]
: LinearOrder ((add F G) α) :=
  inferInstanceAs (LinearOrder (F α ⊕ₗ G α))

/- Species instance -/
instance instSpeciesAdd : Species (add F G) where
  fintype         := fun {α} [LabelType α]   => show Fintype (F α ⊕ G α) from inferInstance
  transport       := fun {α β} _ _ σ         => Sum.map (transport σ) (transport σ)
  transport_trans := fun {α β γ} _ _ _ σ τ f => by cases f <;> simp [Species.transport_trans]
  transport_id    := fun {α} _ f             => by cases f <;> simp [Species.transport_id]

end Species
