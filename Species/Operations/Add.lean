import Species.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum

namespace Species

variable {F G : Type → Type} [Species F] [Species G]

def add (F G : Type → Type) (U : Type) : Type := F U ⊕ G U

instance : Add (Type → Type) where
  add := Species.add

instance instSpeciesAdd : Species (F + G) where
  fintype := fun {U} [LabelType U] =>
    show Fintype (F U ⊕ G U) from inferInstance

  transport {U V} _ _ σ := Sum.map (transport σ) (transport σ)

  transport_trans := fun {U V W} _ _ _ σ τ f => by
    cases f <;> simp [Species.transport_trans]

  transport_id := fun {U} _ f => by
    cases f <;> simp [Species.transport_id]

end Species
