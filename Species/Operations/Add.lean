import Species.Basic
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sum.Order

namespace Species

variable {F G : Type → Type} [Species F] [Species G]

def Add (F G : Type → Type) (U : Type) : Type := F U ⊕ G U

/- Display related instances -/
instance instReprAdd {F G : Type → Type} {U : Type} [Repr (F U)] [Repr (G U)]
: Repr ((Add F G) U) where
  reprPrec x _ := match x with
    | .inl a => "L" ++ repr a
    | .inr b => "R" ++ repr b
instance instLinearOrderAdd {F G : Type → Type} {U : Type} [LinearOrder (F U)] [LinearOrder (G U)]
: LinearOrder ((Add F G) U) :=
  inferInstanceAs (LinearOrder (F U ⊕ₗ G U))

/- Species instance -/
instance instSpeciesAdd : Species (Add F G) where
  finite := by
    intros U _; unfold Add
    /- Surface some instances -/
    haveI := Species.finite (F := F) (U := U)
    haveI := Species.finite (F := G) (U := U)
    infer_instance
  transport      := fun {U V} _ _ σ         => Sum.map (transport σ) (transport σ)
  id_transport   := fun {U} _ f             => by cases f <;> simp [Species.id_transport]
  comp_transport := fun {U V W} _ _ _ σ τ f => by cases f <;> simp [Species.comp_transport]

instance instSpeciesCompAdd [SpeciesComp F] [SpeciesComp G] : SpeciesComp (Add F G) where
  fintype := fun {U} [LabelType U] => show Fintype (F U ⊕ G U) from inferInstance
  decEq   := by
    intros U _ _ _; unfold Add
    /- Surface some instances -/
    haveI := SpeciesComp.decEq (F := F) (U := U)
    haveI := SpeciesComp.decEq (F := G) (U := U)
    infer_instance

end Species
