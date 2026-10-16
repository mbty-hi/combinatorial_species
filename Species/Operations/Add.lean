module

public import Species.Basic
public import Species.Computable
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Sum.Order

@[expose] public section

namespace Species

def Add (F G : Type → Type) (U : Type) : Type := F U ⊕ G U

namespace Add

variable {F G : Type → Type} [Species F] [Species G] {U V : Type} [Finite U] [Finite V]

section Display

instance instRepr [Repr (F U)] [Repr (G U)] : Repr ((Add F G) U) where
  reprPrec x _ :=
    match x with
    | .inl a => "L" ++ repr a
    | .inr b => "R" ++ repr b

instance instLinearOrder [LinearOrder (F U)] [LinearOrder (G U)] : LinearOrder ((Add F G) U) :=
  inferInstanceAs (LinearOrder (F U ⊕ₗ G U))

end Display

instance instSpecies : Species (Add F G) where
  finite        := by intros U _; unfold Add; infer_instance
  transport     := fun {U V} _ _ σ => Sum.map (transport σ) (transport σ)
  id_transport  := fun {U} _ f => by
    cases f <;> simp only [Sum.map_inl, Sum.map_inr, id_transport] <;> rfl
  comp_transport := fun {U V W} _ _ _ σ τ f => by
    cases f <;> simp only [Sum.map_inl, Sum.map_inr, comp_transport] <;> rfl

instance instComputableSpecies {F G : Type → Type} [ComputableSpecies F] [ComputableSpecies G]
: ComputableSpecies (Add F G) where
  fintype := fun {U} [LabelType U] => show Fintype (F U ⊕ G U) from inferInstance
  decEq   := by intros U _; unfold Add; infer_instance

@[simp] lemma transport_inl (σ : U ≃ V) (x : F U) :
  transport (F := Add F G) σ (.inl x) = .inl (transport σ x)
:= rfl

@[simp] lemma transport_inr (σ : U ≃ V) (x : G U) :
  transport (F := Add F G) σ (.inr x) = .inr (transport σ x)
:= rfl

end Add
end Species
end
