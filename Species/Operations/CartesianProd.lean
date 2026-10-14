import Species.Basic
import Species.Computable
import Mathlib.Data.Prod.Lex

namespace Species

def CartProd (F G : Type → Type) (U : Type) : Type := F U × G U

namespace CartProd

variable {F G : Type → Type} [Species F] [Species G] {U : Type}

--notation:65 F " × " G => Species.CartProd F G

/- Display related instances -/
instance instRepr {F G : Type → Type} {U : Type} [Repr (F U)] [Repr (G U)]
: Repr ((CartProd F G) U) :=
  inferInstanceAs (Repr (F U × G U))

instance instLinearOrder
  {F G : Type → Type} {U : Type} [LinearOrder (F U)] [LinearOrder (G U)]
: LinearOrder ((CartProd F G) U) :=
  inferInstanceAs (LinearOrder (F U ×ₗ G U))

/- Species instance -/
instance instSpecies : Species (CartProd F G) where
  finite := by
    intros U _; unfold CartProd
    /- Surface instances -/
    have := Species.finite (F := F) (U := U)
    have := Species.finite (F := G) (U := U)
    infer_instance
  transport      := fun {U V} _ _ σ ⟨f, g⟩       => (transport σ f, transport σ g)
  id_transport   := fun {U} _ ⟨f, g⟩             => by simp only [id_transport  ]; rfl
  comp_transport := fun {U V W} _ _ _ σ τ ⟨f, g⟩ => by simp only [comp_transport]; rfl

variable {F G : Type → Type} [ComputableSpecies F] [ComputableSpecies G] {U : Type}

instance instComputableSpecies : ComputableSpecies (CartProd F G) where
  fintype := fun {U} _ => show Fintype (F U × G U) from inferInstance
  decEq   := by
    intros U _; unfold CartProd
    /- Surface some instances -/
    haveI := ComputableSpecies.decEq (F := F) (U := U)
    haveI := ComputableSpecies.decEq (F := G) (U := U)
    infer_instance

end CartProd

end Species
