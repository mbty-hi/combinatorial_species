import Species.Basic
import Mathlib.Data.Prod.Lex

namespace Species

variable {F G : Type → Type} [Species F] [Species G] {U : Type}

def cartProd (F G : Type → Type) (U : Type) : Type := F U × G U

--notation:65 F " × " G => Species.cartProd F G

/- Display related instances -/
instance instReprCartProd {F G : Type → Type} {U : Type} [Repr (F U)] [Repr (G U)]
: Repr ((cartProd F G) U) :=
  inferInstanceAs (Repr (F U × G U))

instance instLinearOrderCartProd
  {F G : Type → Type} {U : Type} [LinearOrder (F U)] [LinearOrder (G U)]
: LinearOrder ((cartProd F G) U) :=
  inferInstanceAs (LinearOrder (F U ×ₗ G U))

/- Species instance -/
-- TODO find ways of using × instead of cartProd
--instance instSpeciesCartProd : Species (fun t => (F t) × (G t)) where
instance instSpeciesCartProd : Species (cartProd F G) where
  finite := by
    intros U _; unfold cartProd
    /- Surface instances -/
    haveI := Species.finite (F := F) (U := U)
    haveI := Species.finite (F := G) (U := U)
    infer_instance
  transport      := fun {U V} _ _ σ ⟨f, g⟩       => (transport σ f, transport σ g)
  id_transport   := fun {U} _ ⟨f, g⟩             => by simp [id_transport]
  comp_transport := fun {U V W} _ _ _ σ τ ⟨f, g⟩ => by simp [comp_transport]

instance instSpeciesCompCartProd [SpeciesComp F] [SpeciesComp G] : SpeciesComp (cartProd F G) where
  fintype := fun {U} _ => show Fintype (F U × G U) from inferInstance
  decEq   := by
    intros U _ _ _; unfold cartProd
    /- Surface some instances -/
    haveI := SpeciesComp.decEq (F := F) (U := U)
    haveI := SpeciesComp.decEq (F := G) (U := U)
    infer_instance
end Species
