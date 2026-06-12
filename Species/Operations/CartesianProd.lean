import Species.Basic
import Mathlib.Data.Prod.Lex

namespace Species

variable {F G : Type → Type} [Species F] [Species G] {α : Type}

def cartProd (F G : Type → Type) (α : Type) : Type := F α × G α

--notation:65 F " × " G => Species.cartProd F G

/- Display related instances -/
instance instReprCartProd {F G : Type → Type} {α : Type} [Repr (F α)] [Repr (G α)]
: Repr ((cartProd F G) α) :=
  inferInstanceAs (Repr (F α × G α))

instance instLinearOrderCartProd
  {F G : Type → Type} {α : Type} [LinearOrder (F α)] [LinearOrder (G α)]
: LinearOrder ((cartProd F G) α) :=
  inferInstanceAs (LinearOrder (F α ×ₗ G α))

/- Species instance -/
-- TODO find ways to use × instead of cartProd
--instance instSpeciesCartProd : Species (fun t => (F t) × (G t)) where
instance instSpeciesCartProd : Species (cartProd F G) where
  fintype         := fun {α} _                    => show Fintype (F α × G α) from inferInstance
  transport       := fun {α β} _ _ σ ⟨f, g⟩       => (transport σ f, transport σ g)
  transport_trans := fun {α β γ} _ _ _ σ τ ⟨f, g⟩ => by simp [transport_trans]
  transport_id    := fun {α} _ ⟨f, g⟩             => by simp [transport_id]

end Species
