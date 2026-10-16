module

public import Species.Basic
public import Species.Computable
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section

namespace Species

def CartProd (F G : Type → Type) (U : Type) : Type := F U × G U

namespace CartProd

variable {F G : Type → Type} [Species F] [Species G] {U : Type}

section Display

instance instRepr [Repr (F U)] [Repr (G U)] : Repr ((CartProd F G) U) :=
  inferInstanceAs (Repr (F U × G U))

instance instLinearOrder [LinearOrder (F U)] [LinearOrder (G U)] : LinearOrder ((CartProd F G) U) :=
  inferInstanceAs (LinearOrder (F U ×ₗ G U))

end Display

instance instSpecies : Species (CartProd F G) where
  finite         := fun {U} _                    => by unfold CartProd; infer_instance
  transport      := fun {U V} _ _ σ ⟨f, g⟩       => (transport σ f, transport σ g)
  id_transport   := fun {U} _ ⟨f, g⟩             => by simp only [id_transport  ]; rfl
  comp_transport := fun {U V W} _ _ _ σ τ ⟨f, g⟩ => by simp only [comp_transport]; rfl

instance instComputableSpecies {F G : Type → Type} [ComputableSpecies F] [ComputableSpecies G]
: ComputableSpecies (CartProd F G) where
  fintype := fun {U} _ => show Fintype (F U × G U) from inferInstance
  decEq   := fun {U} _ => by unfold CartProd; infer_instance

end CartProd
end Species
end
