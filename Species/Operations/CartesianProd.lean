import Species.Basic

namespace Species

variable {F G : Type → Type} [Species F] [Species G]

def cartProd (F G : Type → Type) (U : Type) : Type := F U × G U

notation:65 F " × " G => Species.cartProd F G

instance instSpeciesCartProd : Species (F × G) where
  fintype := fun {U} _ =>
    show Fintype (F U × G U) from inferInstance

  transport := fun {U V} _ _ σ ⟨f, g⟩ =>
    (transport σ f, transport σ g)

  transport_trans := fun {U V W} _ _ _ σ τ ⟨f, g⟩ => by
    simp [transport_trans]

  transport_id := fun {U} _ ⟨f, g⟩ => by
    simp [transport_id]

end Species
