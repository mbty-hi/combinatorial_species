import Species.Basic

namespace Species

variable {F G : Type → Type} [Species F] [Species G] {U: Type}

def cartProd (F G : Type → Type) (U : Type) : Type := F U × G U

--notation:65 F " × " G => Species.cartProd F G

instance : Prod (Type → Type) (Type → Type) where
  fst := F
  snd := G

--instance instSpeciesCartProd : Species (fun t => (F t) × (G t)) where
instance instSpeciesCartProd : Species (cartProd F G) where --find ways to use × instead of cartProd
  fintype := fun {U} _ =>
    show Fintype (F U × G U) from inferInstance

  transport := fun {U V} _ _ σ ⟨f, g⟩ =>
    (transport σ f, transport σ g)

  transport_trans := fun {U V W} _ _ _ σ τ ⟨f, g⟩ => by
    simp [transport_trans]

  transport_id := fun {U} _ ⟨f, g⟩ => by
    simp [transport_id]

end Species
