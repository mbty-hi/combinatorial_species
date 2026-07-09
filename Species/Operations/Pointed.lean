import Species.Basic
import Mathlib.Data.Prod.Lex

namespace Species

variable {F : Type → Type} [Species F] {α : Type}

def Pointed (F : Type → Type) (α : Type) : Type := α × F α


instance instSpeciesPointed : Species (Pointed F) where
  fintype         := fun {α} _                    => show Fintype (α × F α ) from inferInstance
  transport       := fun {α β} _ _ σ x         => (σ x.1, Species.transport σ x.2)
  transport_trans := fun {α β γ} _ _ _ σ τ f => by simp [Species.transport_trans]
  transport_id    := fun {α} _ f             => by simp [Species.transport_id]

end Species
