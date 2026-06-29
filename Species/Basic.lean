import Mathlib.GroupTheory.Perm.Basic
import Species.Labels.LabelType

class Species (F : Type → Type) where
  fintype: {α : Type} → [LabelType α] → Fintype (F α)
  transport: {α β : Type} → [LabelType α] → [LabelType β] → (α ≃ β) → F α → F β
  transport_trans:
    ∀ {α β γ : Type} [LabelType α] [LabelType β] [LabelType γ] (σ : α ≃ β) (τ : β ≃ γ) (f : F α),
    transport (σ.trans τ) f = (transport τ ∘ transport σ) f
  transport_id: ∀ {α : Type} [LabelType α] (f : F α), transport (Equiv.refl α) f = f

namespace Species

variable {F : Type → Type} [Species F] {α β : Type} [LabelType α] [LabelType β]

/- For any `LabelType` α, there is a finite number of `F`-structures labelled with α. -/
instance instFintypeOfSpecies : Fintype (F α) := Species.fintype

/- Relabelling is an action of `Equiv.Perm U` on `F U` (`σ • f := transport σ f`). Its orbits are
   the isomorphism types of `F`-structures. -/
instance {U : Type} [LabelType U] (F : Type → Type) [Species F]
: MulAction (Equiv.Perm U) (F U) where
  smul σ f       := Species.transport σ f
  one_smul       := Species.transport_id
  mul_smul σ τ f := Species.transport_trans τ σ f

/- The finite set of `F`-structures on label type `α`. -/
def structures : Finset (F α) := Finset.univ

/- Transport bundled as an equivalence: every bijection between label types induces a bijection of
   labelled structures. -/
def transportEquiv (σ : α ≃ β) : F α ≃ F β where
  toFun     := transport σ
  invFun    := transport σ.symm
  left_inv  := fun f => by
    have h := transport_trans σ σ.symm f
    rw [Equiv.self_trans_symm, transport_id] at h
    exact h.symm
  right_inv := fun f => by
    have h := transport_trans σ.symm σ f
    rw [Equiv.symm_trans_self, transport_id] at h
    exact h.symm

/- Sanity check: structure count depends only on the cardinality of labels. -/
theorem card_structures_eq (σ : α ≃ β) : Fintype.card (F α) = Fintype.card (F β) :=
  Fintype.card_congr (transportEquiv σ)

-- TODO test notations
scoped notation:max F "[" α "]" => Species.structures (F := F) (α := α)
scoped notation:max f "⟦" σ "⟧" => σ • f

end Species
