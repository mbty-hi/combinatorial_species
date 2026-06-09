import Init.Control.Lawful.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Embedding

/- A label type: finite, linearly ordered. The order is required for computationality (`Finset`
   exposes a `sort` function that gives a list of its members, and it requires `LinearOrder`). -/
class LabelType (U: Type) extends Fintype U, LinearOrder U

/- Build `LabelType` from its parents. -/
instance {U: Type} [Fintype U] [LinearOrder U] : LabelType U where
  toFintype     := inferInstance
  toLinearOrder := inferInstance

class Species (F: Type → Type) where
  fintype: {U: Type} → [LabelType U] → Fintype (F U)
  transport: {U V: Type} → [LabelType U] → [LabelType V] → (U ≃ V) → F U → F V
  transport_trans:
    ∀ {U V W: Type} [LabelType U] [LabelType V] [LabelType W] (σ: U ≃ V) (τ: V ≃ W) (f: F U),
    transport (σ.trans τ) f = (transport τ ∘ transport σ) f
  transport_id: ∀ {U: Type} [LabelType U] (f: F U), transport (Equiv.refl U) f = f

namespace Species

variable {F: Type → Type} [Species F] {U V: Type} [LabelType U] [LabelType V]

/- For any `LabelType` U, there is a finite number of `F`-structures labelled with U. -/
instance instFintypeOfSpecies : Fintype (F U) := Species.fintype

/- The finite set of `F`-structures on label type `U`. -/
def structures : Finset (F U) := Finset.univ

/- Transport bundled as an equivalence: every bijection between label types induces a bijection of
   labelled structures. -/
def transportEquiv (σ: U ≃ V) : F U ≃ F V where
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
theorem card_structures_eq (σ: U ≃ V) : Fintype.card (F U) = Fintype.card (F V) :=
  Fintype.card_congr (transportEquiv σ)

-- TODO test notations
scoped notation:max F "[" U "]" => Species.structures (F := F) (U := U)
scoped notation:max f "⟦" σ "⟧" => Species.transport σ f

end Species
