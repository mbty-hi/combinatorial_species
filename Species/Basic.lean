import Mathlib.GroupTheory.Perm.Basic
import Species.Labels.LabelType

-- Finite-based species class, faithful to the book
class Species (F : Type → Type) where
  finite : {U : Type} → [Finite U] → Finite (F U)
  transport : {U V : Type} → [Finite U] → [Finite V] → (U ≃ V) → F U → F V
  transport_id : ∀ {U} [Finite U] (f : F U), transport (Equiv.refl U) f = f
  transport_trans :
    ∀ {U V W} [Finite U] [Finite V] [Finite W] (σ : U ≃ V) (τ : V ≃ W) (f : F U),
    transport (σ.trans τ) f = (transport τ ∘ transport σ) f

class SpeciesComp (F : Type → Type) extends Species F where
  fintype : {U : Type} → [LabelType U] → Fintype (F U)
  decEq   : {U : Type} → [LabelType U] → DecidableEq (F U)


namespace Species

variable {F : Type → Type} [Species F] {U V : Type} [Finite U] [Finite V]

/- For any `LabelType U`, there is a finite number of `F`-structures labelled with `U`. -/
instance instFiniteOfSpecies : Finite (F U) := Species.finite

/- Relabelling is an action of `Equiv.Perm U` on `F U` (`σ • f := transport σ f`). Its orbits are
   the isomorphism types of `F`-structures. -/
instance {U : Type} [LabelType U] (F : Type → Type) [Species F]
: MulAction (Equiv.Perm U) (F U) where
  smul σ f       := transport σ f
  one_smul       := transport_id
  mul_smul σ τ f := transport_trans τ σ f

/- Transport bundled as an equivalence: every bijection between label types induces a bijection of
   labelled structures. -/
def transportEquiv (σ : U ≃ V) : F U ≃ F V where
  toFun     := Species.transport σ
  invFun    := Species.transport σ.symm
  left_inv  := fun f => by
    have h := Species.transport_trans σ σ.symm f
    rw [Equiv.self_trans_symm, Species.transport_id] at h
    exact h.symm
  right_inv := fun f => by
    have h := Species.transport_trans σ.symm σ f
    rw [Equiv.symm_trans_self, Species.transport_id] at h
    exact h.symm

end Species

namespace SpeciesComp

variable {F : Type → Type} [SpeciesComp F] {U V : Type} [LabelType U] [LabelType V]

/- For any `LabelType U`, there is a finite number of `F`-structures labelled with `U`. -/
instance instFintypeOfSpecies : Fintype (F U) := fintype

/- Relabelling is an action of `Equiv.Perm U` on `F U` (`σ • f := transport σ f`). Its orbits are
   the isomorphism types of `F`-structures. -/
instance {U : Type} [LabelType U] (F : Type → Type) [Species F]
: MulAction (Equiv.Perm U) (F U) where
  smul σ f       := Species.transport σ f
  one_smul       := Species.transport_id
  mul_smul σ τ f := Species.transport_trans τ σ f

/- The finite set of `F`-structures on label type `U`. -/
def structures : Finset (F U) := Finset.univ

/- Sanity check: structure count depends only on the cardinality of labels. -/
theorem card_structures_eq (σ : U ≃ V) : Fintype.card (F U) = Fintype.card (F V) :=
  Fintype.card_congr (Species.transportEquiv σ)

-- TODO test notations
scoped notation:max F "[" U "]" => Species.structures (F := F) (U := U)
scoped notation:max f "⟦" σ "⟧" => σ • f

end SpeciesComp
