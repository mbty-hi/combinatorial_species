import Mathlib.GroupTheory.Perm.Basic
import Species.Labels.LabelType

-- Finite-based species class, faithful to the book
class Species (F : Type → Type) where
  finite : {U : Type} → [Finite U] → Finite (F U)
  transport : {U V : Type} → [Finite U] → [Finite V] → (U ≃ V) → F U → F V
  id_transport : ∀ {U} [Finite U] (f : F U), transport (Equiv.refl U) f = f
  comp_transport :
    ∀ {U V W} [Finite U] [Finite V] [Finite W] (σ : U ≃ V) (τ : V ≃ W) (f : F U),
    transport (σ.trans τ) f = (transport τ ∘ transport σ) f

namespace Species

variable {F : Type → Type} [Species F] {U V : Type} [Finite U] [Finite V]

/- For any `LabelType U`, there is a finite number of `F`-structures labelled with `U`. -/
instance instFiniteSpecies : Finite (F U) := Species.finite

/- Relabelling is an action of `Equiv.Perm U` on `F U` (`σ • f := transport σ f`). Its orbits are
   the isomorphism types of `F`-structures. -/
instance instMulActionSpecies {U : Type} [LabelType U] (F : Type → Type) [Species F]
: MulAction (Equiv.Perm U) (F U) where
  smul σ f       := transport σ f
  one_smul       := id_transport
  mul_smul σ τ f := comp_transport τ σ f

/- Transport bundled as an equivalence: every bijection between label types induces a bijection of
   labelled structures. -/
def transportEquiv (σ : U ≃ V) : F U ≃ F V where
  toFun    := Species.transport σ
  invFun   := Species.transport σ.symm
  left_inv := fun f => by
    have h := Species.comp_transport σ σ.symm f
    rw [Equiv.self_trans_symm, Species.id_transport] at h
    exact h.symm
  right_inv := fun f => by
    have h := Species.comp_transport σ.symm σ f
    rw [Equiv.symm_trans_self, Species.id_transport] at h
    exact h.symm

theorem transportEquiv_symm {U V} {F: Type → Type} [Finite U] [Finite V] [Species F] (σ : U ≃ V)
: (Species.transportEquiv (F := F) σ.symm) = (Species.transportEquiv (F := F) σ).symm :=
  Equiv.ext fun _ => rfl

theorem transport_transport
  {F : Type → Type} [Species F] {α β γ : Type}
  [Finite α] [Finite β] [Finite γ] (σ : α ≃ β) (τ : β ≃ γ) (f : F α)
: Species.transport τ (Species.transport σ f) = Species.transport (σ.trans τ) f := by
  have h := Species.comp_transport (F := F) σ τ f
  rw [Function.comp_apply] at h
  exact h.symm

theorem transport_eq_self_of_val
  {F : Type → Type} [Species F] {α : Type} [Finite α] (e : α ≃ α) (h : ∀ a, e a = a) (f : F α)
: Species.transport e f = f := by
  have he : e = Equiv.refl α := Equiv.ext h
  rw [he, Species.id_transport]

end Species

class SpeciesComp (F : Type → Type) extends Species F where
  fintype : {U : Type} → [LabelType U] → Fintype (F U)
  decEq   : {U : Type} → [LabelType U] → DecidableEq (F U)

namespace SpeciesComp

variable {F : Type → Type} [SpeciesComp F] {U V : Type} [LabelType U] [LabelType V]

/- For any `LabelType U`, there is a finite number of `F`-structures labelled with `U`. -/
instance instFintypeOfSpecies : Fintype (F U) := fintype

/- The finite set of `F`-structures on label type `U`. -/
def structures : Finset (F U) := Finset.univ

/- Sanity check: structure count depends only on the cardinality of labels. -/
theorem card_structures_eq (σ : U ≃ V) : Fintype.card (F U) = Fintype.card (F V) :=
  Fintype.card_congr (Species.transportEquiv σ)

instance instDecEqOfSpecies {F : Type → Type} [SpeciesComp F] {U : Type} [LabelType U]
: DecidableEq (F U) :=
  decEq

end SpeciesComp
