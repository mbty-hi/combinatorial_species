import Species.Basic
import Species.Labels.LabelType

import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Basic
import Species.Labels.LabelType
import Mathlib.Data.Fintype.Sigma

import Mathlib.Data.Setoid.Basic

import Mathlib.Order.Basic
import Mathlib.Data.Finset.Max
import Species.Labels.LabelType

/- We encode composition as a decidable equivalence relation on the label set (U → U → Bool)
   (like a coloring, except that there is no order between equivalence classes, so we do not need to
   manually correct for overcounting). -/

/- To define this, we first need a notion of a decidable equivalence relation. A setoid almost fits
   the bill, but we need computability, so we use `(U → U → Bool)` instead of `U → U → Prop`. -/
structure DecSetoid (α : Type) where
  d     : α → α → Bool
  iseqv : Equivalence (fun x y => d x y = true)

namespace DecSetoid
  variable {α β : Type}

  -- We can easily get a standard setoid from a decidable one
  def toSetoid (s : DecSetoid α) : Setoid α :=
    ⟨fun x y => s.d x y = true, s.iseqv⟩

  -- We need a way of remapping DecSetoids to define `transport`.
  def map (s : DecSetoid α) (σ : α ≃ β) : DecSetoid β where
    d     := fun x y => s.d (σ.symm x) (σ.symm y)
    iseqv := (s.toSetoid.comap σ.symm).iseqv

  -- Interactions with quotienting arise because the outer type is applied to `U` after quotienting
  -- by `d`.
  def quotEquiv (s : DecSetoid α) (σ : α ≃ β)
  : Quotient s.toSetoid ≃ Quotient (s.map σ).toSetoid := by
    apply Quotient.congr σ; intros x y
    constructor <;> intros h <;> simp [toSetoid, map] at * <;> exact h

  -- This is about remapping blocks.
  def blockEquiv (s : DecSetoid α) (σ : α ≃ β) (block : Quotient (s.map σ).toSetoid)
  : {x // Quotient.mk s.toSetoid x = (s.quotEquiv σ).symm block}
    ≃ {y // Quotient.mk (s.map σ).toSetoid y = block}
  where
    toFun := by
      rintro ⟨block_rep, hblock_rep⟩; constructor
      case val      => exact σ block_rep
      case property => have h := congrArg (s.quotEquiv σ) hblock_rep; simp [quotEquiv] at h; exact h
    invFun := by
      rintro ⟨block_rep, hblock_rep⟩; constructor
      case val      => exact σ.symm block_rep
      case property => subst block; apply (s.quotEquiv σ).injective; simp [quotEquiv]
    left_inv  := fun ⟨block, _⟩ => Subtype.ext (σ.symm_apply_apply block)
    right_inv := fun ⟨block, _⟩ => Subtype.ext (σ.apply_symm_apply block)
end DecSetoid

-- The actual operation definition
structure Composition (F G: Type → Type) (U: Type) where
  partition: DecSetoid U
  outer    : F (Quotient partition.toSetoid)
  inner    : Π (eqv_class : Quotient partition.toSetoid), G { x // ⟦x⟧ = eqv_class }

namespace Composition
  variable {U V : Type} [LabelType U] [LabelType V] {F G : Type → Type} [Species F] [Species G]

  def transport (σ : U ≃ V) (c : Composition F G U) : Composition F G V where
    partition := c.partition.map σ
    outer     := Species.transport (c.partition.quotEquiv σ) c.outer
    inner     :=
      fun b =>
        Species.transport
          (c.partition.blockEquiv σ b)
          (c.inner ((c.partition.quotEquiv σ).symm b))
end Composition
