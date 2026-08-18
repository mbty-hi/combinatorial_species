import Species.Basic
import Species.Labels.LabelType
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Setoid.Basic

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

-- BEGSLOP
@[simp] theorem quotEquiv_refl (s : DecSetoid α)
: s.quotEquiv (Equiv.refl α) = Equiv.refl (Quotient s.toSetoid) :=
  Equiv.ext fun q => q.inductionOn fun _ => rfl
-- ENDSLOP
end DecSetoid

-- The actual operation definition
structure Composition (F G: Type → Type) (U: Type) where
  partition: DecSetoid U
  outer    : F (Quotient partition.toSetoid)
  inner    : Π (eqv_class : Quotient partition.toSetoid), G { x // ⟦x⟧ = eqv_class }

namespace Composition
  variable {U V W : Type} [Finite U] [Finite V] [Finite W]
  variable {F G : Type → Type} [Species F] [Species G]

  def transport (σ : U ≃ V) (c : Composition F G U) : Composition F G V where
    partition := c.partition.map σ
    outer     := Species.transport (c.partition.quotEquiv σ) c.outer
    inner     :=
      fun b =>
        Species.transport
          (c.partition.blockEquiv σ b)
          (c.inner ((c.partition.quotEquiv σ).symm b))

-- BEGSLOP
theorem transport_id (c : Composition F G U) : transport (Equiv.refl U) c = c := by
  obtain ⟨p, o, i⟩ := c; simp only [transport, Composition.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  . apply heq_of_eq; rw [DecSetoid.quotEquiv_refl]; exact Species.transport_id o
  . apply heq_of_eq; funext b; refine Quotient.inductionOn b fun x => Species.transport_id _

theorem transport_trans (σ : U ≃ V) (τ : V ≃ W) (c : Composition F G U)
: transport (σ.trans τ) c = (transport τ ∘ transport σ) c := by
  obtain ⟨p, o, i⟩ := c
  simp only [transport, Function.comp_apply, Composition.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  . apply heq_of_eq
    have foo := Species.transport_trans (p.quotEquiv σ) ((p.map σ).quotEquiv τ) o
    simp at foo; simp [← foo]; congr
    exact Equiv.ext fun q => q.inductionOn fun x => rfl
  . refine heq_of_eq (funext fun b => ?_)
    refine Quotient.inductionOn b fun z => ?_
    exact Species.transport_trans
      (p.blockEquiv σ (((p.map σ).quotEquiv τ).symm (Quotient.mk _ z)))
      ((p.map σ).blockEquiv τ (Quotient.mk _ z)) _

def equivSigma
: Composition F G U ≃ Σ s : DecSetoid U,
  F (Quotient s.toSetoid) × ∀ b, G {x // Quotient.mk s.toSetoid x = b}
where
  toFun c     := ⟨c.partition, c.outer, c.inner⟩
  invFun p    := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _  := rfl
  right_inv _ := rfl

instance {α : Type} [Finite α] : Finite (DecSetoid α) :=
  Finite.of_injective (fun s => s.d) (fun s₁ s₂ h => by cases s₁; cases s₂; simpa using h)
-- ENDSLOP

/-   theorem transport_id: ∀ (c : Composition F G U), transport (Equiv.refl U) c = c := by -/
/-     rintro ⟨c_part, c_out, c_in⟩ -/
/-     simp [transport] -/
/-     refine ⟨?outs, ?ins⟩ -/
/-     /1- case parts => simp [DecSetoid.map] -1/ -/
/-     case outs => sorry -/
/-     case ins => simp [decSetoid.quotEquiv, DecSetoid.blockEquiv]; sim -/

instance instSpeciesComposition : Species (Composition F G) where
  finite          := Finite.of_equiv _ equivSigma.symm
  transport       := transport
  transport_id    := transport_id
  transport_trans := transport_trans

end Composition
