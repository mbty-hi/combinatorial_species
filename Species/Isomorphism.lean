import Species.Basic

/-!
# Isomorphism of species
This file defines the notion of isomorphism for species.

## Important definitions
* `Iso` : a structure for the isomorphisms of species (a family of bijections respecting a
  naturality condition)
* `Iso.refl` : the identity isomorphism
* `Iso.symm` : the inverse isomorphism
* `Iso.trans` : the composite isomorphism

## References
* [F. Bergeron, G. Labelle, P. Leroux, *Combinatorial Species and Tree-like Structures*][BLL]
-/

namespace Species

/-- An isomorphism of species (i.e., a family of bijections `F[U] ≃ G[U]` that are natural in `U`).
Although the notion of isomorphism of species is weaker than that of equality, isomorphic species
share their essential combinatorial properties (in particular, their series match). In algebraic
settings, [BLL] in fact uses `=` in lieu of `≅`. -/
structure Iso (F G : Type → Type) [Species F] [Species G] where
  /-- A family of bijections. -/
  equiv (U : Type) [Finite U] : F U ≃ G U
  /-- `equiv` respects a naturality condition: the following diagram must commute (`αᵤ` corresponds
  to `equiv U`).
             αᵤ
      F[U] ─────► G[U]
  F[σ] │            │ G[σ]
       ▼     αᵥ     ▼
      F[V] ─────► G[V]
  -/
  naturality {U V : Type} [Finite U] [Finite V] (σ : U ≃ V) (fu : F U) :
    equiv V (transport σ fu) = transport σ (equiv U fu)

namespace Iso

variable {F G H : Type → Type} [Species F] [Species G] [Species H]

/-- The identity isomorphism (reflexivity of isomorphism). -/
def refl (F : Type → Type) [Species F] : Iso F F where
  equiv      _   := Equiv.refl _
  naturality _ _ := rfl

/-- The inverse isomorphism (symmetry of isomorphism). -/
def symm (iso : Iso F G) : Iso G F where
  equiv   U    := (iso.equiv U).symm
  naturality σ gu := by
    rw [Equiv.symm_apply_eq]    -- transport = equiv ∘ transport ∘ equiv⁻¹
    rw [iso.naturality]         -- use equiv ∘ transport = transport ∘ equiv:
                                -- transport = transport ∘ equiv ∘ equiv⁻¹
    rw [Equiv.apply_symm_apply] -- use equiv ∘ equiv⁻¹ = id

/-- The composite isomorphism (transitivity of isomorphism). -/
def trans (iso₁ : Iso F G) (iso₂ : Iso G H) : Iso F H where
  equiv      U    := (iso₁.equiv U).trans (iso₂.equiv U)
  naturality σ fu := by simp only [Equiv.trans_apply]; rw [iso₁.naturality, iso₂.naturality]

end Iso

end Species
