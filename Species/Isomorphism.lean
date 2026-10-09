import Species.Basic

namespace Species

variable (F G H : Type → Type) [Species F] [Species G] [Species H]

structure Iso where
  equiv   (U : Type)   [Finite U] : F U ≃ G U
  natural {U V : Type} [Finite U] [Finite V] (σ : U ≃ V) (fu : F U) :
    equiv V (Species.transport σ fu) = Species.transport σ (equiv U fu)

namespace Iso

def refl : Iso F F where
  equiv   _   := Equiv.refl _
  natural _ _ := rfl

def symm (iso : Iso F G) : Iso G F where
  equiv   U    := (iso.equiv U).symm
  natural σ gu := by
    rw [Equiv.symm_apply_eq]    -- transport = equiv ∘ transport ∘ equiv'
    rw [natural]                -- use equiv ∘ transport = transport ∘ equiv:
                                -- transport = transport ∘ equiv ∘ equiv'
    rw [Equiv.apply_symm_apply] -- use equiv ∘ equiv' = id

def trans (iso₁ : Iso F G) (iso₂ : Iso G H) : Iso F H where
  equiv   U    := (iso₁.equiv U).trans (iso₂.equiv U)
  natural σ fu := by simp; rw [natural, natural]

end Iso

end Species
