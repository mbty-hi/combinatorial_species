import Species.Basic
import Mathlib.Data.Fintype.Sigma

namespace Species

variable {F G : Type → Type} [Species F] [Species G]
variable {U V : Type} [LabelType U] [LabelType V]

def mul (F G : Type → Type) (U : Type) : Type :=
  Σ d : U → Bool, F {u // d u = true} × G {u // d u = false}

-- σ restricts to each color class; precomposition by σ.symm relabels the coloring.
-- block equiv on the `true` class:  {u // d u} ≃ {v // (d ∘ σ.symm) v}
def colorEquiv {U V} (σ : U ≃ V) (d : U → Bool) (b : Bool)
: {u // d u = b} ≃ {v // (d ∘ σ.symm) v = b} :=
  σ.subtypeEquiv (fun u => by simp [Function.comp, Equiv.symm_apply_apply])

def mul.transport {U V} [LabelType U] [LabelType V] (σ : U ≃ V)
: mul F G U → mul F G V :=
  fun ⟨d, f, g⟩ =>
    ⟨ d ∘ σ.symm,
      Species.transport (colorEquiv σ d true) f,
      Species.transport (colorEquiv σ d false) g ⟩

theorem colorEquiv_trans {U V W} (σ : U ≃ V) (τ : V ≃ W) (d : U → Bool) (b : Bool) :
    colorEquiv (σ.trans τ) d b
      = (colorEquiv σ d b).trans (colorEquiv τ (d ∘ σ.symm) b) := by
  apply Equiv.ext; rintro ⟨u, hu⟩; apply Subtype.ext; rfl
  -- both send u ↦ τ (σ u); the `d ∘ σ.symm` index on the middle type lines up definitionally

instance instSpeciesMul : Species (mul F G) where
  fintype := fun {U} _ => by unfold mul; infer_instance   -- Pi.fintype: Fintype (U → Bool)
  transport := fun σ x => mul.transport σ x
  transport_id := by
    rintro U _ ⟨d, f, g⟩
    -- index d ∘ refl.symm ≡ d definitionally ⇒ fibers homogeneous
    simp only [mul.transport, Equiv.refl_symm]
    -- remaining: colorEquiv refl d b = Equiv.refl _, then Species.transport_id
    refine Sigma.ext rfl (heq_of_eq ?_)
    ext <;> simp [colorEquiv, Equiv.subtypeEquiv]
    · exact Species.transport_id f
    · exact Species.transport_id g
  transport_trans := by
    rintro U V W _ _ _ σ τ ⟨d, f, g⟩
    simp only [mul.transport]
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Prod.ext
    · rw [colorEquiv_trans]
      exact Species.transport_trans (colorEquiv σ d true) (colorEquiv τ (d ∘ σ.symm) true) f
    · rw [colorEquiv_trans]
      exact Species.transport_trans (colorEquiv σ d false) (colorEquiv τ (d ∘ σ.symm) false) g

end Species
