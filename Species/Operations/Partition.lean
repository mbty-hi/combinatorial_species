import Species.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Basic
import Mathlib.Data.Prod.Lex

namespace Species

variable {F G : Type → Type} [Species F] [Species G] {U V : Type} {n : ℕ}

def Part (n : ℕ) (F : Type → Type) (U : Type) : Type :=
  Σ split : U → Fin n, ∀ i : Fin n, F {u // split u = i}

/- Relabelling a split: `v` falls in the same block as its `σ`-preimage. -/
abbrev transportSplit {U V : Type} (σ : U ≃ V) (split : U → Fin n) : V → Fin n :=
  split ∘ σ.symm

/- There is a bijection between blocks before and after transport. -/
def blockEquiv {U V} (σ : U ≃ V) (split : U → Fin n) (x : Fin n)
: {u // split u = x} ≃ {v // transportSplit σ split v = x} :=
  σ.subtypeEquiv (fun u => by simp [Equiv.symm_apply_apply])

/- Species instance -/
instance instSpeciesPart : Species (Part n F) where
  fintype := fun {U} _ => by unfold Part; infer_instance
  transport := fun σ ⟨split, f⟩ => ⟨
    transportSplit σ split,
    fun i => Species.transport (blockEquiv σ split i) (f i)
  ⟩
  transport_id := by
    rintro U _ ⟨split, f⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext i                                  -- fibre is a Π, so funext, not Prod.ext
    have foo : blockEquiv (Equiv.refl U) split i = Equiv.refl _ := by
      apply Equiv.ext; rintro ⟨u, hu⟩; apply Subtype.ext; rfl
    simp [foo]; exact Species.transport_id (f i)
  transport_trans := by
    rintro U V W _ _ _ σ τ ⟨split, f⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext i
    have foo : blockEquiv (σ.trans τ) split i
         = (blockEquiv σ split i).trans (blockEquiv τ (transportSplit σ split) i) := by
      apply Equiv.ext; rintro ⟨u, hu⟩; apply Subtype.ext; rfl
    simp [foo]
    exact Species.transport_trans (blockEquiv σ split i) (blockEquiv τ (transportSplit σ split) i) (f i)
