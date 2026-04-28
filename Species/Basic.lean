import Init.Control.Lawful.Basic
import Init.Data.List.Perm
import Init.Data.List.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.List.Permutation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Logic.Equiv.Embedding

class Species {F: Type → Type} where
  structures: {U: Type} → [DecidableEq U] → (labels: Finset U) → (Finset (F U))
  transport: {U V: Type} → {σ: U → V} → (σ_bij: Function.Bijective σ) → (f: F U) → F V
  transport_trans:
    ∀{U V W: Type} {σ: U → V} {τ: V → W}
     (σ_bij: Function.Bijective σ) (τ_bij: Function.Bijective τ)
     (f: F U),
    @transport U W (τ ∘ σ) (Function.Bijective.comp τ_bij σ_bij) f
    = ((@transport V W τ τ_bij) ∘ (@transport U V σ σ_bij)) f
  transport_id: ∀{U: Type} (f: F U), transport Function.bijective_id f = id f

def CatB (α: Type) : Type := CategoryTheory.Core (Finset α)

/- /1- A species can be defined as an endofunctor on the category B (whose objects are FinSets and whose -/
/-    morphisms are bijections) -1/ -/
/- def SpeciesFunctorial {α β: Type} : Type := -/
/-   Functor -/

/- instance SpeciesFunctorial_to_Species {F: Type → Type} where -/

def SpeciesEquivalence {F: Type → Type} [S: @Species F] {U: Type} (s t: F U) : Prop :=
  ∃(σ: U → U) (σ_bij: Function.Bijective σ), S.transport σ_bij s = t

-- FIXME
notation:80 lhs:81 "[σ" rhs:80 "]" => Species.transport rhs lhs
notation:80 lhs:81 "[" rhs:80 "]" => Species.get_structures rhs lhs
