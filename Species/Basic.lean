import Init.Control.Lawful.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Embedding

class Species (F: Type → Type) where
  structures: {U: Type} → [DecidableEq U] → (labels: Finset U) → Finset (F U)
  transport: {U V: Type} → (U ≃ V) → F U → F V
  transport_trans:
    ∀ {U V W: Type} (σ: U ≃ V) (τ: V ≃ W) (f: F U),
    transport (σ.trans τ) f = (transport τ ∘ transport σ) f
  transport_id: ∀ {U: Type} (f: F U), transport (Equiv.refl U) f = f

/- A theorem such as
   ```
   theorem transport_structures_ok
     {F: Type → Type} {U V: Type} [DecidableEq U] [DecidableEq V]
     (SF: Species F) (σ: U ≃ V) (labels: Finset U)
   : SF.structures (labels.map σ.toEmbedding)
     = (SF.structures labels).map ⟨SF.transport σ, by apply transport_injective⟩
   ```
   with
   ```
   theorem transport_injective
     {F: Type → Type} (SF: Species F) {U V: Type} [DecidableEq U] [DecidableEq V] (σ: U ≃ V)
   : (SF.transport σ).Injective :=
     Function.LeftInverse.injective
       (g := SF.transport σ.symm)
       (fun fu => by
         have x := SF.transport_trans σ σ.symm fu
         simp at x
         simp [SF.transport_id, ← x]
       )
   ```
   would be a nice sanity check to have, but Lean does not let us prove it.

   Indeed, although it looks as though we should be able to do so by parametricity (i.e., as the
   function is parametric, we cannot manipulate objects differently depending on their values: they
   are opaque to us). Alas, the axiom of parametricity is not compatible with Lean's standard
   axioms, as we can use the excluded middle to define (noncomputable) functions violating it:
  ```
  noncomputable def nonParametric {α : _} (xs : List α) : List α :=
    if α = Nat then [] else xs
  ```
  (example from https://lean-lang.org/doc/reference/latest/Axioms/#axiom-consistency)

  Note that something similar could be proven for any concrete (and computable, or at least not evil
  like in the above example) instance of Species.

  TODO add as axiom?
  -/

/- TODO A species can be defined as an endofunctor on the category B (whose objects are FinSets and whose
   morphisms are bijections). Conversion. -/
/- open CategoryTheory -/

-- FIXME
notation:80 lhs:81 "[σ" rhs:80 "]" => Species.transport rhs lhs
notation:80 lhs:81 "[" rhs:80 "]" => Species.get_structures rhs lhs
