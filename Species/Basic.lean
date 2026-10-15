module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.GroupTheory.Perm.Basic

/-!
# Combinatorial species

This file defines combinatorial species and some of their properties.

## Important definitions
* `Species` : the class of species, following the combinatorial definition of [BLL]

## Implementation notes
We use finite types instead of [BLL]'s finite sets for labels. This has no bearing on the
expressivity of the theory, but it makes the proofs nicer.

## References
* [F. Bergeron, G. Labelle, P. Leroux, *Combinatorial Species and Tree-like Structures*][BLL]
TODO add .bib
-/

@[expose] public section

/-- A combinatorial species is a rule (`F` of type `Type → Type`) that associates to each finite
type of labels (`U`) a finite type `F[U]`, independently of the nature of the elements of `U`. -/
class Species (F : Type → Type) where
  /-- For any finite type of labels `U`, the number of `F`-structures on `U` is finite. -/
  finite : {U : Type} → [Finite U] → Finite (F U)
  /-- Updating the labels of an `F`-structure according to a bijection between label types. -/
  transport : {U V : Type} → [Finite U] → [Finite V] → (U ≃ V) → F U → F V
  /-- Functoriality law. -/
  id_transport : ∀ {U} [Finite U] (f : F U), transport (Equiv.refl U) f = f
  /-- Functoriality law. -/
  comp_transport :
    ∀ {U V W} [Finite U] [Finite V] [Finite W] (σ : U ≃ V) (τ : V ≃ W) (f : F U),
    transport (σ.trans τ) f = transport τ (transport σ f)

namespace Species

variable {F : Type → Type} [Species F] {U V W : Type} [Finite U] [Finite V] [Finite W]

/-- For any `Finite U`, there is a finite number of `F`-structures labelled with `U`. -/
instance instFinite : Finite (F U) := finite

/-- Relabelling is an action of `Equiv.Perm U` on `F U` (with `σ • f` defined as `transport σ f`).
Its orbits are the isomorphism types (unlabelled structures) of `F`-structures on `U`. -/
instance instMulAction : MulAction (Equiv.Perm U) (F U) where
  smul σ f       := transport σ f
  one_smul       := id_transport
  mul_smul σ τ f := comp_transport τ σ f

section transport

/-- Transport bundled as an equivalence. Useful for interacting with Mathlib machinery. -/
def transportEquiv (σ : U ≃ V) : F U ≃ F V where
  toFun       := transport σ
  invFun      := transport σ.symm
  left_inv  f := by rw [← comp_transport, Equiv.self_trans_symm, id_transport]
  right_inv f := by rw [← comp_transport, Equiv.symm_trans_self, id_transport]

theorem transportEquiv_symm (σ : U ≃ V)
: (transportEquiv (F := F) σ.symm) = (transportEquiv (F := F) σ).symm
:= Equiv.ext (fun _ => rfl)

theorem transport_transport (σ : U ≃ V) (τ : V ≃ W) (f : F U)
: transport τ (transport σ f) = transport (σ.trans τ) f :=
  (comp_transport (F := F) σ τ f).symm

theorem transport_eq_self_of_id (σ : U ≃ U) (h : ∀ a, σ a = a) (f : F U)
: transport σ f = f := by
  have hσ : σ = Equiv.refl U := Equiv.ext h
  rw [hσ, id_transport]

end transport
end Species
end
