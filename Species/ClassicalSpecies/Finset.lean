import Init.Control.Lawful.Basic
import Init.Data.List.Perm
import Init.Data.List.Find
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.List.Permutation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Order.Defs.LinearOrder
import Basic

-- Finset
instance : @Species Finset where
  structures := fun ls => {ls}
  transport := by
    intro U V σ σ_bij fu
    have ⟨inj, surj⟩ := σ_bij
    have σ_emb : U ↪ V := by
      apply Function.Embedding.mk
      apply inj
    apply (Finset.map σ_emb fu)
  transport_trans := by
    intro U V W σ σ_bij τ τ_bij fu
    unfold Function.Bijective.comp
    have ⟨σ_inj, σ_surj⟩ := σ_bij
    have ⟨τ_inj, τ_surj⟩ := τ_bij
    simp; rw [Finset.map_map]; simp
  transport_id := by
    intro U fu
    unfold Function.bijective_id; simp
