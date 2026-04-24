import Init.Data.List.Perm
import Init.Data.List.Find
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.List.Permutation
import Mathlib.Data.Set.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Order.Defs.LinearOrder
import Species.Basic

-- Set
instance SetSpecies: @Species Set where
  structures := fun ls => {↑ls}
  transport := by
    intro U V σ σ_bij fu
    apply (Set.image σ fu)
  transport_trans := by
    intro U V W σ σ_bij τ τ_bij f
    simp; rw [Set.image_image]
  transport_id := by simp
