import Init.Control.Lawful.Basic
import Init.Data.List.Perm
import Init.Data.List.Find
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.List.Permutation
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Order.Defs.LinearOrder
import Species.Basic
import Species.Utils.DependentFunctional

-- Linear orders
structure FinStrictLinOrder (U: Type) where
  order: List U
  order_Nodup: List.Nodup order

lemma permutations_preserves_nodup:
  ∀ (A: Type) (l: List A),
  l.Nodup → ∀l' ∈ l.permutations, l'.Nodup
:= by
  intro A l lnd
  induction l with
  | nil => simp
  | cons h t =>
    intro l' l'inp
    apply List.mem_permutations.1 at l'inp
    apply List.Nodup.perm lnd (List.Perm.symm l'inp)

instance : @Species FinStrictLinOrder where
  structures := fun labels =>
    let ls_list := Finset.toList labels
    let ls_list_Nodup : ls_list.Nodup := by {
      unfold ls_list; apply Finset.nodup_toList
    }
    let perms := ls_list.permutations
    let perms_Nodup : ∀p ∈ perms, p.Nodup := apply permutations_preserves_nodup (ls_list_Nodup)
    let perms_ls : List FinStrictLinOrder :=
      dependent_map (fun x xinp → (x, perms_Nodup xinp)) perms
    {List.map
      (fun (x, y) => { order := x; order_Nodup := y })
      perms_ls}
  /- transport := by -/
  /-   intro U V σ σ_bij fu -/
  /-   apply (Set.image σ fu) -/
/-   transport_trans := by -/
/-     intro U V W σ σ_bij τ τ_bij f -/
/-     simp; rw [Set.image_image] -/
/-   transport_id := by simp -/
