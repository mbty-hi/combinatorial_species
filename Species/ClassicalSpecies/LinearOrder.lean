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
  ∀ {α: Type} {l: List α},
  l.Nodup → ∀l' ∈ l.permutations, l'.Nodup
:= by
  intro α l lnd
  induction l with
  | nil => simp
  | cons h t =>
    intro l' l'inp
    apply List.mem_permutations.1 at l'inp
    apply List.Nodup.perm lnd (List.Perm.symm l'inp)

def Nodup_List_to_Finset {α: Type} (l: List α) (lnd: l.Nodup) : Finset α := {
  val := Multiset.ofList l,
  nodup := lnd
}

/- TODO workaround noncomputability -/
/- instance : @Species FinStrictLinOrder where -/
/-   structures := fun labels => -/
/-     let ls_list := Finset.toList labels -/
/-     let ls_list_Nodup : ls_list.Nodup := by { -/
/-       unfold ls_list; apply Finset.nodup_toList -/
/-     } -/
/-     let perms := ls_list.permutations -/
/-     let perms_Nodup_internal : ∀p ∈ perms, p.Nodup := permutations_preserves_nodup (ls_list_Nodup) -/
/-     let perms_Nodup_external : perms.Nodup := by -/
/-       unfold perms; apply List.nodup_permutations; assumption -/
/-     let perms_ls : List (FinStrictLinOrder _) := -/
/-       dependent_map perms (fun x xinp => FinStrictLinOrder.mk x (perms_Nodup_internal x xinp)) -/
/-     let perms_ls_Nodup : perms_ls.Nodup := by -/
/-         unfold perms_ls -/
/-         unfold List.Nodup -/
/-     Nodup_List_to_Finset perms_ls perms_ls_Nodup -/
/-   transport := by -/
/-     intro U V σ σ_bij fu -/
/-     sorry -/
/-     /1- apply (Set.image σ fu) -1/ -/
/-   transport_trans := by -/
/-     intro U V W σ σ_bij τ τ_bij f -/
/-     simp -/
/-     /1- rw [Set.image_image] -1/ -/
/-   transport_id := by simp; sorry -/
