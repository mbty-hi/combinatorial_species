import Species.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Dedup

structure FinStrictLinOrder (U: Type) where
  order: List U
  order_Nodup: order.Nodup

lemma permutations_preserves_nodup {α: Type} {l: List α}:
  l.Nodup → ∀l' ∈ l.permutations, l'.Nodup
:= fun lnd l' l'_in_lp =>
  let lpl' : l.Perm l' := (l'.mem_permutations.1 l'_in_lp).symm
  lnd.perm lpl'

def transport_FinStrictLinOrder {U V: Type} (F: FinStrictLinOrder U) (σ: U ≃ V)
: FinStrictLinOrder V := {
  order       := F.order.map σ
  order_Nodup := F.order_Nodup.map σ.injective
}

/- TODO workaround noncomputability -/
noncomputable instance LinearOrderSpecies: @Species FinStrictLinOrder where
  structures := fun labels =>
    let perms := labels.toList.permutations
    let perms_Nodup_internal : ∀p ∈ perms, p.Nodup :=
      permutations_preserves_nodup labels.nodup_toList
    let perms_Nodup_external : perms.Nodup := by
      apply List.nodup_permutations; apply labels.nodup_toList
    let perms_ls : List (FinStrictLinOrder _) :=
      List.pmap
        (fun x xinp => FinStrictLinOrder.mk x (perms_Nodup_internal x xinp))
        perms (fun _ is_in => is_in)
    let perms_ls_Nodup : perms_ls.Nodup := by
      apply List.Nodup.pmap
      . intro m n x y eq; simp at eq; subst eq; rfl
      . apply perms_Nodup_external
    ⟨perms_ls, perms_ls_Nodup⟩
  transport       := fun σ s => transport_FinStrictLinOrder s σ
  transport_trans := by simp [transport_FinStrictLinOrder]
  transport_id    := by simp [transport_FinStrictLinOrder]
