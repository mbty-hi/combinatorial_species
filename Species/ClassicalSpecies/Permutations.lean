import Species.Basic
import Mathlib.Data.List.Permutation

structure Permutation (U: Type) where
  l_from: List U
  l_to: List U
  perm: l_from.Perm l_to
  nodup: l_from.Nodup

def nodup_perm_lists_to_Permutation {U: Type} [DecidableEq U]
  (l_from l_to: List U) (perm: l_from.Perm l_to) (nd: l_from.Nodup)
: Permutation U := {
  l_from := l_from,
  l_to   := l_to,
  perm   := perm,
  nodup  := nd,
}

noncomputable instance PermutationSpecies: @Species Permutation where
  structures :=
    fun labels =>
      have ls_nd := labels.nodup_toList
      have ps_nd := List.nodup_permutations _ ls_nd
      { val :=
          List.pmap
             (fun p p_in_ps =>
               have ls_perm_p := (p.perm_of_mem_permutations p_in_ps).symm
               nodup_perm_lists_to_Permutation labels.toList p ls_perm_p ls_nd
             )
             labels.toList.permutations (fun _ is_in => is_in),
        nodup := by
          apply List.Nodup.pmap _ ps_nd
          intros _ _ _ _ _; simp [nodup_perm_lists_to_Permutation] at *; assumption
      }
  transport := fun σ s => ⟨s.l_from.map σ, s.l_to.map σ, s.perm.map σ.1, s.nodup.map σ.injective⟩
  transport_trans := by simp
  transport_id    := by simp
