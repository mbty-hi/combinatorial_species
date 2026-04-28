import Species.Basic

structure Permutation (U: Type) where
  l_from: List U
  l_to: List U
  perm: l_from.Perm l_to
  nodup: l_from.Nodup

def nodup_perm_lists_to_Permutation {U: Type} [DecidableEq U]
  (l_from l_to: List U) (perm: l_from.Perm l_to) (nd: l_from.Nodup)
: Permutation U :=
  { l_from := l_from,
    l_to   := l_to,
    perm   := perm,
    nodup  := nd,
  }

noncomputable instance PermutationSpecies: @Species Permutation where
  structures :=
    fun labels =>
      let ls := labels.toList
      have ls_nd : ls.Nodup := by apply labels.nodup_toList
      let ps := ls.permutations
      have p_in_ps_is_ls_perm : ∀p, p ∈ ps → ls.Perm p := by
        intros p p_in_ps; subst ps; symm; apply List.perm_of_mem_permutations; assumption
      have ps_nd : ps.Nodup := by apply List.nodup_permutations; assumption
      let ls_fcts :=
        List.pmap
           (fun p p_in_ps =>
             have ls_perm_p : ls.Perm p := by apply (p_in_ps_is_ls_perm p p_in_ps)
             nodup_perm_lists_to_Permutation ls p ls_perm_p ls_nd
           )
           ps (fun _ is_in => is_in)
      have ls_fcts_nodup : ls_fcts.Nodup := by
        subst ls_fcts
        apply List.Nodup.pmap
        . intros l₁ l₁in l₂ l₂in eq; simp [nodup_perm_lists_to_Permutation] at eq; lia
        . apply ps_nd
      ({
        val := Multiset.ofList ls_fcts,
        nodup := ls_fcts_nodup,
      } : Finset _)
  transport := by
    intros U V σ bij pu
    constructor; rotate_left; rotate_left
    . apply List.map σ pu.l_from
    . apply List.map σ pu.l_to
    . apply List.Perm.map; apply pu.perm
    . apply List.Nodup.map bij.1 pu.nodup
  transport_trans := by simp
  transport_id := by simp
