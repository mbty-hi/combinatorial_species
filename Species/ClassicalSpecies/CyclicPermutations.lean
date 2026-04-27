import Mathlib.Data.List.Permutation
import Species.Basic

/- The head of the ref_list is always the (implicit) first (or last, depending on how you view
   things) element in `data` (our explicit cycle list): this is how we avoid cyclical redundancy
   issues. -/
structure CyclicPermutation (U: Type) where
  data: List U
  ref_list: List U
  ref_list_nd: ref_list.Nodup
  is_cyclic_permutation: data.Perm ref_list.tail

def make_cyclic_permutations {U: Type} (labels: List U) (labels_nd: labels.Nodup)
: List (CyclicPermutation U) :=
  let tail_perms := labels.tail.permutations
  have p_in_tail_perms_is_perm_of_labels_tail : ∀p, p ∈ tail_perms → labels.tail.Perm p := by
    intros p p_in_tail_perms; subst tail_perms; symm; apply List.perm_of_mem_permutations
    apply p_in_tail_perms
  List.pmap
    (fun (p: List U) p_in_ps =>
      have p_perm_labels : p.Perm labels.tail := by
        apply List.Perm.symm; apply (p_in_tail_perms_is_perm_of_labels_tail p p_in_ps)
      {
        data := p,
        ref_list := labels,
        ref_list_nd := labels_nd,
        is_cyclic_permutation := p_perm_labels,
      }
    )
    tail_perms
    (fun _ is_in => is_in)

lemma make_cyclic_permutations_nodup {U: Type}:
  ∀(labels: List U) (labels_nd: labels.Nodup),
  (make_cyclic_permutations labels labels_nd).Nodup
:= by
  intros labels labels_nd
  induction labels with
  | nil => simp [make_cyclic_permutations]
  | cons h t ih =>
    have t_nd : t.Nodup := List.Nodup.of_cons labels_nd
    specialize ih t_nd
    simp [make_cyclic_permutations] at *
    apply List.Nodup.pmap
    . intros p p_in_t_permutations p' p'_in_t_permutations eq; cases eq; rfl
    . apply (List.nodup_permutations _ t_nd)

noncomputable instance CyclicPermutationSpecies: @Species CyclicPermutation where
  structures :=
    fun labels =>
      let ls := labels.toList
      have ls_nd : ls.Nodup := by apply labels.nodup_toList
      let cyclic_permutations := make_cyclic_permutations ls ls_nd
      have cyclic_permutations_nd: cyclic_permutations.Nodup := by
        apply make_cyclic_permutations_nodup
      ({
        val := Multiset.ofList cyclic_permutations,
        nodup := cyclic_permutations_nd,
      } : Finset _)
  transport := by
    intros U V σ bij pu
    constructor; rotate_left; rotate_left
    . apply List.map σ pu.data
    . apply List.map σ pu.ref_list
    . apply List.Nodup.map bij.1 pu.ref_list_nd
    . rw [← List.map_tail]; apply List.Perm.map; apply pu.is_cyclic_permutation
  transport_trans := by simp
  transport_id := by simp
