import Species.Basic

/- The head of the ref_list is always the (implicit) first (or last, depending on how you view
   things) element in `data` (our explicit cycle list): this is how we avoid cyclical redundancy
   issues. -/
structure CyclicPermutation (U: Type) where
  data: List U
  ref_list: List U
  ref_list_nd: ref_list.Nodup
  is_cyclic_permutation: data.Perm ref_list.tail

def make_cyclic_permutations {U: Type} {labels: List U} (labels_nd: labels.Nodup)
: List (CyclicPermutation U) :=
  List.pmap
    (fun p p_in_ps =>
      {
        data := p,
        ref_list := labels,
        ref_list_nd := labels_nd,
        is_cyclic_permutation := List.perm_of_mem_permutations p_in_ps
      }
    )
    labels.tail.permutations
    (fun _ is_in => is_in)

lemma make_cyclic_permutations_nodup {U: Type} {labels: List U} (labels_nd: labels.Nodup):
  (make_cyclic_permutations labels_nd).Nodup
:=
  List.Nodup.pmap
    (fun _ _ _ _ eq => by cases eq; rfl)
    (List.nodup_permutations _ (labels_nd.sublist labels.tail_sublist))

noncomputable instance CyclicPermutationSpecies: @Species CyclicPermutation where
  structures :=
    fun labels =>
      { val   := Multiset.ofList (make_cyclic_permutations labels.nodup_toList),
        nodup := make_cyclic_permutations_nodup _ }
  transport := fun bij pu =>
    ⟨pu.data.map _, pu.ref_list.map _, pu.ref_list_nd.map bij.1,
     by rw [← List.map_tail]; exact pu.is_cyclic_permutation.map _⟩
  transport_trans := by simp
  transport_id    := by simp
