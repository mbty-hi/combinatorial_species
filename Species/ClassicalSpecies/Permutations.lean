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
import Species.Basic
import Species.Utils.DependentFunctional

-- Permutations
-- TODO generate from Mathlib's definition of a permutation
structure Permutation (U: Type) where
  f: U → U
  f_bij: f.Bijective

def build_function_from_mappings {U: Type} [DecidableEq U] (mappings: List (U×U)) : U → U :=
  match mappings with
  | [] => id
  | (h_from, h_to)::t => (fun x => if x = h_from then h_to else build_function_from_mappings t x)

@[simp] lemma build_function_from_mappings_nil {U: Type} [DecidableEq U]:
  @build_function_from_mappings U _ [] = id
:= by
  simp [build_function_from_mappings]

@[simp] lemma build_function_from_mappings_cons {U: Type} [DecidableEq U]:
  ∀h_from h_to (t: List (U×U)),
  build_function_from_mappings ((h_from, h_to)::t)
  = (fun x => if x = h_from then h_to else build_function_from_mappings t x)
:= by
  simp [build_function_from_mappings]

lemma build_function_from_mappings_applied_to_out {U: Type} [DecidableEq U]:
  ∀x_from (l: List (U×U)),
  (∀y, y ∈ l → y.fst ≠ x_from)
  → (build_function_from_mappings l) x_from = x_from
:= by
  intros x_from l
  induction l with
  | nil => simp
  | cons h t ih =>
    intros nin; obtain ⟨h_from, h_to⟩ := h; simp
    have neq : h_from ≠ x_from := by specialize nin (h_from, h_to); apply nin; simp
    rw [if_neg]
    . apply ih; intros y y_in_t; apply nin; simp; right; assumption
    . lia

def gen_mappings? {U: Type} [DecidableEq U] (l_from l_to: List U) : Option (List (U × U)) :=
  match l_from, l_to with
  | [], [] => some []
  | h::t, h'::t' =>
    match gen_mappings? t t' with
    | none => none
    | some x => some ((h, h')::x)
  | _, _ => none

lemma gen_mappings?_if_same_length {U: Type} [DecidableEq U] {l₁ l₂: List U}:
  l₁.length = l₂.length
  → (gen_mappings? l₁ l₂).isSome = true
:= by
  revert l₂
  induction l₁ with
  | nil =>
    simp; intros l₂ length_l₂; symm at length_l₂; apply List.eq_nil_of_length_eq_zero at length_l₂
    subst l₂; simp [gen_mappings?]
  | cons h t ih =>
    simp; intros l₂ length_l₂; symm at length_l₂;
    have length_l₂': l₂.length = t.length + 1 := by assumption
    apply List.exists_cons_of_length_eq_add_one at length_l₂
    obtain ⟨h', hh'⟩:= length_l₂
    obtain ⟨t', ht'⟩:= hh'
    subst l₂; simp at *; symm at length_l₂'
    simp [gen_mappings?]
    specialize ih length_l₂'
    rw [Option.isSome_iff_exists] at ih; obtain ⟨x, xh⟩ := ih; simp [xh]

lemma gen_mappings?_only_if_same_length {U: Type} [DecidableEq U] (l₁ l₂: List U):
  (gen_mappings? l₁ l₂).isSome = true
  → l₁.length = l₂.length
:= by
  revert l₂
  induction l₁ with
  | nil =>
    simp; intros l₂ l₂_some
    match l₂ with
    | List.nil => simp
    | List.cons h t => simp [gen_mappings?] at l₂_some
  | cons h t ih =>
    simp; intros l₂ l₂_some
    match l₂ with
    | List.nil => simp [gen_mappings?] at l₂_some
    | List.cons h' t' =>
      simp [gen_mappings?] at *
      specialize ih t'
      generalize mh : gen_mappings? t t' = m
      rw [mh] at l₂_some
      match m with
      | none => simp at *
      | some x =>
        simp at *; have h : (gen_mappings? t t').isSome = true := by rw [mh]; simp
        apply ih h

lemma gen_mappings?_is_some_for_perms {U: Type} [DecidableEq U] {l_from l_to: List U}:
  l_from.Perm l_to
  → (gen_mappings? l_from l_to).isSome = true
:= by
  intros is_prem
  apply List.Perm.length_eq at is_prem
  apply gen_mappings?_if_same_length; assumption

def build_function_from_pair_of_lists? {U: Type} [DecidableEq U] (l_from l_to: List U)
: Option (U → U) :=
  match gen_mappings? l_from l_to with
  | none => none
  | some x => build_function_from_mappings x

lemma build_function_from_pair_of_lists?_nin_l_from_is_id
  {U: Type} [DecidableEq U] {l_from l_to: List U}
  : ∀h f, h ∉ l_from
  → build_function_from_pair_of_lists? l_from l_to = some f
  → f h = h
:= by
  intros x f x_nin_lf bs
  simp [build_function_from_pair_of_lists?] at *
  generalize ho : gen_mappings? l_from l_to = o
  match o with
  | .none => simp [ho] at bs
  | .some y =>
    simp [ho] at bs
    have lengths := gen_mappings?_only_if_same_length _ _ (Option.isSome_of_eq_some ho)
    revert l_to y f
    clear o
    induction l_from with
    | nil =>
      intros l_to f y ho bs lengths
      have foo := build_function_from_mappings_applied_to_out x y; rw [← bs]; apply foo; intros z a
      simp at *; symm at lengths; apply List.eq_nil_of_length_eq_zero at lengths; subst l_to
      simp [gen_mappings?] at *; subst y; contradiction
    | cons h t ih =>
      intros l_to f y ho bs lengths
      match l_to with
      | .nil => contradiction
      | .cons h' t' =>
        simp at *
        obtain ⟨x_neq_h, x_nin_t⟩ := x_nin_lf
        simp [gen_mappings?] at ho
        generalize hp : gen_mappings? t t' = p
        match p with
        | .none => simp [hp] at ho
        | .some e =>
          simp [hp] at ho
          specialize @ih x_nin_t t' e hp lengths
          subst y; simp [build_function_from_mappings] at bs; lia

lemma build_function_from_pair_of_lists?_in_l_from_impl_image_in_l_to
  {U: Type} [DecidableEq U] {l_from l_to: List U}
  : ∀x f, x ∈ l_from
  → build_function_from_pair_of_lists? l_from l_to = some f
  → ∃k, k ∈ l_to ∧ f x = k
:= by
  intros x f x_in bfpl_some
  simp [build_function_from_pair_of_lists?] at *
  generalize ho : gen_mappings? l_from l_to = o
  match o with
  | .none => simp [ho] at bfpl_some
  | .some y =>
    clear o
    simp [ho] at bfpl_some
    have lengths := gen_mappings?_only_if_same_length _ _ (Option.isSome_of_eq_some ho)
    revert l_from y f
    induction l_to with
    | nil =>
      intros l_from f x_in y bfm ho lengths
      simp at lengths; subst l_from; contradiction
    | cons h t ih =>
      intros l_from f x_in y bfm ho lengths
      match l_from with
      | .nil => contradiction
      | .cons h' t' =>
        simp [gen_mappings?] at *
        generalize ho' : gen_mappings? t' t = o'
        match o' with
        | .none => simp [ho'] at bfm
        | .some z =>
          simp [ho'] at bfm; subst y; simp [build_function_from_mappings] at ho
          obtain x_eq | x_in := x_in
          . left; subst x f; simp
          . subst f; simp
            specialize ih (build_function_from_mappings z) x_in z ho'
            simp at ih; specialize ih lengths
            generalize d : (Decidable.decide (x = h)) = b
            lia

lemma build_function_from_pair_of_lists?_is_some_for_same_length
  {U: Type} [DecidableEq U] {l_from l_to: List U}
: l_from.length = l_to.length
  → (build_function_from_pair_of_lists? l_from l_to).isSome = true
:= by
  intros same_length
  unfold build_function_from_pair_of_lists?
  have h : (gen_mappings? l_from l_to).isSome = true := by
    apply gen_mappings?_if_same_length same_length
  rw [Option.isSome_iff_exists] at h; obtain ⟨x, xh⟩ := h; simp [xh]

lemma build_function_from_pair_of_lists?_is_some_for_perms
  {U: Type} [DecidableEq U] {l_from l_to: List U}
: l_from.Perm l_to
  → (build_function_from_pair_of_lists? l_from l_to).isSome = true
:= by
  intros is_perm
  unfold build_function_from_pair_of_lists?
  have h : (gen_mappings? l_from l_to).isSome = true := by
    apply gen_mappings?_is_some_for_perms is_perm
  rw [Option.isSome_iff_exists] at h; obtain ⟨x, xh⟩ := h; simp [xh]

def build_function_from_perm {U: Type} [DecidableEq U]
  (l_from l_to: List U) (perm: l_from.Perm l_to)
: (U → U) := by
  generalize h : build_function_from_pair_of_lists? l_from l_to = o
  match o with
  | .none =>
    have h' : (build_function_from_pair_of_lists? l_from l_to).isSome = true := by
      apply build_function_from_pair_of_lists?_is_some_for_perms perm
    rw [h] at h'; simp at h'
  | .some x => apply x

lemma build_function_from_pair_of_lists?_perm_same_index {U: Type} [DecidableEq U]
  {l₁ l₂: List U} (l₁_nd: l₁.Nodup) (lengths: l₁.length = l₂.length) (f: U → U)
: build_function_from_pair_of_lists? l₁ l₂ = some f
  → ∀x, (p₁: x < l₁.length) → (p₂: x < l₂.length)
  → f (l₁[x]'p₁) = (l₂[x]'p₂)
:= by
  intros a x p₁ p₂
  revert l₂ f x
  induction l₁ with
  | nil =>
    intros l₂ lengths f a x p₁ p₂
    simp at p₁
  | cons h t ih =>
    intros l₂ lengths f a x p₁ p₂
    match l₂ with
    | .nil => simp at p₂
    | .cons h' t' =>
      simp at *
      obtain ⟨h_nin, t_nd⟩ := l₁_nd
      specialize @ih t_nd t'
      simp [build_function_from_pair_of_lists?, gen_mappings?] at a
      generalize hgm : gen_mappings? t t' = gm
      match gm with
      | .none => simp [hgm] at a
      | .some m =>
        simp [hgm] at a
        simp [build_function_from_pair_of_lists?, hgm] at ih
        match x with
        | .zero => subst f; simp
        | .succ x' =>
          subst f; simp
          simp [List.length] at p₁
          simp [List.length] at p₂
          have foo : t[x']'p₁ ≠ h := by
            have tmp : t[x']'p₁ ∈ t := by apply List.getElem_mem p₁
            lia
          simp [foo]
          specialize ih lengths x' p₁ p₂
          assumption

-- Will be in the standard library from next version on (4.29) TODO remove then
theorem idxOf?_eq_some_iff {α} [BEq α] [LawfulBEq α] {l : List α} {a : α} {i : Nat} :
  l.idxOf? a = some i ↔ ∃ (h : i < l.length), l[i] = a ∧ ∀ j (_ : j < i), ¬l[j] = a := by
  simp [List.idxOf?, List.findIdx?_eq_some_iff_getElem]

-- Constructive
theorem idxOf?_eq_some_constructive {α} [BEq α] [LawfulBEq α] {l : List α} {a : α} {i : Nat}
: l.idxOf? a = some i → (ll: i < l.length) → l[i]'ll = a := by
  intros is_some length_ok
  simp [List.idxOf?] at is_some
  apply List.of_findIdx?_eq_some at is_some
  generalize himg : l[i]? = img
  match img with
  | .none => simp [himg] at is_some
  | .some img => simp [himg] at is_some; apply (List.getElem_eq_iff length_ok).2 at himg; lia

def build_function_from_pair_of_lists_Bijective_for_nodup_perms
  {U: Type} [DecidableEq U] {l_from l_to: List U} (nodup: l_from.Nodup) (perm: l_from.Perm l_to)
  {f: U → U} (P: (build_function_from_pair_of_lists? l_from l_to) = some f)
: f.Bijective := by
    have lengths : l_from.length = l_to.length := by apply List.Perm.length_eq at perm; lia
    have bfpl := build_function_from_pair_of_lists?_perm_same_index nodup lengths f P
    unfold Function.Bijective
    constructor
    . unfold Function.Injective; intros a₁ a₂ img_eq
      generalize hidx₁: l_from.idxOf? a₁ = idx₁
      generalize hidx₂: l_from.idxOf? a₂ = idx₂
      match idx₁ with
      | .none =>
        have is_none₁ := Option.isNone_iff_eq_none.2 hidx₁
        rw [List.isNone_idxOf?] at is_none₁
        rw [build_function_from_pair_of_lists?_nin_l_from_is_id a₁ f is_none₁ P] at img_eq
        match idx₂ with
        | .none =>
          have is_none₂ := Option.isNone_iff_eq_none.2 hidx₂
          rw [List.isNone_idxOf?] at is_none₂
          rw [build_function_from_pair_of_lists?_nin_l_from_is_id a₂ f is_none₂ P] at img_eq
          assumption
        | .some idx₂ =>
          exfalso -- contradiction: `f a₂` is in `l_to` but `f a₁` isn't
          have not_in_l_to₁ : a₁ ∉ l_to := by
            intros x; apply List.Perm.mem_iff at perm; apply perm.2 at x; lia
          have is_some₂ := Option.isSome_of_eq_some hidx₂
          apply List.isSome_idxOf?.1 at is_some₂
          have lok₂a: idx₂ < l_from.length := by apply idxOf?_eq_some_iff.1 at hidx₂; lia
          have lok₂b: idx₂ < l_to.length := by lia
          have p₂: a₂ = l_from[idx₂] := by apply idxOf?_eq_some_iff.1 at hidx₂; lia
          specialize bfpl idx₂ lok₂a lok₂b
          subst a₂; rw [bfpl] at img_eq; subst a₁
          simp at not_in_l_to₁
      | .some idx₁ =>
        match idx₂ with
        | .none =>
          exfalso -- contradiction: `f a₁` is in `l_to` but `f a₂` isn't
          have is_none₂ := Option.isNone_iff_eq_none.2 hidx₂
          rw [List.isNone_idxOf?] at is_none₂
          rw [build_function_from_pair_of_lists?_nin_l_from_is_id a₂ f is_none₂ P] at img_eq
          have not_in_l_to₂ : a₂ ∉ l_to := by
            intros x; apply List.Perm.mem_iff at perm; apply perm.2 at x; lia
          have lok₁a: idx₁ < l_from.length := by apply idxOf?_eq_some_iff.1 at hidx₁; lia
          have lok₁b: idx₁ < l_to.length   := by lia
          have p₁: a₁ = l_from[idx₁] := by apply idxOf?_eq_some_iff.1 at hidx₁; lia
          specialize bfpl idx₁ lok₁a lok₁b
          subst a₁; rw [bfpl] at img_eq; subst a₂
          simp at not_in_l_to₂
        | .some idx₂ =>
          have is_some₁ := Option.isSome_of_eq_some hidx₁
          apply List.isSome_idxOf?.1 at is_some₁
          have lok₁a: idx₁ < l_from.length := by apply idxOf?_eq_some_iff.1 at hidx₁; lia
          have lok₁b: idx₁ < l_to.length := by lia
          have p₁: a₁ = l_from[idx₁] := by apply idxOf?_eq_some_iff.1 at hidx₁; lia
          have bfpl₁ := bfpl idx₁ lok₁a lok₁b
          have is_some₂ := Option.isSome_of_eq_some hidx₂
          apply List.isSome_idxOf?.1 at is_some₂
          have lok₂a: idx₂ < l_from.length := by apply idxOf?_eq_some_iff.1 at hidx₂; lia
          have lok₂b: idx₂ < l_to.length   := by lia
          have p₂: a₂ = l_from[idx₂] := by apply idxOf?_eq_some_iff.1 at hidx₂; lia
          have bfpl₂ := bfpl idx₂ lok₂a lok₂b
          subst a₁ a₂; rw [bfpl₁, bfpl₂] at img_eq
          have l_to_nodup: l_to.Nodup := by
            apply List.Nodup.perm nodup perm
          have tmp: idx₁ = idx₂ := by
            apply List.Nodup.getElem_inj_iff at l_to_nodup
            apply l_to_nodup.1; assumption
          lia
    . unfold Function.Surjective
      intros b
      generalize hidx: l_to.idxOf? b = idx
      match idx with
      | .none =>
        exists b
        apply List.idxOf?_eq_none_iff.1 at hidx
        have not_in_l_from : b ∉ l_from := by
          intros x; apply List.Perm.mem_iff at perm; apply perm.1 at x; lia
        simp [build_function_from_pair_of_lists?_nin_l_from_is_id b f not_in_l_from P]
      | .some idx =>
        have lok_from: idx < l_from.length := by apply idxOf?_eq_some_iff.1 at hidx; lia
        have lok_to  : idx < l_to.length   := by lia
        exists l_from[idx]
        specialize bfpl idx lok_from lok_to; rw [bfpl]
        apply idxOf?_eq_some_constructive hidx

def nodup_perm_lists_to_Permutation {U: Type} [DecidableEq U]
  (l_from l_to: List U) (nd: l_from.Nodup) (perm: l_from.Perm l_to)
: Permutation U := by
  have r := build_function_from_pair_of_lists?_is_some_for_perms perm
  generalize h : build_function_from_pair_of_lists? l_from l_to = o
  match o with
  | .none =>
    have h' : (build_function_from_pair_of_lists? l_from l_to).isSome = true := by
      apply build_function_from_pair_of_lists?_is_some_for_perms perm
    rw [h] at h'; simp at h'
  | .some perm_f =>
    have f_bij := build_function_from_pair_of_lists_Bijective_for_nodup_perms nd perm h
    constructor; apply f_bij

lemma nodup_perm_lists_to_inj_on_l_to
  {U: Type} [DecidableEq U] {l_from l_to₁ l_to₂: List U}
  (nd: l_from.Nodup) (perm₁: l_from.Perm l_to₁) (perm₂: l_from.Perm l_to₂)
: l_to₁ ≠ l_to₂
  → nodup_perm_lists_to_Permutation l_from l_to₁ nd perm₁
    ≠ nodup_perm_lists_to_Permutation l_from l_to₂ nd perm₂
:= by
  intros neq
  /- TODO We can always point to an index that changed... -/
  sorry

instance : @Species Permutation where
  structures :=
    fun labels =>
      let ls := labels.toList
      have ls_nd : ls.Nodup := by apply labels.nodup_toList
      let ps := ls.permutations
      have p_in_ps_is_ls_perm : ∀p, p ∈ ps → ls.Perm p := by
        intros p p_in_ps; subst ps; symm; apply List.perm_of_mem_permutations; assumption
      let ls_fcts :=
        dependent_map
           ps
           (fun p p_in_ps =>
             have ls_perm_p : ls.Perm p := by apply (p_in_ps_is_ls_perm p p_in_ps)
             nodup_perm_lists_to_Permutation ls p ls_nd ls_perm_p
           )
      have ls_fcts_nodup : ls_fcts.Nodup := by
        subst ls_fcts
      ({
        val := Multiset.ofList ls_fcts,
        nodup := ls_fcts_nodup,
      } : Finset _)
  transport := by sorry
  transport_trans := by sorry
  transport_id := by sorry
