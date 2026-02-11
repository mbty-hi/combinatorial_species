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

@[simp]
lemma build_function_from_mappings_nil {U: Type} [DecidableEq U]:
  @build_function_from_mappings U _ [] = id
:= by
  simp [build_function_from_mappings]

@[simp]
lemma build_function_from_mappings_cons {U: Type} [DecidableEq U]:
  ∀ h_from h_to (t: List (U×U)),
  build_function_from_mappings ((h_from, h_to)::t)
  = (fun x => if x = h_from then h_to else build_function_from_mappings t x)
:= by
  simp [build_function_from_mappings]

lemma build_function_from_mappings_applied_to_out {U: Type} [DecidableEq U]:
  ∀ x_from (l: List (U×U)),
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

lemma build_function_from_mappings_applied_to_in {U: Type} [DecidableEq U]:
  ∀ x_from (l: List (U×U)) x_to,
  (x_from, x_to) ∈ l
  → (∀z, z ∈ l → z.fst = x_from → z.snd = x_to)
  → (build_function_from_mappings l) x_from = x_to
:= by
  intros x_from l
  induction l with
  | nil => intros x_to x_in_l x_from_unique; contradiction
  | cons h t ih =>
    intros x_to x_in_l x_from_unique
    by_cases h_eq : (h.fst = x_from)
    . simp [build_function_from_mappings];
      rw [if_pos]; apply (x_from_unique h); simp; assumption; lia
    . simp [build_function_from_mappings]
      rw [if_neg]
      . apply ih
        . simp at x_in_l
          obtain x_h | x_in_t := x_in_l; subst h; contradiction; assumption
        . intros z z_in_t z_eq; apply x_from_unique; simp; right; assumption; apply z_eq
      . lia

lemma build_function_from_mappings_nondefault_result_corresponds_to_mapping
  {U: Type} [DecidableEq U]
: ∀ h_from h_to (l: List (U×U)),
  (build_function_from_mappings l) h_from = h_to
  → h_from ≠ h_to
  → (h_from, h_to) ∈ l
:= by
  intro h_from h_to l is_res neq_from_to
  induction l with
  | nil => contradiction
  | cons h t ih =>
    have x : h = (h.1, h.2) := by simp
    rw [x, build_function_from_mappings_cons] at is_res; clear x
    have x_eq := eq_or_ne h_from h.1
    obtain eq | neq := x_eq
    . simp [eq] at is_res; rw [eq, ← is_res]; simp
    . apply List.mem_cons_of_mem
      simp at is_res; rw [if_neg neq] at is_res
      apply ih is_res

lemma build_function_from_mappings_in_not_overridden_ok {U: Type} [DecidableEq U]:
  ∀ h_from h_to (l: List (U×U)),
  (h_from, h_to) ∈ l
  → (∀ h_to', (h_from, h_to') ∈ l → h_to' = h_to)
  → (build_function_from_mappings l) h_from = h_to
:= by
  intro h_from h_to l mapping_in_l mapping_unique
  induction l with
  | nil => contradiction
  | cons h t ih =>
    have x_eq_u := eq_or_ne h.1 h_from
    simp [build_function_from_mappings]
    obtain eq | neq := x_eq_u
    . rw [eq]; simp; apply mapping_unique; rw [← eq]; simp
    . rw [if_neg]
      . apply ih; simp at mapping_in_l
        obtain in_h | in_t := mapping_in_l
        . exfalso; apply neq; rw [← in_h]
        . assumption
        . intro h_to' alt_in_t; apply mapping_unique; simp; right; assumption
      . intro ctr; subst ctr; contradiction


def get_preimage? {U: Type} [BEq U] (l_from l_to: List U) (x: U) : Option U :=
  match l_to.idxOf? x with
  | .none => none
  | .some n =>
    match l_from[n]? with
    | .none => none
    | .some y => some y

lemma get_preimage_succeeds {U: Type} [BEq U]:
  ∀x (l_from l_to: List U) n y,
  l_to.idxOf? x = some n → l_from[n]? = some y
  → ∃r, get_preimage? l_from l_to x = some r
:= by
  intro x l_from l_to n y h_new_index h_replaced_item
  simp [get_preimage?, h_new_index, h_replaced_item]

def get_preimage_dep {U: Type} [BEq U]
  (l_from l_to: List U) (x y: U) (n: ℕ) (_x_idx: l_to.idxOf? x = some n)
  (_l_from_nth: l_from[n]? = some y)
: U :=
  y

lemma get_preimage_permutation {U: Type} [DecidableEq U]:
  ∀(l_from l_to: List U) (_l_from_perm_l_to: l_from.Perm l_to) (x: U) (_x_in_l_from: x ∈ l_from),
  ∃y, get_preimage? l_from l_to x = some y
:= by
  intro l_from l_to ls_perm x xinlf
  have xinlt : x ∈ l_to := by apply ((List.Perm.mem_iff ls_perm).1 xinlf)
  simp [get_preimage?]
  have h := Option.isSome_iff_exists.1 (List.isSome_idxOf?.2 xinlt)
  obtain ⟨n, xn⟩ := h
  simp [xn]
  have ls_len_eq := List.Perm.length_eq ls_perm
  have xn' := List.idxOf_eq_getD_idxOf? x l_to
  rw [xn] at xn'; simp at *; clear xn
  have n_in_range := List.idxOf_lt_length_iff.2 xinlt
  rw [← ls_len_eq] at n_in_range
  rw [xn'] at n_in_range
  apply List.getElem?_eq_getElem at n_in_range; rw [n_in_range]; simp

def gen_mappings_dep {U: Type} [DecidableEq U] (l_from l_to: List U) (ls_perm: l_from.Perm l_to)
: List (U × U) :=
  dependent_map
    l_from
    (fun (x: U) (xinlf: x ∈ l_from) =>
      /- We know that the element comes from l_from, and therefore that it exists in l_to -/
      have xinlt : x ∈ l_to := by apply ((List.Perm.mem_iff ls_perm).1 xinlf)
      have ls_len_eq := List.Perm.length_eq ls_perm
      have n_in_range := List.idxOf_lt_length_iff.2 xinlt
      have xn' := @List.idxOf_eq_getD_idxOf? U instBEqOfDecidableEq x l_to
      /- x is in l_to: we extract its index (we prove that it must exist first) -/
      let idx_in_l_to : ((n: ℕ) ×' @l_to.idxOf? U instBEqOfDecidableEq x = some n) := by
        constructor
        generalize foo : @List.idxOf? U instBEqOfDecidableEq x l_to = u
        rw [foo] at xn'
        match u with
        | .none =>
          simp at *; apply Nat.ne_of_lt at n_in_range
          rw [← xn'] at n_in_range; apply n_in_range; rfl
        | .some c => simp at *; rw [← xn']
      let ⟨idx_in_l_to, idx_in_l_to_proof⟩ := idx_in_l_to
      /- In l_from, there exists an element that has index idx_in_l_to -/
      let l_from_value_at_idx : ((y: U) ×' (l_from[idx_in_l_to]? = some y)) := by
        rw [← ls_len_eq] at n_in_range; simp [idx_in_l_to_proof] at xn'
        rw [xn'] at n_in_range
        apply List.getElem?_eq_getElem at n_in_range; rw [n_in_range]; simp
        constructor; rfl
      let ⟨l_from_value_at_idx, l_from_value_at_idx_proof⟩ := l_from_value_at_idx
      (x,
       @get_preimage_dep
         U instBEqOfDecidableEq
         l_from l_to x l_from_value_at_idx
         idx_in_l_to
         idx_in_l_to_proof l_from_value_at_idx_proof
      )
    )

def gen_mappings? {U: Type} [DecidableEq U] (l_from l_to: List U) : Option (List (U × U)) :=
  match l_from, l_to with
  | [], [] => some []
  | h::t, h'::t' =>
    match gen_mappings? t t' with
    | none => none
    | some x => some ((h, h')::x)
  | _, _ => none

lemma gen_mappings?_self {U: Type} [DecidableEq U] (l: List U):
  (gen_mappings? l l).isSome = true
:= by
  induction l with
  | nil => simp [gen_mappings?]
  | cons h t ih =>
    simp [gen_mappings?]; rw [Option.isSome_iff_exists] at ih; obtain ⟨x, xh⟩ := ih; simp [xh]

lemma gen_mappings?_if_same_length {U: Type} [DecidableEq U] (l₁ l₂: List U):
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
    specialize ih t' length_l₂'
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

lemma gen_mappings?_trans {U: Type} [DecidableEq U] {l₁ l₂ l₃: List U}:
  (gen_mappings? l₁ l₂).isSome = true
  → (gen_mappings? l₂ l₃).isSome = true
  → (gen_mappings? l₁ l₃).isSome = true
:= by
  intros h₁₂ h₂₃
  apply gen_mappings?_only_if_same_length at h₁₂
  apply gen_mappings?_only_if_same_length at h₂₃
  apply gen_mappings?_if_same_length
  trans; assumption; assumption

lemma gen_mappings?_is_some_for_perms {U: Type} [DecidableEq U] {l_from l_to: List U}:
  l_from.Perm l_to
  → (gen_mappings? l_from l_to).isSome = true
:= by
  intros is_prem
  apply List.Perm.length_eq at is_prem
  apply gen_mappings?_if_same_length; assumption

def gen_mappings_from_perm
  {U: Type} [DecidableEq U] {l_from l_to: List U} (perm: l_from.Perm l_to)
: List (U × U) := by
  generalize h : gen_mappings? l_from l_to = o
  match o with
  | .none =>
    have h' : (gen_mappings? l_from l_to).isSome = true := by
      apply gen_mappings?_is_some_for_perms perm
    rw [h] at h'; simp at h'
  | .some x => apply x

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
  sorry

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

lemma build_function_from_pair_of_lists_Bijective_for_nodup_perms
  {U: Type} [DecidableEq U] (l_from l_to: List U) (nodup: l_from.Nodup) (perm: l_from.Perm l_to)
: ∃x, (build_function_from_pair_of_lists? l_from l_to) = some x
  ∧ x.Bijective
:= by
  induction perm with
  | nil =>
    simp [build_function_from_pair_of_lists?, gen_mappings?]
    apply Function.bijective_id
  | @cons h l₁ l₂ perm is_bij =>
    simp [build_function_from_pair_of_lists?, gen_mappings?] at *
    obtain ⟨h_nin_l₁, l₁_nodup⟩ := nodup; specialize is_bij l₁_nodup
    obtain ⟨f, map_is_some, f_bij⟩ := is_bij
    have h' : (gen_mappings? l₁ l₂).isSome = true := by
      apply gen_mappings?_is_some_for_perms perm
    rw [Option.isSome_iff_exists] at h'; obtain ⟨y, yh⟩ := h'
    have gen_ret_some : build_function_from_pair_of_lists? l₁ l₂ = some f := by
      simp [build_function_from_pair_of_lists?]; assumption
    simp [yh]; simp [yh] at map_is_some; rw [map_is_some]
    unfold Function.Bijective at *
    obtain ⟨f_inj, f_surj⟩ := f_bij
    have tmp : f h = h := by
      apply build_function_from_pair_of_lists?_nin_l_from_is_id h f h_nin_l₁ gen_ret_some
    constructor
    . unfold Function.Injective at *
      intros a₁ a₂ h_inj; simp at  *
      generalize d₁ : (Decidable.decide (a₁ = h)) = b₁
      generalize d₂ : (Decidable.decide (a₂ = h)) = b₂
      match b₁, b₂ with
      | true, true => simp at *; lia
      | false, false =>
        repeat rw [ite_cond_eq_false] at h_inj
        . apply f_inj h_inj
        . lia
        . lia
      | true, false =>
        simp at *
        rw [ite_cond_eq_true] at h_inj; rw [ite_cond_eq_false] at h_inj
        . exfalso; rw [← tmp] at h_inj; apply f_inj at h_inj; lia
        . lia
        . lia
      | false, true =>
        simp at *
        rw [ite_cond_eq_false] at h_inj; rw [ite_cond_eq_true] at h_inj
        . exfalso; rw [← tmp] at h_inj; apply f_inj at h_inj; lia
        . lia
        . lia
    . unfold Function.Surjective at *
      intros b; simp at *
      specialize f_surj b; obtain ⟨a , ha⟩ := f_surj
      generalize d : (Decidable.decide (b = h)) = hd
      match hd with
      | true  => exists b; lia
      | false =>
        exists a; rw [ha]; apply ite_cond_eq_false
        have tmp : f h = h := by
          apply build_function_from_pair_of_lists?_nin_l_from_is_id h f h_nin_l₁ gen_ret_some
        lia
  | swap x y l =>

    sorry
  | @trans l₁ l₂ l₃ perm_l₁_l₂ perm_l₂_l₃ some₁₂ some₂₃ => sorry

/-     simp [gen_mappings?] -/
/-     have h := gen_mappings?_self l -/
/-     rw [Option.isSome_iff_exists] at h -/
/-     obtain ⟨x, xh⟩ := h -/
/-     simp  [xh] -/
/-     apply gen_mappings?_trans some₁₂ some₂₃ -/

/- lemma gen_mappings?_ok_for_perm {U: Type} [DecidableEq U] (l_from l_to: List U): -/
/-   l_from.Perm l_to -/
/-   → (gen_mappings? l_from l_to).isSome = true -/
/- := by -/
/-   intros is_prem -/
/-   apply -/
/-   induction is_prem with -/
/-   | nil => simp [gen_mappings?] -/
/-   | @cons h l₁ l₂ perm is_some => -/
/-     simp [gen_mappings?]; rw [Option.isSome_iff_exists] at is_some -/
/-     obtain ⟨x, xh⟩ := is_some -/
/-     simp [xh] -/
/-   | swap x y l => -/
/-     simp [gen_mappings?] -/
/-     have h := gen_mappings?_self l -/
/-     rw [Option.isSome_iff_exists] at h -/
/-     obtain ⟨x, xh⟩ := h -/
/-     simp  [xh] -/
/-   | @trans l₁ l₂ l₃ perm_l₁_l₂ perm_l₂_l₃ some₁₂ some₂₃ => -/
/-     apply gen_mappings?_trans some₁₂ some₂₃ -/

/- lemma gen_function_from_mapping -/

/- lemma gen_mappings_dep_preserves_l_from {U: Type} [DecidableEq U] : -/
/-   ∀(l_from l_to: List U) (ls_perm: l_from.Perm l_to), -/
/-   (List.unzip (gen_mappings_dep l_from l_to ls_perm)).fst = l_from -/
/- := by -/
/-   intros l_from -/
/-   unfold gen_mappings_dep -/
/-   unfold dependent_map -/
/-   generalize h: l_from = ref_list -/
/-   have h_tmp : -/
/-     ∀x y, dependent_map_aux ref_list ref_list x y = dependent_map_aux ref_list l_from x y -/
/-   := by -/
/-     simp -/
/-   induction l_from with -/
/-   | nil => intros; simp [gen_mappings_dep] -/
/-   | cons h t ih => -/
/-     intros l_to ls_perm -/
/-     simp at * -/
/-     unfold gen_mappings_dep at * -/
/-     rw [dependent_map_cons] at * -/
/-     unfold dependent_map at ih -/
/-     simp at * -/
/-     rw [dependent_map_aux_cons] -/
    
/-     sorry -/

def permutation_list_to_permutation {U: Type} [DecidableEq U]
  (l_from l_to: List U) (ls_perm: l_from.Perm l_to)
: U → U :=
  build_function_from_mappings (gen_mappings_dep l_from l_to ls_perm)

/- @[simp] -/
/- lemma permutation_list_to_permutation_nil {U: Type} [DecidableEq U]: -/
/-   ∀(l_to: List U) (ls_perm: [].Perm l_to), -/
/-   permutation_list_to_permutation [] l_to ls_perm = id -/
/- := by -/
/-   intro lt lp -/
/-   simp [permutation_list_to_permutation, dependent_map] -/

/- lemma permutation_list_to_permutation_applied_to_other {U: Type} [DecidableEq U]: -/
/-   ∀(l_from l_to: List U) (ls_perm: l_from.Perm l_to) (u: U), -/
/-   u ∉ l_from -/
/-   → (permutation_list_to_permutation l_from l_to ls_perm) u = u -/
/- := by -/
/-   intros l_from l_to ls_perm u u_nin -/
/-   unfold permutation_list_to_permutation -/
/-   apply build_function_from_mappings_applied_to_out -/
/-   simp; intros a b in_res contra; subst a -/


/-   revert l_to -/
/-   induction l_from with -/
/-   | nil => simp -/
/-   | cons h t ih => -/
/-     intros l_from ls_perm -/
/-     intro y -/
/-     simpu -/
/-     sorry -/

/- lemma permutation_list_to_permutation_bij {U: Type} [deq: DecidableEq U]: -/
/-   ∀(l_from l_to: List U) (ls_perm: l_from.Perm l_to), -/
/-   (permutation_list_to_permutation l_from l_to ls_perm).Bijective -/
/- := by -/
/-   intro lf -/
/-   simp [Function.Bijective] -/
/-   intro lt lp -/
/-   constructor -/
/-   . unfold Function.Injective -/
/-     intros a₁ a₂ h_eq -/
/-     have x : Decidable (a₁ ∈ lf) := by sorry -/
/-     cases x with -/
/-     | isTrue h => sorry -/
/-     | isFalse h => apply permutation_list_to_permutation_applied_to_other -/

/-     /1- Two cases: in list or not -1/ -/
/-     have h : ∀a, a ∈ lf ∨ a ∉ lf := by -/
/-       intro a; apply Decidable.em -/
/-   . sorry -/

/-   induction lf with -/
/-   | nil => -/
/-     intros lt lp -/
/-     rw [permutation_list_to_permutation_nil lt lp] -/
/-     apply Function.bijective_id -/
/-   | cons h t ih => -/
/-     intros lt lp -/
/-     have simpl_lt : t.Perm (lt.erase h) := by -/
/-       have t_revert : t = (h::t).erase h := by simp -/
/-       rw [t_revert]; apply List.Perm.erase -/
/-     specialize ih (lt.erase h) simpl_lt -/
/-     obtain ⟨ih_inj, ih_surj⟩ := ih -/
/-     constructor -/
/-     . unfold Function.Injective -/
/-       intros a₁ a₂ h_eq -/
/-     . sorry -/

def perm_to_Permutation {U: Type} (l1 l2: List U) (hl: ∀x, x ∈ l1 ↔ x ∈ l2)
: Permutation U := by
  constructor
  . constructor
    . sorry
    . sorry
  . sorry

/- instance : @Species Permutation where -/
/-   structures := -/
/-     fun ls => -/
/-       {ls.toList.permutations} -/

/-   transport := by sorry -/
/-   transport_trans := by sorry -/
/-   transport_id := by sorry -/

/-
structure Permutation (U: Type) where
  data_canonical: List U
  data_map: List ℕ
  data_is_permutation:
    data_map.length = data_canonical.length
    ∧ data_map.Perm (List.range (data_map.length))

def mk_Permutation {U: Type}
  (ls: List U) (ll: List ℕ)
  (ll_is_permutation: ll.Perm (List.range (ll.length)))
  (lengths_agree: ls.length = ll.length)
: Permutation U := {
  data_canonical := ls
  data_map := ll
  data_is_permutation := by
    constructor
    . rw [lengths_agree]
    . assumption
}

structure CyclicPermutation (U: Type) where
  data: List (ℕ × U)
  data_is_permutation:
    ∀n, List.map (Prod.fst) data ∈ List.cyclicPermutations (List.range n)

def Osef : Type := (a: ℕ) ×' (a%2 = 0)
def Osef_instance : Osef :=
  let h: 0%2 = 0 := by simp
  ⟨0, h⟩
-/


/- def list_zip_dep {A: Type} {B: A → Prop} (l: List A) (P: ∀x ∈ l, B x) -/
/- : (List ((a: A) ×' B a)) := by -/
/-   have f : (n: ℕ) → (n < l.length) → ((a: A) ×' B a) := by -/
/-     intro n np -/
/-     generalize x : l[n]? = h -/
/-     match h with -/
/-     | none => apply (List.getElem?_eq_getElem) at np; rw [x] at np; contradiction -/
/-     | some y => -/
/-       apply List.mem_of_getElem? at x; apply P at x; constructor; apply x -/
/-   apply (dependent_map (List.range (l.length)) f) -/

/- def permutations_from_labels {U: Type} (fs: Finset U) -/
/- : Finset (Permutation U) := -/
/-   let ls := Finset.toList fs -/
/-   let lp := List.permutations (List.range (List.length ls)) -/
/-   have lengths_eq : ∀x ∈ lp, x.length = ls.length := by -/
/-     intro x xin -/
/-     have h : ∀x ∈ lp, x.length = ls.length := by -/
/-       intro y yinlp; unfold lp at yinlp -/
/-       apply List.perm_of_mem_permutations at yinlp -/
/-       apply List.Perm.length_eq at yinlp -/
/-       rw [yinlp, List.length_range] -/
/-     apply h; apply xin -/
/-   let perms : -/
/-     ∀x ∈ lp, -/
/-     x.Perm (List.range (ls.length)) ∧ x.length = ls.length -/
/-   := by -/
/-     unfold lp -/
/-     intro x xinlp -/
/-     constructor -/
/-     . rw [← List.mem_permutations]; assumption -/
/-     . unfold lp at * -/
/-       specialize lengths_eq x xinlp; assumption -/
/-   let ConstrainedList : Type := -/
/-     (l: List ℕ) -/
/-     ×' (l.length = ls.length ∧ l.Perm (List.range (ls.length))) -/
/-   /1- let elp : ConstrainedList := sorry -1/ -/

/-
  List.map
  {
    data_canonical := ls
    data_map := fst x
    data_is_permutation := snd x
  }

instance : @Species Permutation where
  structures := by
    intro U fu
    let lu := Finset.toList fu
    let lp := List.permutations (List.range (List.length lu))
    apply (List.toFinset)
    . apply List.map
      swap
      . exact lp
      . have leq : ∀x ∈ lp, x.length = lu.length := by
          intro x xinlp
          unfold lp at xinlp
        apply
        (fun x =>
          mk_Permutation
            (Finset.toList fu) x

        )
      . sorry -- apply
      . sorry
    . sorry
   fun ls =>
    {List.map
      (fun x =>
        mk_Permutation
          (Finset.toList ls) x
          ()
      )
        (List.permutations (List.range (Finset.toList ls).length)
    )}
  transport := by
    intro U V σ σ_bij fu
    apply (Set.image σ fu)
  transport_trans := by
    intro U V W σ σ_bij τ τ_bij f
    simp; rw [Set.image_image]
  transport_id := by simp

lemma foo: powerset (Finset.range 8) = powerset (Finset.range 0) := by
  simp [powerset, Set.Iio, Set.powerset]
-/
