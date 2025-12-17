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
    obtain ⟨eq, neq⟩ := x_eq_u
    . sorry
    . rw [if_neg]
      . sorry
      . intro ctr; subst ctr; contradiction

def undo_mapping? {U: Type} [BEq U] (l_from l_to: List U) (x: U) : Option U :=
  match l_to.idxOf? x with
  | .none => none
  | .some n =>
    match l_from[n]? with
    | .none => none
    | .some y => some y

lemma undo_mapping_succeeds {U: Type} [BEq U]:
  ∀x (l_from l_to: List U) n y,
  l_to.idxOf? x = some n → l_from[n]? = some y
  → ∃r, undo_mapping? l_from l_to x = some r
:= by
  intro x l_from l_to n y h_new_index h_replaced_item
  simp [undo_mapping?, h_new_index, h_replaced_item]

def undo_mapping {U: Type} [BEq U]
  (l_from l_to: List U) (x y: U) (n: ℕ) (_x_idx: l_to.idxOf? x = some n)
  (_l_from_nth: l_from[n]? = some y)
: U :=
  y

lemma undo_permutation_mapping {U: Type} [DecidableEq U]:
  ∀(l_from l_to: List U) (_l_from_perm_l_to: l_from.Perm l_to) (x: U) (_x_in_l_from: x ∈ l_from),
  ∃y, undo_mapping? l_from l_to x = some y
:= by
  intro l_from l_to ls_perm x xinlf
  have xinlt : x ∈ l_to := by apply ((List.Perm.mem_iff ls_perm).1 xinlf)
  simp [undo_mapping?]
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

def permutation_list_to_permutation {U: Type} [DecidableEq U]
  (l_from l_to: List U) (ls_perm: l_from.Perm l_to)
: U → U :=
  let mappings :=
    dependent_map
      l_from
      (fun (x: U) (xinlf: x ∈ l_from) =>
        have xinlt : x ∈ l_to := by apply ((List.Perm.mem_iff ls_perm).1 xinlf)
        have ls_len_eq := List.Perm.length_eq ls_perm
        have n_in_range := List.idxOf_lt_length_iff.2 xinlt
        have xn' := @List.idxOf_eq_getD_idxOf? U instBEqOfDecidableEq x l_to
        let pt : ((n: ℕ) ×' @l_to.idxOf? U instBEqOfDecidableEq x = some n) := by
          constructor
          generalize foo : @List.idxOf? U instBEqOfDecidableEq x l_to = u
          rw [foo] at xn'
          match u with
          | .none =>
            simp at *; apply Nat.ne_of_lt at n_in_range
            rw [← xn'] at n_in_range; apply n_in_range; rfl
          | .some c => simp at *; rw [← xn']
        let ⟨n, hn⟩ := pt
        let pf : ((y: U) ×' (l_from[n]? = some y)) := by
          rw [← ls_len_eq] at n_in_range; simp [hn] at xn'
          rw [xn'] at n_in_range
          apply List.getElem?_eq_getElem at n_in_range; rw [n_in_range]; simp
          constructor; rfl
        let ⟨y, hy⟩ := pf
        (x, @undo_mapping U instBEqOfDecidableEq l_from l_to x y n hn hy))
  build_function_from_mappings mappings

@[simp]
lemma permutation_list_to_permutation_nil {U: Type} [DecidableEq U]:
  ∀(l_to: List U) (ls_perm: [].Perm l_to),
  permutation_list_to_permutation [] l_to ls_perm = id
:= by
  intro lt lp
  simp [permutation_list_to_permutation, dependent_map, build_function_from_mappings]

lemma permutation_list_to_permutation_cons {U: Type} [DecidableEq U]:
  ∀(h: U) (t l_to: List U) (ls_perm: (h::t).Perm l_to),
  have x : t.Perm (l_to.eraseIdx (l_to.idxOf h)) := by
    apply List.cons_perm_iff_perm_erase.1 at ls_perm
    obtain ⟨lth1, lth2⟩ := ls_perm
    simp; assumption
  permutation_list_to_permutation (h::t) l_to ls_perm
  = permutation_list_to_permutation t (l_to.eraseIdx (l_to.idxOf h)) x
:= by
  intro u t lto lto_perm
  simp [permutation_list_to_permutation]
  simp [build_function_from_mappings]
  funext x
  simp [undo_mapping]
  have x_eq_u : x = u ∨ x ≠ u := by apply eq_or_ne x u
  obtain ⟨eq, neq⟩ := x_eq_u
  . simp
  . sorry

lemma permutation_list_to_permutation_bij {U: Type} [deq: DecidableEq U]:
  ∀(l_from l_to: List U) (ls_perm: l_from.Perm l_to),
  (permutation_list_to_permutation l_from l_to ls_perm).Bijective
:= by
  intro lf lt lp
  induction lf with
  | nil =>
    rw [permutation_list_to_permutation_nil lt lp]
    apply Function.bijective_id
  | cons h t ih =>
    s

def perm_to_Permutation {U: Type} (l1 l2: List U) (hl: ∀x, x ∈ l1 ↔ x ∈ l2)
: Permutation U := by
  constructor
  . constructor
    .
    . sorry
  . sorry

instance : @Species Permutation where
  structures :=
    fun ls =>
      {ls.toList.permutations}

  transport := by sorry
  transport_trans := by sorry
  transport_id := by sorry

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

/-
def Osef : Type := (a: ℕ) ×' (a%2 = 0)
def Osef_instance : Osef :=
  let h: 0%2 = 0 := by simp
  ⟨0, h⟩
-/
#print Option
-/


def list_zip_dep {A: Type} {B: A → Prop} (l: List A) (P: ∀x ∈ l, B x)
: (List ((a: A) ×' B a)) := by
  have f : (n: ℕ) → (n < l.length) → ((a: A) ×' B a) := by
    intro n np
    generalize x : l[n]? = h
    match h with
    | none => apply (List.getElem?_eq_getElem) at np; rw [x] at np; contradiction
    | some y =>
      apply List.mem_of_getElem? at x; apply P at x; constructor; apply x
  apply (dependent_map (List.range (l.length)) f)
-/

def permutations_from_labels {U: Type} (fs: Finset U)
: Finset (Permutation U) :=
  let ls := Finset.toList fs
  let lp := List.permutations (List.range (List.length ls))
  have lengths_eq : ∀x ∈ lp, x.length = ls.length := by
    intro x xin
    have h : ∀x ∈ lp, x.length = ls.length := by
      intro y yinlp; unfold lp at yinlp
      apply List.perm_of_mem_permutations at yinlp
      apply List.Perm.length_eq at yinlp
      rw [yinlp, List.length_range]
    apply h; apply xin
  let perms :
    ∀x ∈ lp,
    x.Perm (List.range (ls.length)) ∧ x.length = ls.length
  := by
    unfold lp
    intro x xinlp
    constructor
    . rw [← List.mem_permutations]; assumption
    . unfold lp at *
      specialize lengths_eq x xinlp; assumption
  let ConstrainedList : Type :=
    (l: List ℕ)
    ×' (l.length = ls.length ∧ l.Perm (List.range (ls.length)))
  let elp : ConstrainedList := sorry

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

/-
lemma foo: powerset (Finset.range 8) = powerset (Finset.range 0) := by
  simp [powerset, Set.Iio, Set.powerset]
-/
