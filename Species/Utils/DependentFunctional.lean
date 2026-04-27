/- Dependent counterparts to classical functional operations -/
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Data.List.Nodup

-- Map
-- This definition of `dependent_map` is stronger than that of `map` as it provides a proof of the
-- fact that the element being mapped belongs to the original list to the function doing the
-- mapping.
-- TODO stdlib's pmap actually does that same, switch to it.
def dependent_map_aux
  {A B: Type} (ref_list: List A) (sub_list: List A) (sub_list_Sublist: sub_list.Sublist ref_list)
  (f: (a: A) → a ∈ ref_list → B)
: List B := by
  generalize x : sub_list = sub_list'; revert sub_list'
  match sub_list with
  | List.nil => intro l l_empty; apply List.nil
  | List.cons h t =>
    intro l hl
    apply List.cons
    . apply f
      have hh : h ∈ ref_list := by apply List.Sublist.mem _ sub_list_Sublist; simp
      apply hh
    . apply dependent_map_aux ref_list t (List.sublist_of_cons_sublist sub_list_Sublist) f

def dependent_map {A B: Type} (l: List A) (f: (a: A) → a ∈ l → B) : List B :=
  dependent_map_aux l l (List.Sublist.refl l) f

@[simp]
theorem dependent_map_aux_nil {A B: Type}:
  ∀ rl (f: (a: A) → a ∈ rl → B), dependent_map_aux rl [] (List.nil_sublist rl) f = []
:= by
  simp [dependent_map_aux]

@[simp]
theorem dependent_map_aux_nil_rl {A B: Type}:
  ∀ sl (slp: sl.Sublist []) (f: (a: A) → a ∈ [] → B), dependent_map_aux [] sl slp f = []
:= by
  intro sl slp f
  have foo : sl = [] := by rw [List.eq_nil_of_sublist_nil slp]
  conv =>
    left
    . congr
      . rw [foo]
  simp

@[simp]
theorem dependent_map_nil {A B: Type}: ∀(f: (a: A) → a ∈ [] → B), dependent_map [] f = [] := by
  simp [dependent_map, dependent_map_aux]

@[simp]
theorem dependent_map_aux_cons {A B: Type}:
  ∀ (h: A) (t rl: List A) (ht_sl_rl: (h::t).Sublist rl) (f: (a: A) → a ∈ rl → B),
  let t_sl_rl : t.Sublist rl := List.sublist_of_cons_sublist ht_sl_rl
  let h_in_rl : h ∈ rl := List.mem_of_cons_sublist ht_sl_rl
  dependent_map_aux rl (h::t) ht_sl_rl f = (f h h_in_rl)::(dependent_map_aux rl t t_sl_rl f)
:= by
  simp [dependent_map_aux]

@[simp]
theorem dependent_map_cons {A B: Type}:
  ∀ (h: A) (t: List A) (f: (a: A) → a ∈ h::t → B),
  let t_sl_rl : t.Sublist (h::t) := List.sublist_cons_self h t
  let h_in_rl : h ∈ h::t := List.mem_cons_self
  dependent_map (h::t) f = (f h h_in_rl)::(dependent_map_aux (h::t) t t_sl_rl f)
:= by
  simp [dependent_map, dependent_map_aux]

theorem generalize_dependent_map_aux {A B: Type}:
  ∀ (rl sl sl': List A) (slp: sl.Sublist rl) (f: (a: A) → a ∈ rl → B) (sl_sl': sl = sl'),
  let slp' : sl'.Sublist rl := by rw [sl_sl'] at slp; apply slp
  dependent_map_aux rl sl slp f = dependent_map_aux rl sl' slp' f
:= by
  intro rl sl sl' slp f sl_sl' slp'
  conv =>
    rhs
    congr
    . rw [← sl_sl']
    . rfl

theorem generalize_dependent_map_aux_bis {A B: Type}:
  ∀ (rl sl: List A) (slp: sl.Sublist rl) (f: (a: A) → a ∈ rl → B),
  ∃ sl' slp', dependent_map_aux rl sl slp f = dependent_map_aux rl sl' slp' f
:= by
  intro rl sl slp f
  exists sl, slp

theorem map_to_dependent_map_aux:
  ∀ {A B: Type} (f: A → B) (sl rl: List A) (rl_sl: sl.Sublist rl),
  List.map f sl = dependent_map_aux rl sl rl_sl (fun x _ => f x)
:= by
  intro A B f sl
  induction sl with
  | nil => intro rl rl_sl; simp
  | cons h t ih => intro rl rl_sl; simp; apply ih

theorem map_to_dependent_map:
  ∀ {A B: Type} (f: A → B) (l: List A),
  List.map f l = dependent_map l (fun x _ => f x)
:= by
  intro A B f l
  simp [dependent_map]
  apply map_to_dependent_map_aux

theorem dependent_map_aux_inj_unique_nodup {A B: Type}:
  ∀ (rl sl: List A) (h: A) (_slp: (h :: sl).Sublist rl) (f: (a: A) → a ∈ rl → B)
    (slp': sl.Sublist rl) (hp: h ∈ rl) (_h_nin_sl: h ∉ sl),
  (∀ m n x y, f x y = f m n → m = x)
  → (f h hp) ∉ dependent_map_aux rl sl slp' f
:= by
  intro rl sl h slp f slp' hp h_nin_sl f_inj
  induction sl with
  | nil => simp
  | cons h' t' ih =>
    simp
    constructor
    . have h_neq_h' : h ≠ h' := by intro ctr; subst ctr; simp at h_nin_sl
      intro ctr; apply f_inj at ctr; subst ctr; simp at h_neq_h'
    . apply ih
      . apply (List.Sublist.trans (l₂ := h :: h' :: t')); simp; assumption
      . intro ctr; apply List.not_mem_of_not_mem_cons at h_nin_sl; contradiction

theorem dependent_map_aux_inj_preserves_Nodup {A B: Type}:
  ∀ (rl sl: List A) (slp: sl.Sublist rl) (f: (a: A) → a ∈ rl → B),
  sl.Nodup → (∀ m n x y, f x y = f m n → m = x) → (dependent_map_aux rl sl slp f).Nodup
:= by
  intro rl sl slp f sl_nd f_inj
  induction sl with
  | nil => simp
  | cons h t ih =>
    simp
    constructor
    . apply dependent_map_aux_inj_unique_nodup
      . apply slp
      . intro ctr; apply List.Nodup.notMem at sl_nd; contradiction
      . apply f_inj
    . have t_sl : t.Sublist rl := (List.sublist_of_cons_sublist slp)
      have t_nd : t.Nodup := by
        simp at sl_nd
        obtain ⟨_, t_nd⟩ := sl_nd
        assumption
      specialize ih t_sl t_nd
      apply ih

theorem dependent_map_inj_preserves_Nodup:
  ∀ (A B: Type) (l: List A) (f: (a: A) → a ∈ l → B),
  l.Nodup → (∀ m n x y, f x y = f m n → m = x) → (dependent_map l f).Nodup
:= by
  intro A B l f l_nd f_inj
  simp [dependent_map]
  apply dependent_map_aux_inj_preserves_Nodup l l _ f l_nd f_inj
