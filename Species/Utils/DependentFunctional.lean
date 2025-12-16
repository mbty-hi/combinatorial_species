/- Dependent counterparts to classical functional operations -/
import Mathlib.Tactic.NthRewrite

-- Map
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
  ∀rl (f: (a: A) → a ∈ rl → B), dependent_map_aux rl [] (List.nil_sublist rl) f = []
:= by
  simp [dependent_map_aux]

@[simp]
theorem dependent_map_nil {A B: Type}: ∀(f: (a: A) → a ∈ [] → B), dependent_map [] f = [] := by
  simp [dependent_map, dependent_map_aux]

@[simp]
theorem dependent_map_aux_cons {A B: Type}:
  ∀(h: A) (t rl: List A) (ht_sl_rl: (h::t).Sublist rl) (f: (a: A) → a ∈ rl → B),
  let t_sl_rl : t.Sublist rl := List.sublist_of_cons_sublist ht_sl_rl
  let h_in_rl : h ∈ rl := List.mem_of_cons_sublist ht_sl_rl
  dependent_map_aux rl (h::t) ht_sl_rl f = (f h h_in_rl)::(dependent_map_aux rl t t_sl_rl f)
:= by
  simp [dependent_map_aux]

@[simp]
theorem dependent_map_cons {A B: Type}:
  ∀(h: A) (t: List A) (f: (a: A) → a ∈ h::t → B),
  let t_sl_rl : t.Sublist (h::t) := List.sublist_cons_self h t
  let h_in_rl : h ∈ h::t := List.mem_cons_self
  dependent_map (h::t) f = (f h h_in_rl)::(dependent_map_aux (h::t) t t_sl_rl f)
:= by
  simp [dependent_map, dependent_map_aux]

/- theorem generalize_dependent_map_aux {A B: Type}: -/
/-     ∀ (rl sl sl': List A) (slp: sl.Sublist rl) (f: (a: A) → a ∈ rl → B) (sl_sl': sl = sl'), -/
/-     let slp' : sl'.Sublist rl := by rw [sl_sl'] at slp; apply slp -/
/-     dependent_map_aux rl sl slp f = dependent_map_aux rl sl' slp' f -/
/-   := by -/
/-     intro rl sl sl' slp f sl_sl' -/
/-     sorry /1- A bit painful due to dependent types -1/ -/

/- theorem map_to_dependent_map: -/
/-   ∀{A B: Type} (f: A → B) (l: List A), -/
/-   List.map f l = dependent_map l (fun x _ => f x) -/
/- := by -/
/-   intro A B f l -/
/-   simp [dependent_map] -/
/-   generalize hrl : l = rl -/
/-   symm at hrl -/
/-   rw [generalize_dependent_map_aux rl rl l (List.Sublist.refl rl) (fun x _ => f x) hrl] -/
/-   induction l with -/
/-   | nil => simp [dependent_map, dependent_map_aux] -/
/-   | cons h t ih => -/
/-     simp [dependent_map, dependent_map_aux] at * -/

/- theorem dependent_map_inj_preserves_Nodup: -/
/-   ∀(A B: Type) (l: List A) (f: (a: A) → a ∈ l → B), -/
/-   l.Nodup → Function.Injective f → (dependent_map l f).Nodup -/
/- := by -/
/-   intro A B l f l_nd f_inj -/


-- Fold
/-
def dependent_foldl
  {A ACC: Type}
  (l: List A) (n: ℕ) (acc_init: ACC) (acc: ACC) (ll: n < l.length)
  (acch:
    acc =
      match n with
      | .zero => acc_init
      | .succ n' => dependent_foldl l n' acc_init
  )
: ACC := by
-/
