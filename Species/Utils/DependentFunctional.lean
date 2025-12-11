/- Dependent counterparts to classical functional operations -/

-- Map
def dependent_map {A B: Type} (l: List A) (f: (a: A) → a ∈ l → B) : List B := by
  generalize x : l = l'; revert l'
  induction l with
  | nil => intro l l_empty; apply List.nil
  | cons h t ih =>
    intro l hl
    apply List.cons
    . apply f
      have hh : h ∈ h::t := by simp
      apply hh
    . apply ih
      . intro a aint
        have ah : a ∈ h::t := by simp; right; assumption
        apply (f a ah)
      . rfl

lemma dependent_map_nil {A B: Type}:
  ∀(f: (a: A) → a ∈ [] → B), dependent_map [] f = []
:= by
  simp [dependent_map]

/- lemma dependent_map_adapter {A B: Type}: -/
/-   ∀(ref_list: List A) (sub_list: List A) (sl_in_rl: ∀x, x ∈ sub_list → x ∈ ref_list) -/
/-    (f: (a: A) → a ∈ ref_list → B), -/
/-    dependent_map sub_list -/ 

/- lemma dependent_map_cons {A B: Type}: -/
/-   ∀(h: A) (t: List A) (f: (a: A) → a ∈ (h::t) → B), -/
/-   dependent_map (h::t) f = sorry -/
/- := by -/
/-   simp [dependent_map] -/


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
