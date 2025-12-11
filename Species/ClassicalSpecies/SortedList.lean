-- Sorted lists
-- TODO Does this actually belong here?
/- def is_increasing_list (l: List ℕ) : Prop := -/
/-   ∀(n: ℕ), -/
/-   l[n + 1]? = none -/
/-   ∨ (∃(x y: ℕ), l[n]? = some x ∧ l[n + 1]? = some y ∧ x ≤ y) -/

/- structure IncreasingList where -/
/-   l: List ℕ -/
/-   increasing: is_increasing_list l -/

/- @[simp] -/
/- def sorted_insert (l: List ℕ) (n: ℕ) : List ℕ := -/
/-   match l with -/
/-   | .nil => [n] -/
/-   | .cons h t => -/
/-     if Nat.blt h n = true -/
/-     then List.cons h (sorted_insert t n) -/
/-     else List.cons n l -/

/- @[simp] -/
/- def sort_list (l: List ℕ) : List ℕ := -/
/-   List.foldl sorted_insert [] l -/

/- lemma sorted_insert_increments_length : -/
/-   ∀l n, (sorted_insert l n).length = l.length + 1 -/
/- := by -/
/-   intro l -/
/-   induction l with -/
/-   | nil => simp -/
/-   | cons h t ih => intro n; simp; grind -/

/- lemma is_increasing_alt : -/
/-   ∀t h, -/
/-   is_increasing_list (h :: t) -/
/-   ↔ (is_increasing_list t ∧ (t = [] ∨ (∃x, t[0]? = some x ∧ h ≤ x))) -/
/- := by -/
/-   intros t h -/
/-   constructor -/
/-   . intro inc -/
/-     constructor -/
/-     . unfold is_increasing_list at *; simp at * -/
/-       intro n; specialize (inc (n + 1)); simp at inc; exact inc -/
/-     . unfold is_increasing_list at inc -/
/-       specialize (inc 0); simp at inc -/
/-       exact inc -/
/-   . simp; unfold is_increasing_list at * -/
/-     intros inc_t first_ok n -/
/-     match n with -/
/-     | .zero => simp; exact first_ok -/
/-     | .succ n' => simp at *; specialize (inc_t n'); exact inc_t -/

/- lemma sorted_insert_prepend: -/
/-   ∀h t n x, -/
/-   is_increasing_list (sorted_insert (h::t) n) -/
/-   → x ≤ h -/
/-   → x ≤ n -/
/-   → is_increasing_list (x :: (sorted_insert (h::t) n)) -/
/- := by -/
/-   intros h t n x sl x_h x_n -/
/-   unfold is_increasing_list; unfold is_increasing_list at sl -/
/-   simp at *; split -/
/-   case isFalse h_n => -/
/-     simp -/
/-     rw [if_neg h_n] at sl; simp at sl -/
/-     intro n_1 -/
/-     match n_1 with -/
/-     | .zero => simp; apply x_n -/
/-     | .succ n_1' => specialize (sl n_1'); simp at *; apply sl -/
/-   case isTrue h_n => -/
/-     simp -/
/-     rw [if_pos h_n] at sl; simp at sl -/
/-     intro n_1 -/
/-     match n_1 with -/
/-     | .zero => simp; apply x_h -/
/-     | .succ n_1' => specialize (sl n_1'); simp at *; apply sl -/

/- lemma sorted_insert_preserves_is_increasing_list: -/
/-   ∀l, is_increasing_list l → ∀n, is_increasing_list (sorted_insert l n) -/
/- := by -/
/-   intros l lh -/
/-   induction l with -/
/-   | nil => simp [is_increasing_list] -/
/-   | cons h t ih => -/
/-     intro n; simp -/
/-     split -/
/-     case isFalse h_n => -/
/-       apply (is_increasing_alt _ _).2 -/
/-       constructor -/
/-       . apply lh -/
/-       . right; simp; omega -/
/-     case isTrue h_n => -/
/-       match t with -/
/-       | .nil => simp; unfold is_increasing_list; grind -/
/-       | .cons h' t' => -/
/-         apply sorted_insert_prepend -/
/-         . apply ih; apply (is_increasing_alt _ _).1 at lh -/
/-           apply lh.1 -/
/-         . apply (is_increasing_alt _ _).1 at lh -/
/-           obtain ⟨a, b⟩ := lh -/
/-           simp at b; apply b -/
/-         . omega -/

/- lemma sort_list_result_is_increasing_aux: -/
/-   ∀l acc_init, -/
/-   is_increasing_list acc_init -/
/-   → is_increasing_list (List.foldl sorted_insert acc_init l) -/
/- := by -/
/-   intro l -/
/-   induction l with -/
/-   | nil => unfold is_increasing_list; simp -/
/-   | cons h t ih => -/
/-     intros acc_init acc_init_sorted -/
/-     simp [sorted_insert] -/
/-     have h' : is_increasing_list (sorted_insert acc_init h) := by -/
/-       apply sorted_insert_preserves_is_increasing_list -/
/-       apply acc_init_sorted -/
/-     apply ih; apply h' -/

/- lemma sort_list_result_is_increasing: -/
/-   ∀l, is_increasing_list (sort_list l) -/
/- := by -/
/-   intro l -/
/-   unfold sort_list; apply sort_list_result_is_increasing_aux -/
/-   simp [is_increasing_list] -/

/- def List_to_IncreasingList (l: List ℕ) : IncreasingList := { -/
/-   l := sort_list l -/
/-   increasing := sort_list_result_is_increasing l -/
/- } -/

/- def insert_in_IncreasingList (il: IncreasingList) (n: ℕ) -/
/- : IncreasingList := { -/
/-   l := sorted_insert il.l n -/
/-   increasing := -/
/-     sorted_insert_preserves_is_increasing_list (il.l) (il.increasing) n -/
/- } -/

/- def il1 := List_to_IncreasingList ((92:ℕ) :: (9: ℕ) :: (8: ℕ) :: []) -/
/- #eval il1 -/
/- def il2 := insert_in_IncreasingList il1 (45: ℕ) -/
/- #eval il2 -/

