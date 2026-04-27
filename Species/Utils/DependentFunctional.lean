/- Dependent counterparts to classical functional operations -/
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Data.List.Nodup

-- Map
-- This definition of `dependent_map` is stronger than that of `map` as it provides a proof of the
-- fact that the element being mapped belongs to the original list to the function doing the
-- mapping.
def dependent_map {A B: Type} (l: List A) (f: (a: A) → a ∈ l → B) : List B :=
  List.pmap f l (fun _ h => h)

theorem dependent_map_inj_preserves_Nodup:
  ∀ (A B: Type) (l: List A) (f: (a: A) → a ∈ l → B),
  l.Nodup → (∀ m n x y, f x y = f m n → m = x) → (dependent_map l f).Nodup
:= by
  intro A B l f l_nd f_inj
  simp [dependent_map]
  apply List.Nodup.pmap
  intros a ha b hb eq
  apply f_inj; rotate_left; apply ha; apply hb; apply l_nd; symm; apply eq
