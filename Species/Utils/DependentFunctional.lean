/- Dependent counterparts to classical functional operations -/
import Mathlib.Data.List.Nodup

-- A version of that remembers that the elements come from the original list
def dependent_map {A B: Type} (l: List A) (f: (a: A) → a ∈ l → B) : List B :=
  List.pmap f l (fun _ h => h)

theorem dependent_map_inj_preserves_Nodup
  {A B: Type} (l: List A) (f: (a: A) → a ∈ l → B) (l_nd: l.Nodup)
  (f_inj: ∀ m n x y, f m n = f x y → m = x)
: (dependent_map l f).Nodup :=
  List.Nodup.pmap f_inj l_nd
