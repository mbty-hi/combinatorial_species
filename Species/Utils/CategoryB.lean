import Mathlib.CategoryTheory.Category.Basic

instance CategoryB : Category.SmallCategory where
  hom _ _ := {}
  id _ := id
  comp f g :=

  id_comp := by grind
  comp_id := by grind
  assoc := by grind
