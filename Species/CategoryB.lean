import Species.Basic
import Mathlib.CategoryTheory.Groupoid

/- Defines `FinBij`, which corresponds to Joyal's `B` category.
   Objects are `LabelType`s, morphisms are bijections.
   TODO actually use this somewhere -/

open CategoryTheory

structure FinBij where
  α : Type
  [inst : LabelType α]

attribute [instance] FinBij.inst

instance : Category FinBij where
  Hom X Y     := X.α ≃ Y.α
  id  X       := Equiv.refl X.α
  comp f g    := f.trans g
  id_comp _   := Equiv.ext fun _ => rfl
  comp_id _   := Equiv.ext fun _ => rfl
  assoc _ _ _ := Equiv.ext fun _ => rfl

instance : Groupoid FinBij where
  inv        := Equiv.symm
  inv_comp f := Equiv.ext fun x => f.apply_symm_apply x
  comp_inv f := Equiv.ext fun x => f.symm_apply_apply x
