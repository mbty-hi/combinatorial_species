import Species.Arithmetic.Add
import Species.Arithmetic.Mul
import Species.Basic
import Species.Instances.One
import Species.Instances.Zero
import Species.Operations.Add
import Species.Operations.Mul
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Basic

namespace Species
  instance : Zero (Type → Type) where
    zero := SZero

  instance : Add (Type → Type) where
    add := Species.add

  instance instSpeciesSemiring : Semiring (Type → Type) where
    add := Species.add
    mul := Species.mul
    zero := SZero
    one := SOne
    nsmul := nsmulRec
    nsmul_zero := by unfold nsmulRec; simp
    nsmul_succ := by
      intro n x
      induction n with
      | zero => unfold nsmulRec; grind
      | succ n ih => unfold nsmulRec; grind
    add_zero := sorry
    zero_add := sorry
    add_assoc := sorry
    add_comm := sorry
    zero_mul := sorry
    mul_zero := sorry
    one_mul := sorry
    mul_one := sorry
    mul_assoc := sorry
    left_distrib := sorry
    right_distrib := sorry



end Species
