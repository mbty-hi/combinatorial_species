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
    add_zero := sorry -- done
    zero_add := sorry -- done
    add_assoc := sorry -- done
    add_comm := sorry -- done
    zero_mul := sorry
    mul_zero := sorry
    one_mul := sorry -- done
    mul_one := sorry -- done
    mul_assoc := sorry
    left_distrib := sorry -- done
    right_distrib := sorry -- done
    -- npow



end Species
