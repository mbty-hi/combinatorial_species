import Species.Basic
import Species.Instances.One
import Species.Instances.Zero
import Species.Operations.Add
import Species.Operations.Mul
import Mathlib.Algebra.Ring.Defs

namespace Semiring
  instance instSpeciesSemiring : Semiring (Type → Type) where
    add := Species.add
    mul := Species.mul
    zero := SZero
    one := SOne
  
end Semiring
