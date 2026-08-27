import Species.Operations.Add
import Species.Operations.Mul
import Species.Operations.Deriv
import Species.Instances.E
import Species.Basic

variable {F G : Type -> Type} [Species F] [Species G]

def deriv_SE {α : Type}: Species.Deriv SE α ≃ SE α
:= by
  constructor
  case toFun => intro x; constructor
  case invFun => intro x; constructor
  case right_inv => intro x; simp
  case left_inv => unfold Species.Deriv; intro x; simp
