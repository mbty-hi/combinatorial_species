import Species.Operations.Add
import Species.Operations.Deriv

theorem deriv_add {F G : Type → Type} :
  Species.Deriv (Species.add F G) = Species.add (Species.Deriv F) (Species.Deriv G)
:= by rfl
