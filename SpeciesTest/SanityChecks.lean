import Species.Operations.Add
import Species.Operations.Deriv

variable {F G: Type → Type}

theorem deriv_add :
  Species.Deriv (F + G) = Species.Deriv F + Species.Deriv G := by
  funext U
  rfl
