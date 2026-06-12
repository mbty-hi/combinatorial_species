import Species.Labels.LabelType

/- Finite natural numbers as labels. Just an alias around `Fin`: -/
abbrev FinNat (n : ℕ) : Type := Fin n

/- Sanity check: `Fin` already is `Fintype`/`LinearOrder`/..., so this should resolve. -/
example (n : ℕ) : LabelType (FinNat n) := inferInstance
