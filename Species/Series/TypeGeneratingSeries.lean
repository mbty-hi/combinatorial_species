import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Species.Basic

/- (fₙ)~ : number of isomorphism types of F-structures on [n] -/
noncomputable def TGS_coeff (F) [Species F] (n : ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (F (Fin n)))

/- Type generating series : F̃(x) = Σ ((fₙ)∼ * xⁿ) -/
noncomputable def TGS (F) [Species F] : PowerSeries ℚ :=
  PowerSeries.mk fun n => (TGS_coeff F n)
