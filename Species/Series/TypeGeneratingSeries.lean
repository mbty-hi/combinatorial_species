import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Species.Basic

/- (fₙ)~ : number of isomorphism types of F-structures on [n] -/
noncomputable def TGS_coeff (F) [SpeciesComp F] (n : ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (F (Fin n)))

/- def TGS_coeff_Burnside (F) [Species F] (n : ℕ) [DecidableEq (F (Fin n))] : ℕ := -/
/-   (∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter (fun f => σ • f = f)).card) / n.factorial -/

/- Type generating series : F̃(x) = Σ ((fₙ)∼ * xⁿ) -/
noncomputable def TGS (F) [SpeciesComp F] : PowerSeries ℚ :=
  PowerSeries.mk fun n => (TGS_coeff F n)
