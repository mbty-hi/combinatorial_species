import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Species.Basic
/- import Mathlib.GroupTheory.Perm.CycleType -/

namespace Species

-- FIXME
/- /1- Cycle index of the action of Sₙ on F-structures on [n] -1/ -/
/- noncomputable def cycleIndex (F : Type → Type) [SpeciesComp F] (n : ℕ) : Polynomial ℚ := -/
/-   let Sₙ := Equiv.Perm (Fin n) -/
/-   -- sum over conjugacy classes of Sₙ: each class represented by cycle type -/
/-   -- For each σ ∈ Sₙ, the monomial is x_1^{c₁(σ)} · x_2^{c₂(σ)} · ... · x_n^{c_n(σ)} -/
/-   -- where c_k(σ) = number of k-cycles in σ -/
/-   Polynomial.sum (Finset.univ : Finset Sₙ) fun σ => -/
/-     let c := CycleType.cycleType σ  -- List ℕ, sum = n -/
/-     -- Convert to monomial: ∏ₖ xₖ^cₖ -/
/-     -- This is a simplified placeholder; proper implementation needs monomial construction -/
/-     Polynomial.monomial (Finset.univ : Finset ℕ) 1  -- placeholder -/

end Species
