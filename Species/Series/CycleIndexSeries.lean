import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.PowerSeries.Basic
import Species.Basic

namespace Species

variable (F : Type → Type) [Species F] {U : Type} [Finite U]

/-- `Fix σ`: set of fixpoints of `σ` -/
def fixSet (σ : Equiv.Perm U) : Set U := Function.fixedPoints σ

/-- `fix σ`: number of fixpoints of `σ` -/
noncomputable def fixCount (σ : Equiv.Perm U) : ℕ := Nat.card (fixSet σ)

/-- Type of cycles for some `σ` (quotienting to avoid double counting) -/
abbrev Cycles (σ : Equiv.Perm U) := Quotient (Equiv.Perm.SameCycle.setoid σ)

/-- Builds a multiset that plays the role of the book's (σ₁, σ₂, …, σₙ) vector, counting the number
    of cycles of length `1` to `n` -/
noncomputable def cycleLengths (σ : Equiv.Perm U) : Multiset ℕ :=
  letI _ := Fintype.ofFinite (Cycles σ)
  (Finset.univ : Finset (Cycles σ)).val.map (fun c => Nat.card { u | ⟦u⟧ = c })

/-- `σ_k`: number of cycles of length `k`. Note that this uses the permutation only, we do not care
    about `F` at this stage. -/
noncomputable def cycleCount (σ : Equiv.Perm U) (k : ℕ) : ℕ := (cycleLengths σ).count k

/-- Values of the `σ_k` components of the monomial `x₁^σ₁ x₂^σ₂ …` -/
noncomputable def cycleExp (σ : Equiv.Perm U) : ℕ →₀ ℕ :=
  Multiset.toFinsupp (cycleLengths σ)

/-- `fix F[σ] x₁^σ₁ x₂^σ₂ …`, for a given permutation `σ` -/
noncomputable def cisMonomial {n : ℕ} (σ : Equiv.Perm (Fin n)) : MvPolynomial ℕ ℕ :=
  MvPolynomial.monomial (cycleExp σ) (fixCount (U := F (Fin n)) (transportEquiv σ))

/-- The sum of the above for all permutations on a set of n-labels -/
noncomputable def cisNumerator (n : ℕ) : MvPolynomial ℕ ℕ :=
  ∑ (σ : Equiv.Perm (Fin n)), cisMonomial F σ

/-- Z_F(x₁, x₂, …) = Σ ((1/n!) (Σ (for σ in Sₙ) ((fix F[σ]) x₁^σ₁ x₂^σ₂ …))) -/
noncomputable def cis : MvPowerSeries ℕ ℚ := fun m =>
  let n := m.sum fun k c => k * c
  ((MvPolynomial.coeff m (cisNumerator F n) : ℕ) : ℚ) / n.factorial

end Species

namespace SpeciesComp

variable (F : Type → Type) [SpeciesComp F] {U : Type} [DecidableEq U] [Fintype U]

/-- Computable `fix σ` -/
def fixCount (σ : Equiv.Perm U) : ℕ := (Finset.univ.filter fun u => σ u = u).card

/-- Computable multiset storing cycle lengths -/
def cycleLengths (σ : Equiv.Perm U) : Multiset ℕ := σ.partition.parts

/-- How many cycles of length `k` exist for σ, using the above -/
def cycleCount (σ : Equiv.Perm U) (k : ℕ) : ℕ := (cycleLengths σ).count k

/-- Computable `cisMonomial σ`, with a different return type than in the `Species` section, as
  `MvPolynomial`s are not computable -/
def cisMonomial {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ × Multiset ℕ :=
  (fixCount (Species.transportEquiv (F := F) σ), cycleLengths σ)

/-- Computable `cisNumerator`, result of summing the above over all possible permutations on `n` -/
def cisNumerator (n : ℕ) : Multiset (ℕ × Multiset ℕ) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).val.map (cisMonomial (F := F))

/-- Get the coefficient associated with the given monomial `μ`. In effect, this gives the sum of
    |`F`-structures kept fixed| for each `σ` of the `μ` shape. -/
def cisCoeff (n : ℕ) (μ : Multiset ℕ) : ℕ :=
  let cycles_n := cisNumerator F n
  let matching := cycles_n.filter (fun c => c.2 = μ)
  (matching.map (fun c => c.1)).sum

-- TODO correspondence with noncomp

end SpeciesComp

/-/1-- egs from cis: conceptually, setting `x_k` to `0` for all `k > 1` means killing every term -/
/-    that contains anything that is not a one-cycle, effectively leaving us with the identity -/
/-    permutation only. -1/ -/
/-lemma egs_from_cis : sorry := sorry -/

/-/1-- tgs from cis: conceptually, setting `x_k` to `x^k` means that all monomials end up looking like -/
/-    `x^n` (we are just counting labels). Then, for each `n`, we get `((1/n!) Σ_σ fix F[σ])xⁿ`. -/
/-    By Burnside, this is the number of orbits, which corresponds to the number of unlabeled -/
/-    structures. -1/ -/
/-lemma tgs_from_cis : sorry := sorry -/
