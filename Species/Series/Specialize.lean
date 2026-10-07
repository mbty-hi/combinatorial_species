import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries
import Species.Series.CycleIndexSeries

namespace Species

variable (F : Type → Type) [Species F]

section egs_from_cis
/-- EGS from CIS: `Z_F(x, 0, 0, …) = F(x)`.
    Conceptually, setting `x_k` to `0` for all `k > 1` means killing every term that contains
    anything that is not a one-cycle, effectively leaving us with the identity permutation only. -/

-- Evaluating a monomial given by a multiset of indices yields the product of the values
lemma toFinsupp_prod_pow (s : Multiset ℕ) (g : ℕ → ℚ)
: (Multiset.toFinsupp s).prod (fun k e => g k ^ e) = (s.map g).prod := by
  rw [Finsupp.prod, Multiset.toFinsupp_support, Finset.prod_multiset_map_count]
  simp [Multiset.toFinsupp_apply]

/-- With `x_1 = 1` and `x_k = 0` otherwise, only permutations without cycles of length ≥ 2
    survive. -/
lemma prod_indicator_one {n : ℕ} (σ : Equiv.Perm (Fin n))
: ((cycleLengths σ).map fun k => if k = 1 then (1 : ℚ) else 0).prod = if σ = 1 then 1 else 0 := by
  rw [
    ← SpeciesComp.cycleLengths_eq, SpeciesComp.cycleLengths, Equiv.Perm.parts_partition,
    Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, if_pos rfl,
    Multiset.prod_replicate, one_pow, mul_one
  ]
  split_ifs with h
  · subst h; simp
  · -- some cycle of length `≥ 2` contributes a factor `0`
    obtain ⟨k, hk⟩ := Multiset.exists_mem_of_ne_zero (mt Equiv.Perm.cycleType_eq_zero.1 h)
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨k, hk, ?_⟩)
    have := Equiv.Perm.two_le_of_mem_cycleType hk
    rw [if_neg (by omega)]

/-- The identity fixes every structure. -/
lemma fixCount_transportEquiv_one (n : ℕ)
: fixCount (U := F (Fin n)) (transportEquiv (F := F) (1 : Equiv.Perm (Fin n)))
  = Nat.card (F (Fin n))
:= by
  have h1 : (transportEquiv (F := F) (1 : Equiv.Perm (Fin n)) : Equiv.Perm (F (Fin n))) = 1 :=
    Equiv.ext fun f => by
      show Species.transport (1 : Equiv.Perm (Fin n)) f = f
      rw [Equiv.Perm.one_def]; exact Species.id_transport f
  unfold fixCount fixSet
  rw [h1, Equiv.Perm.coe_one, Function.fixedPoints_id, Nat.card_univ]

theorem egs_from_cis : cisSpecialize F (fun k => if k = 1 then 1 else 0) = egs F := by
  ext n; simp only [cisSpecialize, egs, PowerSeries.coeff_mk]; congr 1
  calc MvPolynomial.eval₂ (Nat.castRingHom ℚ) (fun k => if k = 1 then 1 else 0) (cisNumerator F n)
    -- every term with a cycle of length `≥ 2` is killed
    _ = ∑ σ : Equiv.Perm (Fin n),
        (fixCount (U := F (Fin n)) (transportEquiv σ) : ℚ) * (if σ = 1 then 1 else 0)
      := by
        simp only [
          cisNumerator, cisMonomial, cycleExp, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial,
          Nat.coe_castRingHom, toFinsupp_prod_pow, prod_indicator_one
        ]
    -- we are left with the identity only
    _ = (fixCount (U := F (Fin n)) (transportEquiv (F := F) (1 : Equiv.Perm (Fin n))) : ℚ) := by
      simp [Finset.sum_ite_eq']
    -- the identity fixes every structure
    _ = (egsCoeff F n : ℚ) := by rw [fixCount_transportEquiv_one, egsCoeff]

end egs_from_cis

section tgs_from_cis
/-- TGS from CIS: `Z_F(x, x², x³, …) = F~(x)`.
    Conceptually, setting `x_k` to `x^k` means that all monomials end up looking like
    `x^n` (we are just counting labels). Then, for each `n`, we get `((1/n!) Σ_σ fix F[σ])xⁿ`.
    By Burnside, this is the number of orbits, which corresponds to the number of unlabeled
    structures. -/

-- Burnside: summing fixed-point counts over `Sₙ` gives `n!` times the number of orbits
lemma tgsCoeff_mul_factorial (n : ℕ)
: tgsCoeff F n * n.factorial
  = ∑ σ : Equiv.Perm (Fin n), fixCount (U := F (Fin n)) (transportEquiv σ)
:= by
  classical
  let _ := Fintype.ofFinite (F (Fin n))
  have hB :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Equiv.Perm (Fin n)) (F (Fin n))
  rw [Fintype.card_perm, Fintype.card_fin] at hB; unfold tgsCoeff; rw [Nat.card_eq_fintype_card]
  convert hB.symm using 1
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  -- `Fix F[σ]` is `fixedBy (F (Fin n)) σ`: both are `{f | transport σ f = f}`
  unfold fixCount fixSet
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.refl _)

theorem tgs_from_cis : cisSpecialize F (fun _ => 1) = tgs F := by
  ext n; simp only [cisSpecialize, tgs, PowerSeries.coeff_mk]
  calc MvPolynomial.eval₂ (Nat.castRingHom ℚ) (fun _ => 1) (cisNumerator F n) / n.factorial
    -- every monomial evaluates to `1`, leaving the sum of fixed-point counts…
    _ = ((∑ σ : Equiv.Perm (Fin n), fixCount (U := F (Fin n)) (transportEquiv σ) : ℕ) : ℚ)
          / n.factorial := by
      simp [cisNumerator, cisMonomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_monomial,
            Finsupp.prod]
    -- …which is `n!` times the number of orbits (Burnside)
    _ = (tgsCoeff F n : ℚ) := by
      rw [← tgsCoeff_mul_factorial, Nat.cast_mul]
      exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.2 n.factorial_ne_zero)

end tgs_from_cis

end Species
