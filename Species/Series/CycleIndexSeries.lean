import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.PowerSeries.Basic
import Species.Basic
import Species.Computable

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

/-- Get the coefficient associated with the given monomial `μ`. In effect, this gives the sum of
    |`F`-structures kept fixed| for each `σ` of the `μ` shape. -/
noncomputable def cisCoeff (n : ℕ) (μ : Multiset ℕ) : ℕ :=
  MvPolynomial.coeff (Multiset.toFinsupp μ) (cisNumerator F n)

/-- `Z_F(c₁ x, c₂ x², c₃ x³, …)`: turns the CIS into a one-variable formal power series by replacing
    each `xₖ` with `cₖ xᵏ`.
    Note that permutations of `n` labels contribute to the coefficient `xⁿ` only. Therefore, the
    the coefficient of `xⁿ` is `cisNumerator F n` evaluated with `xₖ = cₖ`, divided by `n!`. -/
noncomputable def cisSpecialize (cₖ : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk
    (fun n =>
      MvPolynomial.eval₂ (Nat.castRingHom ℚ) (fun x => cₖ x) (cisNumerator F n) / n.factorial
    )

end Species

namespace ComputableSpecies

variable (F : Type → Type) [ComputableSpecies F] {U : Type} [DecidableEq U] [Fintype U]

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

/-- Computable `cisCoeff`, coefficient associated with the given monomial `μ` -/
def cisCoeff (n : ℕ) (μ : Multiset ℕ) : ℕ :=
  let cycles_n := cisNumerator F n
  let matching := cycles_n.filter (fun c => c.2 = μ)
  (matching.map (fun c => c.1)).sum

section Correctness

lemma fixCount_eq (σ : Equiv.Perm U) : fixCount σ = Species.fixCount σ := by
  unfold fixCount Species.fixCount Species.fixSet
  simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, Function.mem_fixedPoints]; rfl

section cycleTypeToCyclesCorrespondence

section factorPoint

/-- The support of a permutation is the set of points that are not fixed by it.
A fixpoint is not viewed as a cycle factor; therefore cycle factors move at least one point. For
instance, `U` could be `{1, …, 6}`, `σ` could be `(1 2)(3 4 5)` (note that `6` is a fixpoint here)
and `cycleFactor` could be `(3 4 5)`. In other words, their support is not empty. -/
lemma cycleFactor_support_nonempty (σ : Equiv.Perm U) (cycleFactor : σ.cycleFactorsFinset)
: cycleFactor.1.support.Nonempty :=
  (Equiv.Perm.mem_cycleFactorsFinset_iff.1 cycleFactor.2).1.nonempty_support

/-- Picks a point from the support of `cycleFactor` using choice -/
noncomputable def factorPoint (σ : Equiv.Perm U) (cycleFactor : σ.cycleFactorsFinset) : U :=
  (cycleFactor_support_nonempty σ cycleFactor).choose

/-- The point thus picked trivially belongs to the support -/
lemma factorPoint_mem (σ : Equiv.Perm U) (cycleFactor : σ.cycleFactorsFinset)
: factorPoint σ cycleFactor ∈ cycleFactor.1.support :=
  (cycleFactor_support_nonempty σ cycleFactor).choose_spec

/-- …and is therefore moved by `σ` -/
lemma factorPoint_moved (σ : Equiv.Perm U) (cycleFactor : σ.cycleFactorsFinset)
: σ (factorPoint σ cycleFactor) ≠ factorPoint σ cycleFactor :=
  Equiv.Perm.mem_support.1
    (Equiv.Perm.mem_cycleFactorsFinset_support_le cycleFactor.2
    (factorPoint_mem σ cycleFactor))

/-- A cycle factor equals is the cycle of any point in its support (obviously) -/
lemma cycleFactor_eq_cycleOf_factorPoint (σ : Equiv.Perm U) (cycleFactor : σ.cycleFactorsFinset)
: cycleFactor.1 = σ.cycleOf (factorPoint σ cycleFactor) :=
  Equiv.Perm.cycle_is_cycleOf (factorPoint_mem σ cycleFactor) cycleFactor.2

end factorPoint

section classOf

/-- A label is either a fixed point or it belongs to a cycle factor. Our definition of
`Species.Cycles` subsumes both cases. This returns the one such cycle given either a fixpoint or a
cycle factor. This is actually a bijection (see `classOf_bojective` below) -/
noncomputable def classOf (σ : Equiv.Perm U) (v: {x // σ x = x} ⊕ σ.cycleFactorsFinset)
: Species.Cycles σ :=
  match v with
  | .inl x => ⟦x.1⟧
  | .inr f => ⟦factorPoint σ f⟧

/-- A fixed point is only in the same cycle as itself -/
lemma eq_of_sameCycle_fixed {U} {σ : Equiv.Perm U} {x y : U} (hx : σ x = x) (h : σ.SameCycle x y)
: y = x := by
  obtain ⟨i, rfl⟩ := h
  exact Function.IsFixedPt.perm_zpow hx i

/-- `classOf` is a bijection -/
lemma classOf_bijective (σ : Equiv.Perm U) : Function.Bijective (classOf σ) := by
  refine ⟨?injective, ?surjective⟩
  case injective =>
    rintro (fixₗ | facₗ) (fixᵣ | facᵣ) h <;> simp only [classOf] at h
      <;> have h' := Quotient.exact h
    · -- two fixed points in the same class must be equal
      exact congrArg Sum.inl (Subtype.ext (eq_of_sameCycle_fixed fixᵣ.2 h'.symm))
    · exact
        absurd (by rw [eq_of_sameCycle_fixed fixₗ.2 h']; exact fixₗ.2) (factorPoint_moved σ facᵣ)
    · exact
        absurd
          (by rw [eq_of_sameCycle_fixed fixᵣ.2 h'.symm]; exact fixᵣ.2) (factorPoint_moved σ facₗ)
    · -- two factors sharing a class are the same cycle
      refine congrArg Sum.inr (Subtype.ext ?_)
      repeat rw [cycleFactor_eq_cycleOf_factorPoint σ _]
      exact Equiv.Perm.SameCycle.cycleOf_eq h'
  case surjective =>
    intro c; obtain ⟨x, rfl⟩ := Quotient.exists_rep c
    by_cases hx : σ x = x
    · -- fixed: a singleton class
      exact ⟨.inl ⟨x, hx⟩, rfl⟩
    · -- moved: the class of its cycle factor
      have hmem : σ.cycleOf x ∈ σ.cycleFactorsFinset :=
        Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2 (Equiv.Perm.mem_support.2 hx)
      refine ⟨.inr ⟨_, hmem⟩, Quotient.sound ?_⟩
      exact (Equiv.Perm.mem_support_cycleOf_iff.1 (factorPoint_mem σ ⟨_, hmem⟩)).1.symm

/-- The class of `x` has one element if `x` is fixed, otherwise it is the support of its cycle -/
lemma card_class (σ : Equiv.Perm U) (x : U) :
  Nat.card {u : U | (⟦u⟧ : Species.Cycles σ) = ⟦x⟧}
  = (if σ x = x then 1 else (σ.cycleOf x).support.card)
:= by
  -- the class of `x` is `{u | SameCycle σ x u}`
  have hset : {u : U | (⟦u⟧ : Species.Cycles σ) = ⟦x⟧} = {u | σ.SameCycle x u} := by
    ext u; simp only [Set.mem_ofPred_eq, Quotient.eq]
    exact ⟨fun h => Equiv.Perm.SameCycle.symm h, fun h => Equiv.Perm.SameCycle.symm h⟩
  rw [hset]; split_ifs with hfix
  · -- fixed point: its class is `{x}`
    have hsing : {u | σ.SameCycle x u} = {x} := by
      ext u; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]; constructor
      · rintro ⟨i, hi⟩; rw [← hi]; exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix i
      · rintro rfl; exact Equiv.Perm.SameCycle.refl _ _
    rw [hsing, Nat.card_coe_set_eq, Set.ncard_singleton]
  · -- moved point: its class is the support of `cycleOf x`
    have hsupp : {u | σ.SameCycle x u} = ↑(σ.cycleOf x).support := by
      ext u; rw [Finset.mem_coe, Equiv.Perm.mem_support_cycleOf_iff];
      simp only [
        Set.mem_ofPred_eq, Equiv.Perm.mem_support, ne_eq, hfix, not_false_eq_true, and_true
      ]
    rw [hsupp, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- The class of a fixpoint has length 1 -/
lemma length_classOf_fix (σ : Equiv.Perm U) (x : {x // σ x = x})
: Nat.card {u | (⟦u⟧ : Species.Cycles σ) = classOf σ (.inl x)} = 1 := by
  simp only [classOf]; rw [card_class, if_pos x.2]

/-- The class of a cycle factor `c` has length `c.card` -/
lemma length_classOf_fac (σ : Equiv.Perm U) (cycleFactor : σ.cycleFactorsFinset)
: Nat.card {u | (⟦u⟧ : Species.Cycles σ) = classOf σ (.inr cycleFactor)}
  = cycleFactor.1.support.card
:= by
  simp only [classOf]
  rw [
    card_class, if_neg (factorPoint_moved σ cycleFactor),
    ← cycleFactor_eq_cycleOf_factorPoint σ cycleFactor
  ]

end classOf

-- The fixed points of `σ` are the complement of its support
lemma card_fixed (σ : Equiv.Perm U)
: Fintype.card {x // σ x = x} = Fintype.card U - σ.support.card := by
  rw [← Equiv.Perm.sum_cycleType, ← Equiv.Perm.card_fixedPoints]
  exact Fintype.card_congr (Equiv.refl _)

end cycleTypeToCyclesCorrespondence

lemma cycleLengths_eq (σ : Equiv.Perm U) : cycleLengths σ = Species.cycleLengths σ := by
  let _ := Fintype.ofFinite (Species.Cycles σ)
  set e := Equiv.ofBijective _ (classOf_bijective σ)
  unfold cycleLengths Species.cycleLengths
  -- reindex the classes as `fixed points ⊕ cycle factors`
  rw [← Finset.univ_map_equiv_to_embedding e, Finset.map_val, Multiset.map_map]
  simp only [
    ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum, Multiset.map_add,
    Multiset.map_map, Function.comp_def, Equiv.coe_toEmbedding, e, Equiv.ofBijective_apply,
    length_classOf_fix, length_classOf_fac, Multiset.map_const', Finset.card_val, Finset.card_univ
  ]
  rw [Equiv.Perm.parts_partition, card_fixed, add_comm]
  congr 1
  rw [Equiv.Perm.cycleType_def]
  conv_lhs => rw [← Multiset.attach_map_val σ.cycleFactorsFinset.val]
  rw [Multiset.map_map]
  rfl

lemma cycleCount_eq (σ : Equiv.Perm U) (k : ℕ) : cycleCount σ k = Species.cycleCount σ k := by
  unfold cycleCount Species.cycleCount
  rw [cycleLengths_eq]

/-- Summing the computed terms as monomials gives the noncomputable numerator. -/
lemma cisNumerator_eq (n : ℕ)
: ((cisNumerator F n).map fun t => MvPolynomial.monomial (Multiset.toFinsupp t.2) t.1).sum
  = Species.cisNumerator F n
:= by
  unfold cisNumerator Species.cisNumerator
  rw [Multiset.map_map, Finset.sum_eq_multiset_sum]
  congr 1
  apply Multiset.map_congr
  · rfl
  · intro σ _
    simp only [Function.comp_apply, cisMonomial, Species.cisMonomial, Species.cycleExp]
    rw [fixCount_eq, cycleLengths_eq]

lemma coeff_sum_monomials (s : Multiset (ℕ × Multiset ℕ)) (μ : Multiset ℕ) :
  MvPolynomial.coeff
    (Multiset.toFinsupp μ) ((s.map fun t => MvPolynomial.monomial (Multiset.toFinsupp t.2) t.1).sum)
  = ((s.filter (fun x => x.2 = μ)).map (fun x => x.1)).sum
:= by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [
      Multiset.map_zero, Multiset.sum_zero, MvPolynomial.coeff_zero, Multiset.filter_zero
    ]
  | cons t s ih =>
    rw [
      Multiset.map_cons, Multiset.sum_cons, MvPolynomial.coeff_add, ih, MvPolynomial.coeff_monomial,
      Multiset.filter_cons
    ]
    by_cases h : t.2 = μ
    · simp only [h, ↓reduceIte, Multiset.singleton_add, Multiset.map_cons, Multiset.sum_cons]
    · simp only [EmbeddingLike.apply_eq_iff_eq, h, ↓reduceIte, zero_add]

lemma cisCoeff_eq (n : ℕ) (μ : Multiset ℕ) : cisCoeff F n μ = Species.cisCoeff F n μ := by
  unfold cisCoeff Species.cisCoeff
  rw [← cisNumerator_eq, coeff_sum_monomials]

end Correctness

end ComputableSpecies
