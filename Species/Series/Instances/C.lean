module

public import Species.Operations.Deriv
public import Species.Identities.DerivC
public import Species.Instances.C
public import Species.Series.Instances.L
public import Species.Series.ExponentialGeneratingSeries
public import Species.Series.TypeGeneratingSeries

@[expose] public section

namespace Species

section EGS

lemma card_C_zero : Nat.card (C (Fin 0)) = 0 := by
  simp only [C, IsEmpty.forall_iff, and_true]
  exact Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨_, ⟨x⟩⟩ => x.elim0⟩)

/-- A cycle on `n + 1` labels is functionally the same as a cycle on `n` labels plus a hole, i.e., a
linear order on `n` (we can view the hole as the starting point) -/
lemma card_C_succ (n : ℕ) : Nat.card (C (Fin (n + 1))) = n.factorial := by
  have e : Fin (n + 1) ≃ WithHole (Fin n) := (finSuccEquiv n).trans WithHole.equivOption.symm
  rw [Nat.card_congr ((transportEquiv (F := C) e).trans derivCycleEquivLinearOrder), card_L]

/-- `C(x) = Σ_{n ≥ 1} xⁿ/n` (i.e., `log (1/(1 − x))`) -/
theorem egs_C : egs C = PowerSeries.mk fun n => if n = 0 then 0 else (1 : ℚ) / n := by
  ext n
  simp only [egs, PowerSeries.coeff_mk, egsCoeff]
  rcases n with _ | n
  · simp only [
      Nat.card_eq_fintype_card, Nat.factorial_zero, Nat.cast_one, div_one, ↓reduceIte,
      Nat.cast_eq_zero
    ]
    rw [Fintype.card_eq_nat_card, card_C_zero]
  · -- `n! / (n+1)! = 1/(n+1)`
    rw [card_C_succ, ite_eq_right n.succ_ne_zero, Nat.factorial_succ]
    have _ : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    push_cast
    field_simp

end EGS

section TGS

/- Trivially enough, there is only one cycle of length `n` up to relabelling. -/

/-- Relabelling a linear order, then adding the hole = adding the hole, then relabelling -/
lemma holeEquiv_transport {U V : Type} [Finite U] [Finite V] (σ : U ≃ V) (l : L U)
: (holeEquiv (Species.transport σ l)).ord = (WithHole.transport σ).symm.trans (holeEquiv l).ord :=
  Equiv.ext fun ⟨x⟩ => by cases x <;> rfl

/-- `LToCWithHole` commutes with relabelling (the hole stays fixed) -/
lemma LToCWithHole_transport {U V : Type} [Finite U] [Finite V] (σ : U ≃ V) (l : L U)
: LToCWithHole (Species.transport σ l) = Species.transport (WithHole.transport σ) (LToCWithHole l)
:= by
  apply Subtype.ext; ext x
  show
    (holeEquiv _).ord.symm (finRotate _ ((holeEquiv _).ord x))
    = WithHole.transport
        σ ((holeEquiv l).ord.symm (finRotate _ ((holeEquiv l).ord ((WithHole.transport σ).symm x))))
  rw [holeEquiv_transport]; rfl

lemma LToCWithHole_natural {U V : Type} [Finite U] [Finite V] (σ : U ≃ V) (l : L U)
: LToCWithHole (Species.transport σ l) = Species.transport (F := Deriv C) σ (LToCWithHole l) :=
  LToCWithHole_transport σ l

/-- `left_inv` of the equivalence, as a named fact -/
lemma LToC_CToL {U : Type} [Finite U] (c : C (WithHole U)) : LToCWithHole (CWithHoleToL c) = c :=
  derivCycleEquivLinearOrder.left_inv c

/-- Any two cycles through the hole are relabellings of each other -/
lemma C_hole_transitive {U : Type} [Finite U] (c₁ c₂ : C (WithHole U))
: ∃ π : Equiv.Perm (WithHole U), Species.transport π c₁ = c₂ := by
  obtain ⟨σ, hσ⟩ := L_transitive (CWithHoleToL c₁) (CWithHoleToL c₂)
  refine ⟨WithHole.transport σ, ?_⟩
  calc Species.transport (WithHole.transport σ) c₁
    _ = Species.transport (WithHole.transport σ) (LToCWithHole (CWithHoleToL c₁)) := by
      rw [LToC_CToL]
    _ = LToCWithHole (Species.transport σ (CWithHoleToL c₁)) := (LToCWithHole_transport σ _).symm
    _ = LToCWithHole (CWithHoleToL c₂) := by rw [hσ]
    _ = c₂ := LToC_CToL c₂

/-- The same on `n + 1` labels: move to `WithHole (Fin n)`, relabel there, move back -/
lemma C_transitive_succ (n : ℕ) (c₁ c₂ : C (Fin (n + 1)))
: ∃ σ : Equiv.Perm (Fin (n + 1)), Species.transport σ c₁ = c₂ := by
  let e : Fin (n + 1) ≃ WithHole (Fin n) := (finSuccEquiv n).trans WithHole.equivOption.symm
  obtain ⟨π, hπ⟩ := C_hole_transitive (Species.transport e c₁) (Species.transport e c₂)
  refine ⟨(e.trans π).trans e.symm, ?_⟩
  rw [
    ← Species.transport_transport, ← Species.transport_transport, hπ,
    Species.transport_transport, Equiv.self_trans_symm, Species.id_transport
  ]

instance (n : ℕ) : MulAction.IsPretransitive (Equiv.Perm (Fin (n + 1))) (C (Fin (n + 1))) :=
  ⟨C_transitive_succ n⟩

/-- One unlabelled cycle per positive size, none on the empty set -/
lemma tgsCoeff_C (n : ℕ) : tgsCoeff C n = if n = 0 then 0 else 1 := by
  cases n with
  | zero =>
    have _ : IsEmpty (C (Fin 0)) := ⟨fun c => c.2.1.some.elim0⟩
    exact Nat.card_of_isEmpty
  | succ n =>
    rw [ite_eq_right n.succ_ne_zero]
    have _ :=
      (MulAction.pretransitive_iff_subsingleton_quotient
        (Equiv.Perm (Fin (n + 1)))
        (C (Fin (n + 1)))
      ).1 inferInstance
    exact Nat.card_of_subsingleton ⟦rotC n⟧

/-- `C̃(x) = Σ_{n ≥ 1} xⁿ = x (1 − x)⁻¹` -/
theorem tgs_C : tgs C = PowerSeries.X * (1 - PowerSeries.X)⁻¹ := by
  rw [← mk_one_eq_inv]; ext n
  cases n
  · simp only [
      tgs, tgsCoeff_C, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one, PowerSeries.coeff_mk,
      ↓reduceIte, PowerSeries.coeff_zero_X_mul
    ]
  · simp only [
      tgs, tgsCoeff_C, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one, PowerSeries.coeff_mk,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, PowerSeries.coeff_succ_X_mul
    ]

end TGS
end Species
end
