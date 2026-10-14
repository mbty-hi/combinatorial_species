import Species.Instances.L
import Species.Series.ExponentialGeneratingSeries
import Species.Series.TypeGeneratingSeries
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.SetTheory.Cardinal.Finite

namespace Species

section EGS

/-- A linear order on `U` is a bijection with `Fin |U|` (since `card` is forced). -/
noncomputable def equivEquiv (U : Type) [Finite U] : L U ≃ (U ≃ Fin (Nat.card U)) where
  toFun x  := by
    obtain ⟨card, equiv⟩ := x; trans
    · apply equiv
    · apply (finCongr (Nat.card_eq_of_equiv_fin equiv).symm)
  invFun e := ⟨_, e⟩
  left_inv := fun ⟨n, e⟩ => by
    have h : n = Nat.card U := by rw [Nat.card_congr e, Nat.card_fin]
    subst h; simp only [finCongr_refl, Equiv.trans_refl]
  right_inv e := by simp only [finCongr_refl, Equiv.trans_refl]

lemma card_L (n : ℕ) : Nat.card (L (Fin n)) = n.factorial := by
  simp only [Nat.card_eq_fintype_card]; rw [Fintype.card_congr (equivEquiv _)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_perm]

theorem egs_L : egs L = PowerSeries.mk (fun _ => 1) := by
  ext n; simp only [egs, PowerSeries.coeff_mk, egsCoeff, card_L]
  simp only [div_self_eq_one₀, ne_eq, Nat.cast_eq_zero]
  apply n.factorial_ne_zero

end EGS

section TGS

lemma L.card_eq {U : Type} [Finite U] (l : L U) : l.card = Nat.card U := by
  simpa using (Nat.card_congr l.ord).symm

/-- Any two linear orders on `U` are the same up to relabelling -/
lemma L_transitive {U : Type} [Finite U] (l₁ l₂ : L U)
: ∃ σ : Equiv.Perm U, Species.transport σ l₁ = l₂ := by
  obtain ⟨c₁, e₁⟩ := l₁; obtain ⟨c₂, e₂⟩ := l₂
  obtain rfl : c₁ = c₂ := (L.card_eq ⟨c₁, e₁⟩).trans (L.card_eq ⟨c₂, e₂⟩).symm
  refine ⟨e₁.trans e₂.symm, ?_⟩
  show L.mk _ ((e₁.trans e₂.symm).symm.trans e₁) = ⟨_, e₂⟩
  congr 1; ext x
  simp only [Equiv.symm_trans, Equiv.symm_symm, Equiv.trans_apply, Equiv.apply_symm_apply]

instance (n : ℕ) : MulAction.IsPretransitive (Equiv.Perm (Fin n)) (L (Fin n)) :=
  ⟨fun l₁ l₂ => L_transitive l₁ l₂⟩

lemma tgsCoeff_L (n : ℕ) : tgsCoeff L n = 1 := by
  unfold tgsCoeff
  have _ : Subsingleton (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n)) (L (Fin n))) :=
    ⟨fun a b => Quotient.inductionOn₂ a b fun x y =>
      Quotient.sound (MulAction.exists_smul_eq _ y x)⟩
  exact Nat.card_of_subsingleton ⟦⟨n, Equiv.refl _⟩⟧

theorem tgs_L : tgs L = PowerSeries.mk (fun _ => 1) := by
  ext n; simp only [tgs, tgsCoeff_L, Nat.cast_one, PowerSeries.coeff_mk]

end TGS

section ClosedForms

theorem egs_L_closed : egs L = (1 - PowerSeries.X)⁻¹ := by rw [egs_L, mk_one_eq_inv]
theorem tgs_L_closed : tgs L = (1 - PowerSeries.X)⁻¹ := by rw [tgs_L, mk_one_eq_inv]

end ClosedForms

end Species
