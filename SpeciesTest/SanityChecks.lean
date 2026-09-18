import Species.Operations.Operations
import Species.Instances.Instances
import Species.Basic

open Species

variable {F G : Type -> Type} [Species F] [Species G] {U: Type} [Finite U]

def deriv_E: Deriv E U ≃ E U where
  toFun     x := ⟨⟩
  invFun    x := ⟨⟩
  right_inv x := rfl
  left_inv    := by unfold Species.Deriv; intro x; simp

/- If we know that a prefix of an orbit of `x` under `σ` (with `σ` being a permutation) does not
   come back to x, then the list containing the elements of this prefix is `Nodup`. -/
lemma nodup_iterate_prefix
  {α : Type*} (x : α) (σ : Equiv.Perm α)
  (n : ℕ) (not_overshot : ∀ k, 1 ≤ k → k ≤ n → (σ ^ k) x ≠ x)
: ((List.range (n + 1)).map fun k => (σ ^ k) x).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj hij; simp at *
  by_contra i_ne_j -- nodup expected, so the only way for `σ ^ i = σ ^ j` to happen is if `i = j`
  wlog i_le_j : i < j generalizing i j with h
  . exact h j i hij.symm hj hi (by omega) (by omega)
  apply not_overshot (j - i) (by omega) (by omega)
  have split_iterations : (σ ^ j) x = (σ ^ i) ((σ ^ (j - i)) x) := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' i_le_j.le]
  rw [split_iterations] at hij
  exact ((σ ^ i).injective hij).symm

/- It would be nice if we could be lazy and define this as a dumb function using fuel, which we
   would only ever access through a safe wrapper. However, picking an appropriate fuel quantity
   would not be feasible as `Nat.card` is noncomputable. Using it as a `termination_by` arg does not
   preclude computability, though. -/
def listFromCycleWithHole_aux
  /- Looks silly but we don't have a choice: both `U` and `[Finite U]` are in the variables, yet,
     since the body of the function does not rely on `Finite`, Lean forgets about it by the time we
     get to `decreasing_by`, where it actually is required. When adding `[Finite U]` alone, it
     complains about the instance being duplicated. Oh well. -/
  {U} [Finite U]
  (cycle : C (WithHole U)) (focus : WithHole U) (acc : List U)
  (invariant_focus_ok : focus = (cycle.1 ^ (acc.length + 1)) ⊥)
  (invariant_not_overshot : ∀ k, 1 ≤ k → k ≤ acc.length → (cycle.1 ^ k) ⊥ ≠ ⊥)
: List U :=
  match h : focus.val with
  | none => acc.reverse
  | some focus_u =>
    listFromCycleWithHole_aux
      cycle (cycle.1 focus) (focus_u :: acc)
      (by subst focus; simp [pow_succ'])
      (by
        intro k knz kle; rcases Nat.of_le_succ (by omega) with hk | rfl
        . exact invariant_not_overshot k knz hk
        . rw [← invariant_focus_ok]; intro rfl; contradiction
      )
termination_by Nat.card U - acc.length
decreasing_by
  simp; suffices h : acc.length + 1 ≤ Nat.card U by omega
  have hne' : ∀ k, 1 ≤ k → k ≤ acc.length + 1 → (cycle.1 ^ k) ⊥ ≠ ⊥ := by
    intro k knz kle; rcases Nat.of_le_succ (by omega) with hk | rfl
    . exact invariant_not_overshot k knz hk
    . rw [← invariant_focus_ok]; intro rfl; contradiction
  have hnd := nodup_iterate_prefix ⊥ cycle.1 (acc.length + 1) hne'
  have hle : acc.length + 2 ≤ Nat.card (WithHole U) := by
    have FintypeWH := Fintype.ofFinite (WithHole U)
    simp [Nat.card_eq_fintype_card]
    have h := hnd.length_le_card; simp at h; exact h
  have hcard : Nat.card (WithHole U) = Nat.card U + 1 := by
    simp [Nat.card_congr WithHole.equivOption, Finite.card_option]
  omega

def listFromCycleWithHole (cycle : C (WithHole U)) : List U :=
  listFromCycleWithHole_aux cycle (cycle.1 ⊥) [] (by simp) (by simp; intro k hk rfl; contradiction)

lemma listFromCycleWithHole_aux_spec
  (cycle : C (WithHole U)) (focus : WithHole U) (acc : List U)
  (inv_focus : focus = (cycle.1 ^ (acc.length + 1)) ⊥)
  (inv_not_overshot : ∀ k, 1 ≤ k → k ≤ acc.length → (cycle.1 ^ k) ⊥ ≠ ⊥)
  (hacc : acc.reverse.map WithHole.coe = (List.range acc.length).map fun k => (cycle.1 ^ (k + 1)) ⊥)
: let res := listFromCycleWithHole_aux cycle focus acc inv_focus inv_not_overshot
  res.map WithHole.coe = (List.range res.length).map fun k => (cycle.1 ^ (k + 1)) ⊥
:= by
  induction focus, acc, inv_focus, inv_not_overshot using listFromCycleWithHole_aux.induct with
  | case1 acc' inv_not_overshot' h =>
    dsimp; unfold listFromCycleWithHole_aux; split <;> simp_all
  | case2 acc' inv_not_overshot' u h ih =>
    dsimp; unfold listFromCycleWithHole_aux; split <;> simp_all
    next u' heq =>
      rw [h] at heq; simp at heq; subst u'
      apply ih; rw [List.range_succ, List.map_append]; congr; simp
      simp [WithHole.coe_val_eq h]

lemma listFromCycleWithHole_spec
  (cycle : C (WithHole U)) (n : ℕ) (hn : n < (listFromCycleWithHole cycle).length)
: WithHole.coe (listFromCycleWithHole cycle)[n] = (cycle.1 ^ (n + 1)) ⊥ := by
  unfold listFromCycleWithHole at *
  have h :=
    listFromCycleWithHole_aux_spec
      cycle (cycle.1 ⊥) [] (by simp) (by simp; intro k hk rfl; contradiction) (by simp)
  simp at h
  set res := listFromCycleWithHole_aux cycle (cycle.1 ⊥) [] _ _ with hres
  have h_at_n := congrArg (fun l => l[n]?) h
  simp [hn] at h_at_n
  exact h_at_n

lemma listFromCycleWithHole_nodup (cycle : C (WithHole U))
: (listFromCycleWithHole cycle).Nodup := by
  set res := listFromCycleWithHole cycle with hres
  -- no power 1..len returns to ⊥, because each is `coe` of something
  have hne : ∀ k, 1 ≤ k → k ≤ res.length → (cycle.1 ^ k) ⊥ ≠ ⊥ := by
    intro k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [← listFromCycleWithHole_spec cycle j (by rw [hres] at hk2; omega)]
    simp [WithHole.coe, Bot.bot]
  -- orbit list is nodup; our list (mapped by coe) is its tail
  have horb := nodup_iterate_prefix ⊥ cycle.1 res.length hne
  rw [List.range_succ_eq_map, List.map_cons, List.map_map] at horb
  have htail := horb.of_cons
  -- htail : ((range len).map (fun k => σ^(k+1) ⊥)).Nodup, up to `Function.comp`
  apply List.Nodup.of_map WithHole.coe
  subst res
  have hspec :
    (listFromCycleWithHole cycle).map WithHole.coe
    = (List.range (listFromCycleWithHole cycle).length).map fun k => (cycle.1 ^ (k + 1)) ⊥
  :=
    listFromCycleWithHole_aux_spec
      cycle (cycle.1 ⊥) [] (by simp) (by simp; rintro h k rfl; contradiction) (by simp)
  rw [hspec]
  exact htail

lemma WithHole.eq_bot_of_val_none {U} {x : WithHole U} (h : x.val = none) : x = ⊥ := by
  cases x; cases h; rfl

lemma listFromCycleWithHole_aux_period
  (cycle : C (WithHole U)) (focus : WithHole U) (acc : List U)
  (inv_focus : focus = (cycle.1 ^ (acc.length + 1)) ⊥)
  (inv_not_overshot : ∀ k, 1 ≤ k → k ≤ acc.length → (cycle.1 ^ k) ⊥ ≠ ⊥)
: let res := listFromCycleWithHole_aux cycle focus acc inv_focus inv_not_overshot
  (cycle.1 ^ (res.length + 1)) ⊥ = ⊥
:= by
  induction focus, acc, inv_focus, inv_not_overshot using listFromCycleWithHole_aux.induct with
  | case1 acc' inv_not_overshot' h =>
    dsimp; unfold listFromCycleWithHole_aux; split <;> simp_all
    next heq => exact WithHole.eq_bot_of_val_none heq
  | case2 acc' inv_not_overshot' u h ih =>
    dsimp; unfold listFromCycleWithHole_aux; split <;> simp_all
    next u' hu' => rw [h] at hu'; simp at hu'; subst u'; exact ih

lemma listFromCycleWithHole_period (cycle : C (WithHole U))
: (cycle.1 ^ ((listFromCycleWithHole cycle).length + 1)) ⊥ = ⊥ :=
  listFromCycleWithHole_aux_period
    cycle (cycle.1 ⊥) [] (by simp) (by simp; intro k hk rfl; contradiction)

lemma listFromCycleWithHole_complete (cycle : C (WithHole U)) (u : U)
: u ∈ listFromCycleWithHole cycle := by
  set res := listFromCycleWithHole cycle with hres
  set p : ℕ := res.length + 1 with hp
  -- there must be an `x` such that `u = (σ ^ x) ⊥`
  obtain ⟨i, hi⟩ := cycle.2.2 ⊥ (WithHole.coe u)
  -- reduce to `i mod p`, using `(σ ^ p) ⊥ = ⊥`
  have loops_in_p : (cycle.1 ^ p) ⊥ = ⊥ := by
    rw [hp, hres]; exact listFromCycleWithHole_period cycle
  have hred : (cycle.1 ^ (i % p).toNat) ⊥ = WithHole.coe u := by
    rw [← hi, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    conv_rhs => rw [← Int.emod_add_mul_ediv i p]
    rw [
      zpow_add, Equiv.Perm.mul_apply, zpow_mul, zpow_natCast,
      Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self loops_in_p
    ]
  -- the residue is in (0, p)
  set r := (i % p).toNat with hr
  have r_lt_p : r < p := by
    have h1 : i % (p : ℤ) < p := by apply Int.emod_lt_of_pos i (by omega)
    have h2 : 0 ≤ i % (p : ℤ) := by apply Int.emod_nonneg i (by omega)
    rw [hr]; omega
  obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := by
    refine ⟨r - 1, ?_⟩
    have : r ≠ 0 := fun h0 => by simp [h0, WithHole.coe, Bot.bot] at hred
    omega
  -- `(σ ^ (k + 1)) ⊥ = coe res[k]`, so `u = res[k]`
  have k_len : k < res.length := by omega
  have spec := listFromCycleWithHole_spec cycle k k_len
  subst r
  refine List.mem_iff_getElem.mpr ⟨k, k_len, ?_⟩
  rw [hk] at hred
  exact WithHole.coe_injective (spec.trans hred)



-- This is a nice example of a proof that is conceptually trivial, but that Lean has a hard time
-- accepting.
def derivCycleIsLinearOrder : Deriv C U ≃ L U where
  toFun := by
    -- The idea is just to cut at `*`, though it takes a fair amount of work to get Lean to agree
    unfold Deriv; intro c
    set order := listFromCycleWithHole c with hfoo
    /- refine ⟨ -/
    /-   order, -/
    /-   listFromCycleWithHole_nodup c, -/
    /-   listFromCycleWithHole_complete c -/
    /- ⟩ -/
    sorry
  invFun := by
    sorry
  right_inv   := by sorry
  left_inv    := by sorry
