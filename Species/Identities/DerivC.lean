module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Species.Operations.Operations
public import Species.Instances.Instances
public import Species.Basic

@[expose] public section

namespace Species

variable {F G : Type -> Type} [Species F] [Species G] {U: Type} [Finite U]

/- To a first approximation (don't take this too literally):
   `L ≝ (U ≃ Fin |U|)`
   `C ≝ <bij: U ≃ U | Nonempty U ∧ bij.IsSingleCycle>`
   `Deriv (F U) ≝ F (WithHole U) ≝ F (Option U)`

   In this section, we build the equivalence `L U ≃ Deriv C U`, which we can easily reduce to
   `L ≃ C (WithHole U)` or `L ≃ C (Option U)`.

   Note: this is a good example of a proof that's conceptually trivial but that is quite laborious
   to spell out in Lean. The obvious high-level description: "just break the (oriented) cycle at
   the hole, what's left must be a linear order" contains all the actual insight there is to this
   proof. The formalization gets dragged down by the fact that we are dealing with a very concrete
   (and computable) construction. The proof could be much simpler if MathLib's cycle-to-list API
   came with fewer requirements (our `U` has neither `DecidableEq` nor `Fintype`). My intuitive
   proof would use the fact that both of these can be embedded within (directed) graphs.

   We need to build both directions of the bijection before showing that the result is indeed a
   bijection (`f ∘ f' = id`, `f' ∘ f = id`).

   `L` → `C` with a hole, conceptually (this direction really is quite simple):
   * we build an `l' ≝ <l with a hole>`, keeping the same position for all items of l and mapping
     the hole to |U|; this can be seen as a bijection between `(WithHole U)` and `Fin (|U| + 1)`
   * we build the canonical `c: C (Fin (|U| + 1))` (`0 → `1` → … → `card` → `0`)
   * we transport `c`, remapping `n` to the element associated with it in `l'`

   `C` with a hole → `L`, things remain conceptually simple though the implementation was harder.
   * For each `u` in our cycle `c`, how many backward steps until we hit the hole? Call this
     distance `d`
   * `u` gets associated with `d - 1` (since numbering starts at `0`) -/

section LToCWithHole

/- append the hole at the end of the order: `u ↦ ord u` (order of `l` preserved), `⊥ ↦ card` (hole
   appended) -/
abbrev holeEquiv (l : L U) : L (WithHole U) :=
  ⟨l.card + 1, WithHole.equivOption.trans ((Equiv.optionCongr l.ord).trans finSuccEquivLast.symm)⟩

-- "rotating" some `i` of type `Fin card` by `n` positions brings it to `(i + n) mod card`
lemma finRotate_pow_val (card n : ℕ) (i : Fin card)
: ((finRotate card ^ n) i).val = (i.val + n) % card := by
  induction n with
  | zero      => simp only [pow_zero, Equiv.Perm.coe_one, id_eq, add_zero, Nat.mod_eq_of_lt i.2]
  | succ _ ih =>
    simp only [
      pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, finRotate_apply, Fin.val_add, ih,
      Nat.add_mod, dvd_refl, Nat.mod_mod_of_dvd, Fin.coe_ofNat_eq_mod, ← add_assoc
    ]

-- rotations of `Fin` have a single orbit
lemma finRotate_sameCycle (card : ℕ) (x y : Fin card) : (finRotate card).SameCycle x y := by
  refine ⟨(y.val + (card - x.val) : ℕ), ?_⟩
  rw [zpow_natCast]; ext
  have hx := x.2
  rw [
    finRotate_pow_val, show x.val + (y.val + (card - x.val)) = y.val + card by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt y.2
  ]

-- canonical cycle `0` → `1` → … → `card` → `0`
def rotC (card : ℕ) : C (Fin (card + 1)) where
  val      := finRotate (card + 1)
  property := ⟨
    ⟨0⟩, -- nonempty
    finRotate_sameCycle (card + 1) -- same cycle
  ⟩

-- we just transport `rotC`, remapping `n` to the element associated with it in `holeEquiv`
def LToCWithHole (l : L U) : C (WithHole U) :=
  let l' := holeEquiv l
  let canonical_cycle := rotC l.card
  Species.transport l'.ord.symm canonical_cycle

end LToCWithHole

section CWithHoleToL
/- Remember the plan:
   * For each `u` in our cycle `c`, how many backward steps until we hit the hole? Call this
     distance `d`
   * `u` gets associated with `d - 1` (since numbering starts at `0`) -/

variable (c : C (WithHole U))

lemma WithHole.isNone_iff_eq_bot {U} (x : WithHole U) : x.val.isNone = true ↔ x = ⊥ := by
  obtain ⟨_ | u⟩ := x
  <;> simp only [
        Option.isNone_none, Option.isNone_some, Bool.false_eq_true, Bot.bot, mk.injEq, reduceCtorEq
      ]

-- going from `x` to `⊥` via `σ` is as long as going from `⊥` to `x` via `σ⁻¹`
lemma symm_pow_apply_eq_bot_iff {U} (σ : Equiv.Perm (WithHole U)) (m : ℕ) (x : WithHole U)
: (σ.symm ^ m) x = ⊥ ↔ x = (σ ^ m) ⊥ := by
  rw [← Equiv.Perm.inv_def, inv_pow, Equiv.Perm.inv_eq_iff_eq]

section DistanceFromHole
-- we also use this to define the length of a cycle: how many steps from `⊥` to `⊥`?

-- number of steps to the next hole
lemma exists_distanceFromHole (x : WithHole U) : ∃ d, 0 < d ∧ ((c.1.symm ^ d) x).val.isNone := by
  obtain ⟨m, hm⟩ := (c.2.2 ⊥ x).exists_nat_pow_eq
  refine ⟨m + orderOf c.1.symm, by have := orderOf_pos c.1.symm; omega, ?_⟩
  rw [
    WithHole.isNone_iff_eq_bot, pow_add, Equiv.Perm.mul_apply, pow_orderOf_eq_one,
    symm_pow_apply_eq_bot_iff
  ]
  exact hm.symm
def distanceFromHole (x : WithHole U) : ℕ := Nat.find (exists_distanceFromHole c x)

lemma distanceFromHole_eq_iff (x : WithHole U) (d : ℕ) :
  distanceFromHole c x = d
  ↔ 0 < d                                  -- to the _next_ hole
    ∧ x = (c.1 ^ d) ⊥                      -- hole reached in `d` steps
    ∧ ∀ k, 0 < k → k < d → x ≠ (c.1 ^ k) ⊥ -- no hole reached before that
:= by
  unfold distanceFromHole
  simp only [Nat.find_eq_iff, WithHole.isNone_iff_eq_bot, symm_pow_apply_eq_bot_iff]
  constructor <;> aesop

-- `x` is reached from the hole in exactly `distanceFromHole c x` steps, and not before
lemma distanceFromHole_spec (x : WithHole U) :
  0 < distanceFromHole c x
  ∧ x = (c.1 ^ distanceFromHole c x) ⊥
  ∧ ∀ k, 0 < k → k < distanceFromHole c x → x ≠ (c.1 ^ k) ⊥
:=
  (distanceFromHole_eq_iff c x _).1 rfl

-- length of the cycle, computed as the distance from the hole back to itself
def cycleLength (c : C (WithHole U)) : ℕ := distanceFromHole c ⊥

-- the hole comes back after exactly `cycleLength c` steps, and not before
lemma loopsBackInLength
: ⊥ = (c.1 ^ cycleLength c) ⊥ ∧ ∀ k, 0 < k → k < cycleLength c → ⊥ ≠ (c.1 ^ k) ⊥ :=
  (distanceFromHole_spec c ⊥).2

-- starting from the hole, we are guaranteed to meet every point within one lap
lemma exists_pow_bot (x : WithHole U) : ∃ k < cycleLength c, x = (c.1 ^ k) ⊥ := by
  have hlen : 0 < cycleLength c := (distanceFromHole_spec c ⊥).1
  have hper : Function.IsPeriodicPt c.1 (cycleLength c) ⊥ := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.iterate_eq_pow]
    exact (loopsBackInLength c).1.symm
  obtain ⟨m, hm⟩ := (c.2.2 ⊥ x).exists_nat_pow_eq
  exact ⟨
    m % cycleLength c, Nat.mod_lt _ hlen,
    by rw [← Equiv.Perm.iterate_eq_pow, hper.iterate_mod_apply, Equiv.Perm.iterate_eq_pow, hm]
  ⟩

-- any label (non-hole) is strictly less than a full lap away from the hole
lemma distanceFromHole_lt (u : U) : distanceFromHole c (WithHole.coe u) < cycleLength c := by
  obtain ⟨k, hk, hx⟩ := exists_pow_bot c (WithHole.coe u)
  have hpos : 0 < k :=
    Nat.pos_of_ne_zero
      (fun h0 => by
        subst h0
        simp only [
          WithHole.coe, pow_zero, Bot.bot, Equiv.Perm.coe_one, id_eq, WithHole.mk.injEq,
          reduceCtorEq
        ] at hx
      )
  exact
    lt_of_le_of_lt
      (Nat.find_min'
        _ ⟨hpos, by rw [WithHole.isNone_iff_eq_bot, symm_pow_apply_eq_bot_iff]; exact hx⟩)
      hk

end DistanceFromHole

-- if `u` is reached from the hole in `k` steps (within a lap), its distance is `k`
lemma distanceFromHole_of_pow
  (u : U) {k : ℕ} (hk : k < cycleLength c) (hu : WithHole.coe u = (c.1 ^ k) ⊥)
: distanceFromHole c (WithHole.coe u) = k := by
  -- within a lap, different step counts from the hole land on different points
  have pow_ne : ∀ {i j : ℕ}, i < j → j < cycleLength c → (c.1 ^ i) ⊥ ≠ (c.1 ^ j) ⊥ := by
    intro i j hij hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij -- j = i + d + 1
    rw [Nat.add_assoc, pow_add, Equiv.Perm.mul_apply, Ne, (c.1 ^ i).injective.eq_iff]
    exact (loopsBackInLength c).2 (d + 1) (by omega) (by omega)
  have hlt := distanceFromHole_lt c u
  have heq := (distanceFromHole_spec c _).2.1.symm.trans hu -- σ^dist ⊥ = σ^k ⊥
  -- same point within a lap, so same step count
  exact le_antisymm (not_lt.1 fun h => pow_ne h hlt heq.symm) (not_lt.1 fun h => pow_ne h hk heq)

def unwrap (x : WithHole U) (h : x ≠ ⊥) : U :=
  match hx : x.val with
  | none   => absurd ((WithHole.isNone_iff_eq_bot x).1 (by rw [hx]; rfl)) h
  | some u => u

@[simp] lemma WithHole.coe_unwrap {U} (x : WithHole U) (h : x ≠ ⊥)
: WithHole.coe (unwrap x h) = x := by
  obtain ⟨_ | u⟩ := x
  · exact absurd rfl h
  · rfl

section CycleIndex

-- the position of `u` in the linear order is its distance from the hole - 1
def cycleIndex (u : U) : ℕ := distanceFromHole c (WithHole.coe u) - 1

lemma cycleIndex_lt (u : U) : cycleIndex c u < cycleLength c - 1 := by
  have _ := distanceFromHole_lt c u
  have _ := (distanceFromHole_spec c (WithHole.coe u)).1
  unfold cycleIndex; omega

lemma cycleIndex_spec (u : U) : WithHole.coe u = (c.1 ^ (cycleIndex c u + 1)) ⊥ := by
  unfold cycleIndex
  rw [Nat.sub_add_cancel (distanceFromHole_spec c _).1]
  exact (distanceFromHole_spec c _).2.1

lemma cycleIndex_of_pow
  (u : U) {k : ℕ} (hk : k + 1 < cycleLength c) (hu : WithHole.coe u = (c.1 ^ (k + 1)) ⊥)
: cycleIndex c u = k := by
  unfold cycleIndex; rw [distanceFromHole_of_pow c u hk hu]; rfl

end CycleIndex

def CWithHoleToL (c : C (WithHole U)) : L U where
  card := cycleLength c - 1
  ord  := {
    toFun u  := ⟨cycleIndex c u, cycleIndex_lt c u⟩
    invFun k :=
      unwrap
        ((c.1 ^ (k.val + 1)) ⊥) ((loopsBackInLength c).2 _ (by omega) (by have := k.2; omega)).symm
    left_inv u :=
      WithHole.coe_injective
        (by dsimp only; rw [WithHole.coe_unwrap]; exact (cycleIndex_spec c u).symm)
    right_inv k := Fin.ext (cycleIndex_of_pow c _ (by have := k.2; omega) (WithHole.coe_unwrap _ _))
  }

end CWithHoleToL

lemma permCongr_pow {α β : Type} (e : α ≃ β) (p : Equiv.Perm α) (j : ℕ)
: (e.permCongr p) ^ j = e.permCongr (p ^ j) :=
  (map_pow (MulEquiv.mk' e.permCongr e.permCongr_mul) p j).symm

@[simp] lemma holeEquiv_bot {U} (l : L U) : (holeEquiv l).ord ⊥ = Fin.last l.card := rfl

@[simp] lemma holeEquiv_coe {U} (l : L U) (u : U)
: (holeEquiv l).ord (WithHole.coe u) = (l.ord u).castSucc := by
  simp only [holeEquiv, WithHole.coe]; exact finSuccEquivLast_symm_some _

lemma LToCWithHole_pow_apply (l : L U) (j : ℕ) (x : WithHole U)
: ((LToCWithHole l).1 ^ j) x
  = (holeEquiv l).ord.symm ((finRotate (l.card + 1) ^ j) ((holeEquiv l).ord x))
:= by
  show ((holeEquiv l).ord.symm.permCongr (finRotate _) ^ j) x = _
  rw [permCongr_pow, Equiv.permCongr_apply, Equiv.symm_symm]

-- `k + 1` steps from the hole land on the `k`-th label
lemma LToCWithHole_pow_succ_bot (l : L U) (k : ℕ) (hk : k < l.card)
: ((LToCWithHole l).1 ^ (k + 1)) ⊥ = WithHole.coe (l.ord.symm ⟨k, hk⟩) := by
  rw [
    LToCWithHole_pow_apply, holeEquiv_bot, Equiv.symm_apply_eq, holeEquiv_coe,
    Equiv.apply_symm_apply
  ]
  apply Fin.ext
  rw [
    finRotate_pow_val, Fin.val_last, Fin.val_castSucc,
    show l.card + (k + 1) = k + (l.card + 1) by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)
  ]

-- `card + 1` steps from the hole come back to it
lemma LToCWithHole_pow_period (l : L U) : ((LToCWithHole l).1 ^ (l.card + 1)) ⊥ = ⊥ := by
  rw [LToCWithHole_pow_apply, holeEquiv_bot, Equiv.symm_apply_eq, holeEquiv_bot]
  apply Fin.ext
  rw [finRotate_pow_val, Fin.val_last, Nat.add_mod_right, Nat.mod_eq_of_lt (Nat.lt_succ_self _)]

lemma L.ext_of_symm {U} {l₁ l₂ : L U} (h : l₁.card = l₂.card)
  (h' : ∀ k (hk₁ : k < l₁.card) (hk₂ : k < l₂.card), l₁.ord.symm ⟨k, hk₁⟩ = l₂.ord.symm ⟨k, hk₂⟩)
: l₁ = l₂ := by
  obtain ⟨n₁, e₁⟩ := l₁; obtain ⟨n₂, e₂⟩ := l₂
  dsimp only at h h'; subst h
  congr 1
  have hs : e₁.symm = e₂.symm := Equiv.ext fun k => h' k k.2 k.2
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm hs

lemma cycleLength_eq
  (c : C (WithHole U)) {n : ℕ}
  (h : 0 < n ∧ ⊥ = (c.1 ^ n) ⊥ ∧ ∀ k, 0 < k → k < n → ⊥ ≠ (c.1 ^ k) ⊥)
: cycleLength c = n :=
  (distanceFromHole_eq_iff c ⊥ n).2 h

lemma LToCWithHole_spec (l : L U) :
  0 < l.card + 1
  ∧ ⊥ = ((LToCWithHole l).1 ^ (l.card + 1)) ⊥
  ∧ ∀ k, 0 < k → k < l.card + 1 → ⊥ ≠ ((LToCWithHole l).1 ^ k) ⊥
:= ⟨
  Nat.succ_pos _,
  (LToCWithHole_pow_period l).symm, fun k hk1 hk2 heq => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [LToCWithHole_pow_succ_bot l j (by omega)] at heq
    simp only [Bot.bot, WithHole.coe, WithHole.mk.injEq, reduceCtorEq] at heq
⟩

lemma LToC_CToL_pow_bot (c : C (WithHole U)) (j : ℕ) (hj : j ≤ cycleLength c)
: ((LToCWithHole (CWithHoleToL c)).1 ^ j) ⊥ = (c.1 ^ j) ⊥ := by
  have hpos : 0 < cycleLength c := (distanceFromHole_spec c ⊥).1
  rcases j with _ | k
  · simp only [pow_zero, Equiv.Perm.coe_one, id_eq]
  · rcases Nat.lt_or_ge k (cycleLength c - 1) with hk | hk
    · rw [LToCWithHole_pow_succ_bot _ k hk]
      show WithHole.coe (unwrap _ _) = _
      rw [WithHole.coe_unwrap]
    · have hk' : k = (CWithHoleToL c).card := by (show k = cycleLength c - 1; omega)
      subst hk'
      rw [
        LToCWithHole_pow_period,
        show (CWithHoleToL c).card + 1 = cycleLength c by (show cycleLength c - 1 + 1 = _; omega)
      ]
      exact (loopsBackInLength c).1

def derivCycleEquivLinearOrder : Deriv C U ≃ L U where
  toFun  := by unfold Deriv; intro c; exact CWithHoleToL c
  invFun := by unfold Deriv; intro l; exact LToCWithHole l
  right_inv := by
    intro l; dsimp only [id]
    apply L.ext_of_symm
    · show cycleLength _ - 1 = l.card; rw [cycleLength_eq _ (LToCWithHole_spec l)]; rfl
    · intro k hk₁ hk₂
      apply WithHole.coe_injective; show WithHole.coe (unwrap _ _) = _; rw [WithHole.coe_unwrap]
      exact LToCWithHole_pow_succ_bot l k hk₂
  left_inv := by
    intro c; dsimp only [id]
    apply Subtype.ext; ext x
    obtain ⟨j, hj, rfl⟩ := exists_pow_bot c x
    conv_lhs => rw [← LToC_CToL_pow_bot c j hj.le]
    rw [
      ← Equiv.Perm.mul_apply, ← pow_succ', LToC_CToL_pow_bot c (j + 1) hj, pow_succ',
      Equiv.Perm.mul_apply
    ]

def derivCycleIsoLinearOrder : Iso (Deriv C) L where
  equiv      U   := derivCycleEquivLinearOrder
  naturality σ s := by
    sorry

end Species
end
