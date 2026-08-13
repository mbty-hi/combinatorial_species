import Species.Basic
import Species.Operations.Mul
import Species.Instances.One
import Species.Instances.Zero

namespace Species

def zero_mul {S: Type → Type} [Species S] {U} [Finite U] : Species.mul SZero S U
≃ SZero U where
  toFun := by
    unfold mul
    rintro ⟨d,⟨⟩,bar⟩
  invFun := by
    unfold mul
    rintro ⟨⟩
  left_inv := by rintro ⟨d,⟨⟩, bar⟩
  right_inv := by rintro ⟨d,⟨⟩, bar⟩

def mul_zero {S: Type → Type} [Species S] {U} [Finite U] : Species.mul S SZero U
≃ SZero U where
  toFun := by
    unfold mul
    rintro ⟨d,foo,⟨⟩⟩
  invFun := by
    unfold mul
    rintro ⟨⟩
  left_inv := by rintro ⟨d,foo,⟨⟩⟩
  right_inv := by rintro ⟨d,foo,⟨⟩⟩

def mul_comm {F G : Type → Type} [Species F] [Species G] {U} [Finite U] :
Species.mul F G U ≃ Species.mul G F U where
  toFun := by
    unfold mul
    rintro ⟨d,Fstrut,Gstrut⟩
    refine ⟨fun x => !(d x), ?_, ?_⟩
    . simp; exact Gstrut
    . simp; exact Fstrut
  invFun := by
    unfold mul
    rintro ⟨d,Gstrut,Fstrut⟩
    refine ⟨fun x => !(d x), ?_, ?_⟩
    . simp; exact Fstrut
    . simp; exact Gstrut
  left_inv := by
    rintro ⟨d,Fstrut, Gstrut⟩
    simp
    congr <;> simp
  right_inv := by
    rintro ⟨d, Gstrut, Fstrut⟩
    simp
    congr <;> simp

/- `(mul SOne S) U` is a partitioning of `U` by a boolean predicate `d`. The set of labels making
   `d` true carries an `SOne`-structure, and its complement carries an `S`-structure. Since there
   are no `SOne`-structures for nonempty label sets, `d` must return `false` for all inputs. The
   isomorphism is therefore mostly about transport of the `S`-structure along
   `{u : U // d u = false} ≃ U`. -/
def one_mul {S: Type → Type} [Species S] {U} [Finite U] : (mul SOne S) U ≃ S U where
  toFun := by
    rintro ⟨d, one, s⟩
    have d_is_false : ∀u, d u = false := by -- we show that `d` must be `fun _ => false` (pointwise)
      intro u; rcases h : d u; rfl; nomatch (one ⟨u, h⟩)
    have equiv : {u // d u = false} ≃ U := Equiv.subtypeUnivEquiv d_is_false
    exact transportEquiv equiv s

  /- We must be very careful about how we write this function. Indeed,
     `{u // (fun _ => false) u = true}` and `{u // False}`, though equivalent, are different types
     (same goes for `{u // (fun _ => false) u = false}` and `{u // True}`). Being too eager with
     simplifications would force us to use `HEq` in `left_inv`, which is doable but more painful
     than being careful here. -/
  invFun := by
    intros s; unfold mul SOne
    refine ⟨fun _ => false, ?one, ?s⟩ -- we define `d` as `fun _ => false`
    case one => intros x; nomatch x   -- nothing ends up in the set carrying an `SOne`-structure
    case s   =>
      have equiv : {u // false = false} ≃ U := Equiv.subtypeUnivEquiv (by simp)
      exact transportEquiv equiv.symm s

  left_inv := by
    rintro ⟨d, one, s⟩
    have d_is_false : d = fun _ => false := by
      funext u; rcases h : d u; rfl; nomatch one ⟨u, h⟩
    subst d_is_false; simp; congr 2
    · funext x; nomatch x
    · rw [transportEquiv_symm, Equiv.symm_apply_apply]

  right_inv := by intros _; simp [transportEquiv_symm, Equiv.apply_symm_apply]

/- Same logic as `one_mul`, except for some flipped branches. See above for comments. -/
def mul_one {S : Type → Type} [Species S] {U} [Finite U] : (mul S SOne) U ≃ S U where
  toFun := by
    rintro ⟨d, s, one⟩
    have d_is_true : ∀u, d u = true := by -- we show that `d` must be `fun _ => true` (pointwise)
      intro u; rcases h : d u; nomatch (one ⟨u, h⟩); rfl
    have equiv : {u // d u = true} ≃ U := Equiv.subtypeUnivEquiv d_is_true
    exact transportEquiv equiv s

  invFun := by
    intros s; unfold mul SOne
    refine ⟨fun _ => true, ?s, ?one⟩ -- we define `d` as `fun _ => true`
    case s   =>
      have equiv : {u // true = true} ≃ U := Equiv.subtypeUnivEquiv (by simp)
      exact transportEquiv equiv.symm s
    case one => intros x; nomatch x  -- nothing ends up in the set carrying an `SOne`-structure

  left_inv := by
    rintro ⟨d, s, one⟩
    have d_is_true : d = fun _ => true := by
      funext u; rcases h : d u; nomatch one ⟨u, h⟩; rfl
    subst d_is_true; simp; congr 2
    · rw [transportEquiv_symm, Equiv.symm_apply_apply]
    · funext x; nomatch x

  right_inv := by intros _; simp [transportEquiv_symm, Equiv.apply_symm_apply]

--        c₁             d₁          The left branch is taken when the function returns false
--       / \            / \          The right branch is taken when the function returns true
--     c₂   \          /   d₂
--    /  \   \        /   /  \
-- ((S₁)(S₂))(S₃)  (S₁)((S₂)(S₃))

/- Basically, we need to express c₁ and c₂ in terms of d₁ and d₂, and vice versa. The difficulty is
   that c₂ and d₂ are dependent functions that are parameterized on c₁ having returned false, and d₁
   having returned true, respectively. -/

@[simp]
def d_to_c₁ {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = true} → Bool) : U → Bool :=
  fun x => if h : d₁ x = true then d₂ ⟨x, h⟩ else false

@[simp]
def c_to_d₁ {U} (c₁ : U → Bool) (c₂ : {u // c₁ u = false} → Bool) :=
  fun x => if h : c₁ x = false then c₂ ⟨x, h⟩ else true

def mul_assoc : … := mulMul_equiv_mul3.trans mul_mulMul_equiv_mul3.symm

def assocEquiv₁ {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = true} → Bool)
: {y : {u // d₁ u = true} // d₂ y = true} ≃ {u // assocDecider d₁ d₂ u = true} :=
  (Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
    (Equiv.subtypeEquivRight fun u => by by_cases h : d₁ u = true <;> simp [assocDecider, h])

def assocEquiv₂ {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = true} → Bool)
: {y : {u // assocDecider d₁ d₂ u = false} // d₁ y.val = true}
  ≃ {y : {u // d₁ u = true} // d₂ y = false}
:=
  ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
    (Equiv.subtypeEquivRight fun u => by by_cases h : d₁ u = true <;> simp [assocDecider, h])
  ).trans
  (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm

def assocEquiv₃ {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = true} → Bool)
: {y : {u // assocDecider d₁ d₂ u = false} // d₁ y.val = false} ≃ {u // d₁ u = false} :=
  (Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
    (Equiv.subtypeEquivRight fun u => by
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by simp [assocDecider, h], h⟩)

def invEquiv₁ {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = false} → Bool)
: {y : {u // invDecider d₁ d₂ u = true} // d₁ y.val = true} ≃ {u // d₁ u = true} :=
  (Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
    (Equiv.subtypeEquivRight fun u => by
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by simp [invDecider, h], h⟩)

def invEquiv₂ {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = false} → Bool)
: {y : {u // invDecider d₁ d₂ u = true} // d₁ y.val = false}
  ≃ {y : {u // d₁ u = false} // d₂ y = true}
:=
  ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
    (Equiv.subtypeEquivRight fun u => by by_cases h : d₁ u = false <;> simp [invDecider, h])
  ).trans
    (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm

def invEquiv₃ {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = false} → Bool)
: {u // invDecider d₁ d₂ u = false} ≃ {y : {u // d₁ u = false} // d₂ y = false} :=
  (Equiv.subtypeEquivRight fun u => by by_cases h : d₁ u = false <;> simp [invDecider, h]).trans
  (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm

lemma mul_mk_congr
  {S T : Type → Type} [Species S] [Species T] {U} [Finite U]
  {d d' : U → Bool} (hd : d = d')
  {s : S {u // d u = true}} {s' : S {u // d' u = true}}
  {t : T {u // d u = false}} {t' : T {u // d' u = false}}
  (hs : HEq s s') (ht : HEq t t')
: (⟨d, s, t⟩ : mul S T U) = ⟨d', s', t'⟩ := by
  subst hd; rw [eq_of_heq hs, eq_of_heq ht]

/- Helper A: a composite transport along a val-preserving round trip is
   heterogeneously the identity. Packages transport_trans + transport_id + Equiv.ext. -/
theorem transport_comp_heq {S : Type → Type} [Species S] {α β : Type}
    [Finite α] [Finite β] {γ : Type} [Finite γ]
    (e₁ : α ≃ β) (e₂ : β ≃ γ) (h : γ = α)
    (hval : ∀ a, HEq ((e₁.trans e₂) a) a) (s : S α) :
    HEq (Species.transport e₂ (Species.transport e₁ s)) s := by
  rw [show Species.transport e₂ (Species.transport e₁ s)
        = Species.transport (e₁.trans e₂) s from
      (Species.transport_trans e₁ e₂ s).symm]
  subst h
  rw [show e₁.trans e₂ = Equiv.refl γ from Equiv.ext fun a => eq_of_heq (hval a),
      Species.transport_id]

/-- Equiv between subtypes induced by a decider equality. Val-preserving by construction. -/
def deciderCast {U : Type} {d d' : U → Bool} (h : d = d') (b : Bool) :
    {u // d u = b} ≃ {u // d' u = b} :=
  Equiv.subtypeEquivRight fun u => by rw [h]

@[simp] theorem deciderCast_rfl {U : Type} (d : U → Bool) (b : Bool) :
    deciderCast (rfl : d = d) b = Equiv.refl _ :=
  Equiv.ext fun _ => Subtype.ext rfl

theorem mul_ext {S T : Type → Type} [Species S] [Species T] {U} [Finite U]
    {d d' : U → Bool} {s : S _} {s' : S _} {t : T _} {t' : T _}
    (hd : d = d')
    (hs : Species.transport (deciderCast hd true) s = s')
    (ht : Species.transport (deciderCast hd false) t = t') :
    (⟨d, (s, t)⟩ : mul S T U) = ⟨d', (s', t')⟩ := by
  subst hd
  simp only [deciderCast_rfl, Species.transport_id] at hs ht
  rw [hs, ht]

def mul_assoc {S₁ S₂ S₃ : Type → Type} [Species S₁] [Species S₂] [Species S₃] {U} [Finite U]
: (mul (mul S₁ S₂) S₃) U ≃ (mul S₁ (mul S₂ S₃)) U where
  toFun := by
    rintro ⟨d₁, ⟨⟨d₂, ⟨s₁, s₂⟩⟩, s₃⟩⟩
    refine ⟨?d₁, ⟨?s₁, ⟨?d₂, ⟨?s₂, ?s₃⟩⟩⟩⟩
    case d₁ => exact (fun x => if h : d₁ x = true then d₂ ⟨x, h⟩ else false)
    case d₂ => exact (fun x => d₁ x.val)
    case s₁ => exact Species.transport (assocEquiv₁ d₁ d₂) s₁
    case s₂ => exact Species.transport (assocEquiv₂ d₁ d₂).symm s₂
    case s₃ => exact Species.transport (assocEquiv₃ d₁ d₂).symm s₃

  invFun := by
    rintro ⟨d₁, ⟨s₁, ⟨d₂, ⟨s₂, s₃⟩⟩⟩⟩
    refine ⟨?d₁', ⟨⟨?d₂', ⟨?s₁', ?s₂'⟩⟩, ?s₃'⟩⟩
    . exact (fun x => if h : d₁ x = false then d₂ ⟨x, h⟩ else true)
    . exact (fun x => d₁ x)
    · exact Species.transport (invEquiv₁ d₁ d₂).symm s₁
    · exact Species.transport (invEquiv₂ d₁ d₂).symm s₂
    · exact Species.transport (invEquiv₃ d₁ d₂).symm s₃

  left_inv := by
    rintro ⟨d₁, ⟨⟨d₂, s₁, s₂⟩, s₃⟩⟩
    dsimp only
    have hD :
      (fun x => if h : (if h : d₁ x = true then d₂ ⟨x, h⟩ else false) = false then d₁ x else true)
      = d₁ := by
        funext x
        by_cases h₁ : d₁ x = true
        · by_cases h₂ : d₂ ⟨x, h₁⟩ = true <;> simp [h₁, h₂]
        · simp [h₁]
    refine Sigma.ext hD ?_
    congr! 1
    refine mul_ext hD ?_ ?_
    · refine mul_ext hd₂ ?_ ?_    -- hd₂ : inner decider = d₂, transported along deciderCast hD true
      · -- transport (deciderCast hd₂ true) (transport (deciderCast hD true) (transport (invEquiv₁ …).symm (transport (assocEquiv₁ …) s₁))) = s₁
        exact transport_roundtrip4 …
      · exact transport_roundtrip4 …
    · -- transport (deciderCast hD false) (transport (invEquiv₃ …).symm (transport (assocEquiv₃ …).symm s₃)) = s₃
      exact transport_roundtrip3 …

  right_inv := by
    rintro ⟨d₁, ⟨s₁, ⟨d₂, ⟨s₂, s₃⟩⟩⟩⟩
    dsimp only
    sorry

end Species
