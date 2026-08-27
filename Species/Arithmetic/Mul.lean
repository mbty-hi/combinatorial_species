import Species.Basic
import Species.Operations.Mul
import Species.Instances.One
import Species.Instances.Zero
import Mathlib.Tactic.FinCases

namespace Species

def zero_mul {S: Type → Type} [Species S] {U} [Finite U] : Species.mul SZero S U ≃ SZero U where
  toFun     := by unfold mul; rintro ⟨d,⟨⟩,bar⟩
  invFun    := by unfold mul; rintro ⟨⟩
  left_inv  := by rintro ⟨d,⟨⟩, bar⟩
  right_inv := by rintro ⟨d,⟨⟩, bar⟩

def mul_zero {S: Type → Type} [Species S] {U} [Finite U] : Species.mul S SZero U ≃ SZero U where
  toFun     := by unfold mul; rintro ⟨d,foo,⟨⟩⟩
  invFun    := by unfold mul; rintro ⟨⟩
  left_inv  := by rintro ⟨d,foo,⟨⟩⟩
  right_inv := by rintro ⟨d,foo,⟨⟩⟩

def mul_comm {F G : Type → Type} [Species F] [Species G] {U} [Finite U]
: Species.mul F G U ≃ Species.mul G F U where
  toFun := by
    unfold mul; rintro ⟨d,Fstrut,Gstrut⟩
    refine ⟨fun x => !(d x), ?_, ?_⟩ <;> simp
    . exact Gstrut
    . exact Fstrut
  invFun := by
    unfold mul; rintro ⟨d,Gstrut,Fstrut⟩
    refine ⟨fun x => !(d x), ?_, ?_⟩ <;> simp
    . exact Fstrut
    . exact Gstrut
  left_inv  := by rintro ⟨d, Fstrut, Gstrut⟩; simp; congr <;> simp
  right_inv := by rintro ⟨d, Gstrut, Fstrut⟩; simp; congr <;> simp

/- `(mul SOne S) U` is a partitioning of `U` by a boolean predicate `d`. The set of labels making
   `d` false carries an `SOne`-structure, and its complement carries an `S`-structure. Since there
   are no `SOne`-structures for nonempty label sets, `d` must return `true` for all inputs. The
   isomorphism is therefore mostly about transport of the `S`-structure along
   `{u : U // d u = true} ≃ U`. -/
def one_mul {S: Type → Type} [Species S] {U} [Finite U] : (mul SOne S) U ≃ S U where
  toFun := by
    rintro ⟨d, one, s⟩
    have d_is_true : ∀u, d u = true := by -- we show that `d` must be `fun _ => true` (pointwise)
      intro u; rcases h : d u; nomatch (one ⟨u, h⟩); rfl
    have equiv : {u // d u = true} ≃ U := Equiv.subtypeUnivEquiv d_is_true
    exact transportEquiv equiv s

  /- We must be very careful about how we write this function. Indeed,
     `{u // (fun _ => true) u = false}` and `{u // False}`, though equivalent, are different types
     (same goes for `{u // (fun _ => true) u = true}` and `{u // True}`). Being too eager with
     simplifications would force us to use `HEq` in `left_inv`, which is doable but more painful
     than being careful here. -/
  invFun := by
    intros s; unfold mul SOne
    refine ⟨fun _ => true, ?one, ?s⟩ -- we define `d` as `fun _ => false`
    case one => intros x; nomatch x  -- nothing ends up in the set carrying an `SOne`-structure
    case s   =>
      have equiv : {u // true = true} ≃ U := Equiv.subtypeUnivEquiv (by simp)
      exact transportEquiv equiv.symm s

  left_inv := by
    rintro ⟨d, one, s⟩
    have d_is_true : d = fun _ => true := by
      funext u; rcases h : d u; nomatch one ⟨u, h⟩; rfl
    subst d_is_true; simp; congr 2
    · funext x; nomatch x
    · rw [transportEquiv_symm, Equiv.symm_apply_apply]

  right_inv := by intros _; simp [transportEquiv_symm, Equiv.apply_symm_apply]

/- Same logic as `one_mul`, except for some flipped branches. See above for more substantial
   comments. -/
def mul_one {S : Type → Type} [Species S] {U} [Finite U] : (mul S SOne) U ≃ S U where
  toFun := by
    rintro ⟨d, s, one⟩
    have d_is_false : ∀u, d u = false := by -- we show that `d` must be `fun _ => false` (pointwise)
      intro u; rcases h : d u; rfl; nomatch (one ⟨u, h⟩)
    have equiv : {u // d u = false} ≃ U := Equiv.subtypeUnivEquiv d_is_false
    exact transportEquiv equiv s

  invFun := by
    intros s; unfold mul SOne
    refine ⟨fun _ => false, ?s, ?one⟩ -- we define `d` as `fun _ => false`
    case s =>
      have equiv : {u // false = false} ≃ U := Equiv.subtypeUnivEquiv (by simp)
      exact transportEquiv equiv.symm s
    case one => intros x; nomatch x -- nothing ends up in the set carrying an `SOne`-structure

  left_inv := by
    rintro ⟨d, s, one⟩
    have d_is_false : d = fun _ => false := by
      funext u; rcases h : d u; rfl; nomatch one ⟨u, h⟩
    subst d_is_false; simp; congr 2
    · rw [transportEquiv_symm, Equiv.symm_apply_apply]
    · funext x; nomatch x

  right_inv := by intros _; simp [transportEquiv_symm, Equiv.apply_symm_apply]

--        C            D
--        c₁           d₁          The left branch is taken when the function returns false
--       / \          / \          The right branch is taken when the function returns true
--     c₂   \        /   d₂
--    / \    \      /   / \
--  (S₁×S₂) × S₃  S₁ × (S₂×S₃)

/- Basically, we need to express c₁ and c₂ in terms of d₁ and d₂, and vice versa. The difficulty is
   that c₂ and d₂ are dependent functions that are parameterized on c₁ having returned false, and d₁
   having returned true, respectively. To make things conceptually easier, we go through `Mul₃`, an
   intermediate, flat representation with a single decision function yielding a Fin 3. We then have
   to define two simpler mappings: one between C and Mul₃ and one between D and Mul₃ (a direct proof
   would be terser). -/

def Mul₃ (S₀ S₁ S₂: Type → Type) (U: Type) : Type :=
  Σ d : U → Fin 3, S₀ {u // d u = 0} × S₁ {u // d u = 1} × S₂ {u // d u = 2}

--       Mul₃
--        d        Left branch when d returns 0
--      / |\       Middle branch when d returns 1
--     /  | \      Right branch when d returns 2
--    /   |  \
-- (S₁ × S₂ × S₃)

-- Manual ext lemma for Mul₃
def colorCast {U : Type} {c c' : U → Fin 3} (h : c = c') (k : Fin 3)
: {u // c u = k} ≃ {u // c' u = k} :=
  Equiv.subtypeEquivRight fun u => by rw [h]

@[simp] theorem colorCast_rfl {U : Type} (c : U → Fin 3) (k : Fin 3)
: colorCast (rfl : c = c) k = Equiv.refl _ :=
  Equiv.ext fun _ => Subtype.ext rfl

theorem Mul₃_ext {S₀ S₁ S₂ : Type → Type} [Species S₀] [Species S₁] [Species S₂]
  {U : Type} [Finite U] {d d' : U → Fin 3}
  {s₀ : S₀ {u // d u = 0}} {s₀' : S₀ {u // d' u = 0}}
  {s₁ : S₁ {u // d u = 1}} {s₁' : S₁ {u // d' u = 1}}
  {s₂ : S₂ {u // d u = 2}} {s₂' : S₂ {u // d' u = 2}}
  (hd : d = d')
  (h₀ : Species.transport (colorCast hd 0) s₀ = s₀')
  (h₁ : Species.transport (colorCast hd 1) s₁ = s₁')
  (h₂ : Species.transport (colorCast hd 2) s₂ = s₂') :
  (⟨d, (s₀, s₁, s₂)⟩ : Mul₃ S₀ S₁ S₂ U) = ⟨d', (s₀', s₁', s₂')⟩
:= by
  subst hd
  simp only [colorCast_rfl, Species.id_transport] at h₀ h₁ h₂
  rw [h₀, h₁, h₂]

-- Functions to switch between (d₁, d₂) and d
@[simp] def d_to_d₁ {U} (d: U → Fin 3) : U → Bool := fun u => d u != 0
@[simp] def d_to_d₂ {U} (d: U → Fin 3) : (u: {u // d_to_d₁ d u = true}) → Bool :=
  fun ⟨u, _⟩ => d u == 2

@[simp]
def d₁₂_to_d {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = true} → Bool) : U → Fin 3 :=
  fun u =>
    if h : d₁ u = true
    then if d₂ ⟨u, h⟩ then 2 else 1
    else 0

-- Results about the composition of the above functions
@[simp] theorem d_inv {U} (d : U → Fin 3) : d₁₂_to_d (d_to_d₁ d) (d_to_d₂ d) = d := by
  funext u; match hu : d u with
  | 0 => simp [d₁₂_to_d, d_to_d₁, hu]
  | 1 => simp [d₁₂_to_d, d_to_d₁, d_to_d₂, hu]
  | 2 => simp [d₁₂_to_d, d_to_d₁, d_to_d₂, hu]

@[simp] theorem d₁_inv {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = true} → Bool)
: d_to_d₁ (d₁₂_to_d d₁ d₂) = d₁ := by
  funext u; by_cases h₁ : d₁ u = true
  . by_cases h₂ : d₂ ⟨u, h₁⟩ = true <;> simp [h₁, h₂, d_to_d₁, d₁₂_to_d]
  . simp [h₁, d_to_d₁, d₁₂_to_d]

@[simp] theorem d₂_inv {U} (d₁ : U → Bool) (d₂ : {u // d₁ u = true} → Bool)
: (fun y => d_to_d₂ (d₁₂_to_d d₁ d₂) ((deciderCast (d₁_inv d₁ d₂) true).symm y)) = d₂ := by
  funext ⟨u, h₁⟩
  by_cases h₂ : d₂ ⟨u, h₁⟩ = true <;> simp [h₁, h₂, d_to_d₂, d₁₂_to_d, deciderCast]

def Mul₃_equiv₁
  {S₁ S₂ S₃ : Type → Type} [Species S₁] [Species S₂] [Species S₃] {U} [Finite U]
: (mul S₁ (mul S₂ S₃)) U ≃ Mul₃ S₁ S₂ S₃ U where
  toFun := by
    rintro ⟨d₁, s₁, ⟨d₂, s₂, s₃⟩⟩
    refine ⟨?d, ⟨?s₁, ?s₂, ?s₃⟩⟩
    case d  => apply d₁₂_to_d d₁ d₂
    case s₁ =>
      have equiv : {u // d₁ u = false} ≃ {u // d₁₂_to_d d₁ d₂ u = 0} :=
        Equiv.subtypeEquivRight
          (fun u => by
            by_cases h₁ : d₁ u = true <;> simp [h₁]; by_cases h₂ : d₂ ⟨u, h₁⟩ <;> simp [h₂]
          )
      exact Species.transport equiv s₁
    case s₂ =>
      have equiv : {u // d₂ u = false} ≃ {u // d₁₂_to_d d₁ d₂ u = 1} :=
        (Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
          (Equiv.subtypeEquivRight fun u => by
            constructor
            . rintro ⟨h₁, h₂⟩; simp [h₁, h₂]
            . intro h; by_cases h₁ : d₁ u = true
              . refine ⟨h₁, ?_⟩; by_cases h₂ : d₂ ⟨u, h₁⟩ <;> simp_all
              . simp [h₁] at h)
      exact Species.transport equiv s₂
    case s₃ =>
      have equiv : {u // d₂ u = true} ≃ {u // d₁₂_to_d d₁ d₂ u = 2} :=
        (Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
          (Equiv.subtypeEquivRight fun u => by
            constructor
            . rintro ⟨h₁, h₂⟩; simp [h₁, h₂]
            . intro h; by_cases h₁ : d₁ u = true
              . refine ⟨h₁, ?_⟩; by_cases h₂ : d₂ ⟨u, h₁⟩ <;> simp_all
              . simp [h₁] at h)
      exact Species.transport equiv s₃

  invFun := by
    rintro ⟨d, ⟨s₁, s₂, s₃⟩⟩
    refine ⟨?d₁', ?s₁', ⟨?d₂', ?s₂', ?s₃'⟩⟩
    case d₁' => exact d_to_d₁ d
    case d₂' => exact d_to_d₂ d
    case s₁' =>
      have equiv : {u // d u = 0} ≃ {u // d_to_d₁ d u = false} :=
        Equiv.subtypeEquivRight (fun u => by simp)
      exact Species.transport equiv s₁
    case s₂' =>
      have equiv : {u // d u = 1} ≃ {u // d_to_d₂ d u = false} :=
        (Equiv.subtypeEquivRight
          (fun u => by
            constructor
            · intro h; constructor <;> simp [h]
            · rintro ⟨h₁, h₂⟩; simp at *; generalize hu : d u = x; fin_cases x <;> simp [hu] at *
          )
        ).trans
        (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm
      exact Species.transport equiv s₂
    case s₃' =>
      have equiv : {u // d u = 2} ≃ {u // d_to_d₂ d u = true} :=
        (Equiv.subtypeEquivRight
          (fun u => by
            constructor
            . intro h; constructor <;> simp [h]
            . rintro ⟨h₁, h₂⟩; simp at *; generalize hu : d u = x; fin_cases x <;> simp [hu] at *
          )
        ).trans
        (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm
      exact Species.transport equiv s₃

  left_inv := by
    simp; rintro ⟨d₁, s₁, ⟨d₂, s₂, s₃⟩⟩; simp
    refine mul_ext (S := S₁) (T := mul S₂ S₃) (d₁_inv d₁ d₂) ?_ ?_
    . simp [transport_transport]
      exact transport_eq_self_of_val _ (fun a => Subtype.ext rfl) s₁
    · simp [mul_transport_mk]
      refine mul_ext (S := S₂) (T := S₃) ?_ ?_ ?_ <;> try simp [transport_transport]
      . apply d₂_inv
      . exact transport_eq_self_of_val _ (fun a => Subtype.ext (Subtype.ext rfl)) s₂
      . exact transport_eq_self_of_val _ (fun a => Subtype.ext (Subtype.ext rfl)) s₃

  right_inv := by
    simp; rintro ⟨d, s₁, s₂, s₃⟩; simp
    refine Mul₃_ext (d_inv d) ?_ ?_ ?_ <;> simp [transport_transport]
    . exact transport_eq_self_of_val _ (fun a => Subtype.ext rfl) s₁
    . exact transport_eq_self_of_val _ (fun a => Subtype.ext rfl) s₂
    . exact transport_eq_self_of_val _ (fun a => Subtype.ext rfl) s₃

-- Functions to switch between (d₁, d₂) and d
@[simp] def d_to_c₁ {U} (d: U → Fin 3) : U → Bool := fun u => d u == 2
@[simp] def d_to_c₂ {U} (d: U → Fin 3) : (u: {u // d_to_c₁ d u = false}) → Bool :=
  fun ⟨u, _⟩ => d u == 1

@[simp]
def c₁₂_to_d {U} (c₁ : U → Bool) (c₂ : {u // c₁ u = false} → Bool) : U → Fin 3 :=
  fun u =>
    if h : c₁ u = false
    then if c₂ ⟨u, h⟩ then 1 else 0
    else 2

-- Results about the composition of the above functions
@[simp] theorem d_inv' {U} (d : U → Fin 3) : c₁₂_to_d (d_to_c₁ d) (d_to_c₂ d) = d := by
  funext u; match hu : d u with
  | 0 => simp [c₁₂_to_d, d_to_c₁, d_to_c₂, hu]
  | 1 => simp [c₁₂_to_d, d_to_c₁, d_to_c₂, hu]
  | 2 => simp [c₁₂_to_d, d_to_c₁, hu]

@[simp] theorem c₁_inv {U} (c₁ : U → Bool) (c₂ : {u // c₁ u = false} → Bool)
: d_to_c₁ (c₁₂_to_d c₁ c₂) = c₁ := by
  funext u; by_cases h₁ : c₁ u = false
  . by_cases h₂ : c₂ ⟨u, h₁⟩ = true <;> simp [h₁, h₂, d_to_c₁, c₁₂_to_d]
  . simp [h₁, d_to_c₁, c₁₂_to_d]

@[simp] theorem c₂_inv {U} (c₁ : U → Bool) (c₂ : {u // c₁ u = false} → Bool)
: (fun y => d_to_c₂ (c₁₂_to_d c₁ c₂) ((deciderCast (c₁_inv c₁ c₂) false).symm y)) = c₂ := by
  funext ⟨u, h₁⟩
  by_cases h₂ : c₂ ⟨u, h₁⟩ = true <;> simp [h₁, h₂, d_to_c₂, c₁₂_to_d, deciderCast]

def Mul₃_equiv₂
  {S₁ S₂ S₃ : Type → Type} [Species S₁] [Species S₂] [Species S₃] {U} [Finite U]
: (mul (mul S₁ S₂) S₃) U ≃ Mul₃ S₁ S₂ S₃ U where
  toFun := by
    rintro ⟨c₁, ⟨c₂, s₁, s₂⟩, s₃⟩
    refine ⟨?d, ⟨?s₁, ?s₂, ?s₃⟩⟩
    case d  => apply c₁₂_to_d c₁ c₂
    case s₁ =>
      have equiv : {u // c₂ u = false} ≃ {u // c₁₂_to_d c₁ c₂ u = 0} :=
        (Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
          (Equiv.subtypeEquivRight fun u => by
            constructor
            . rintro ⟨h₁, h₂⟩; simp [h₁, h₂]
            . intro h; by_cases h₁ : c₁ u = false
              . refine ⟨h₁, ?_⟩; by_cases h₂ : c₂ ⟨u, h₁⟩ <;> simp_all
              . simp [h₁] at h)
      exact Species.transport equiv s₁
    case s₂ =>
      have equiv : {u // c₂ u = true} ≃ {u // c₁₂_to_d c₁ c₂ u = 1} :=
        (Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
          (Equiv.subtypeEquivRight fun u => by
            constructor
            . rintro ⟨h₁, h₂⟩; simp [h₁, h₂]
            . intro h; by_cases h₁ : c₁ u = false
              . refine ⟨h₁, ?_⟩; by_cases h₂ : c₂ ⟨u, h₁⟩ <;> simp_all
              . simp [h₁] at h)
      exact Species.transport equiv s₂
    case s₃ =>
      have equiv : {u // c₁ u = true} ≃ {u // c₁₂_to_d c₁ c₂ u = 2} :=
        Equiv.subtypeEquivRight
          (fun u => by
            by_cases h₁ : c₁ u = false <;> simp [h₁]; by_cases h₂ : c₂ ⟨u, h₁⟩ <;> simp [h₂]
          )
      exact Species.transport equiv s₃

  invFun := by
    rintro ⟨d, ⟨s₁, s₂, s₃⟩⟩
    refine ⟨?c₁', ⟨?c₂', ?s₁', ?s₂'⟩, ?s₃'⟩
    case c₁' => exact d_to_c₁ d
    case c₂' => exact d_to_c₂ d
    case s₁' =>
      have equiv : {u // d u = 0} ≃ {u // d_to_c₂ d u = false} :=
        (Equiv.subtypeEquivRight
          (fun u => by
            constructor
            · intro h; constructor <;> simp [h]
            · rintro ⟨h₁, h₂⟩; simp at *; generalize hu : d u = x; fin_cases x <;> simp [hu] at *
          )
        ).trans
        (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm
      exact Species.transport equiv s₁
    case s₂' =>
      have equiv : {u // d u = 1} ≃ {u // d_to_c₂ d u = true} :=
        (Equiv.subtypeEquivRight
          (fun u => by
            constructor
            . intro h; constructor <;> simp [h]
            . rintro ⟨h₁, h₂⟩; simp at *; generalize hu : d u = x; fin_cases x <;> simp [hu] at *
          )
        ).trans
        (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm
      exact Species.transport equiv s₂
    case s₃' =>
      have equiv : {u // d u = 2} ≃ {u // d_to_c₁ d u = true} :=
        Equiv.subtypeEquivRight (fun u => by simp)
      exact Species.transport equiv s₃

  left_inv := by
    simp; rintro ⟨c₁, ⟨c₂, s₁, s₂⟩, s₃⟩; simp
    refine mul_ext (S := mul S₁ S₂) (T := S₃) (c₁_inv c₁ c₂) ?_ ?_
    · simp [mul_transport_mk]
      refine mul_ext (S := S₁) (T := S₂) ?_ ?_ ?_ <;> try simp [transport_transport]
      . apply c₂_inv
      . exact transport_eq_self_of_val _ (fun a => Subtype.ext (Subtype.ext rfl)) s₁
      . exact transport_eq_self_of_val _ (fun a => Subtype.ext (Subtype.ext rfl)) s₂
    . simp [transport_transport]
      exact transport_eq_self_of_val _ (fun a => Subtype.ext rfl) s₃

  right_inv := by
    simp; rintro ⟨d, s₁, s₂, s₃⟩; simp
    refine Mul₃_ext (d_inv' d) ?_ ?_ ?_ <;> simp [transport_transport]
    . exact transport_eq_self_of_val _ (fun a => Subtype.ext rfl) s₁
    . exact transport_eq_self_of_val _ (fun a => Subtype.ext rfl) s₂
    . exact transport_eq_self_of_val _ (fun a => Subtype.ext rfl) s₃

def mul_assoc
  {S₁ S₂ S₃ : Type → Type} [Species S₁] [Species S₂] [Species S₃] {U} [Finite U]
: (mul (mul S₁ S₂) S₃) U ≃ (mul S₁ (mul S₂ S₃)) U :=
  Mul₃_equiv₂.trans (@Mul₃_equiv₁ S₁ S₂ S₃ _ _ _ U _).symm

end Species
