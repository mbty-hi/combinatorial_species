import Species.Operations.Add
import Species.Operations.Mul
import Species.Operations.Deriv
import Species.Instances.E
import Species.Basic

theorem deriv_add {F G : Type → Type} :
  Species.Deriv (Species.add F G) = Species.add (Species.Deriv F) (Species.Deriv G)
:= by rfl

variable {F G : Type -> Type} [Species F] [Species G]

def deriv_SE {α : Type}: Species.Deriv SE α ≃ SE α
:= by
  constructor
  case toFun => intro x; constructor
  case invFun => intro x; constructor
  case right_inv => intro x; simp
  case left_inv =>
    unfold Species.Deriv
    rintro ⟨⟩
    simp


def foobar {U} {b : Bool} {split : Option U → Bool} (foo : split none = !b) :
    {x : Option U // split x = b} ≃ {y : U // split (some y) = b} where
  toFun
    | ⟨none  , h⟩ => absurd h (by rw [foo]; cases b <;> decide)
    | ⟨some y, h⟩ => ⟨y, h⟩
  invFun := fun ⟨y, h⟩  => ⟨some y, h⟩
  left_inv
    | ⟨none  , h⟩ => absurd h (by rw [foo]; cases b <;> decide)
    | ⟨some y, h⟩ => rfl
  right_inv := fun _ => rfl


def barfoo {U} {b : Bool} {split : Option U → Bool} (hn : split none = b) :
    Option {u // split (some u) = b} ≃ {v // split v = b} where
  toFun
    | none => ⟨none, hn⟩
    | some ⟨u, hu⟩ => ⟨some u, hu⟩
  invFun
    | ⟨none, _⟩ => none
    | ⟨some u, hu⟩ => some ⟨u, hu⟩
  left_inv := by rintro (_ | ⟨u, hu⟩) <;> rfl
  right_inv := by rintro ⟨(_ | u), hv⟩ <;> rfl


def e {α} {split : α → Bool} {b: Bool} :
{u : Option α // Option.rec b (fun val => split val) u = b} ≃ Option {v // split v = b} where
  toFun
    | ⟨none, _⟩ => none
    | ⟨some val, hv⟩ => some ⟨val, hv⟩
  invFun
    | none => ⟨none, rfl⟩
    | some ⟨val, hv⟩ => ⟨val, hv⟩
  left_inv := by rintro ⟨(_ | val), hv⟩ <;> rfl
  right_inv := by rintro (_ | ⟨val, hv⟩) <;> rfl

def f {α} {split : α → Bool} {b: Bool} :
    {u : Option α // Option.rec (!b) (fun val => split val) u = b}
      ≃ {v : α // split v = b}
where
  toFun
    | ⟨none, h⟩ => absurd h (by simp)
    | ⟨some val, hv⟩ => ⟨val, hv⟩
  invFun
    | ⟨val, hv⟩ => ⟨some val, hv⟩
  left_inv := by
    rintro ⟨(_ | val), hv⟩
    · exact absurd hv (by simp)
    · rfl
  right_inv := fun _ => rfl


def deriv_mul {U : Type} [Finite U]:
  Species.Deriv (Species.mul F G) U
  ≃ Species.add (Species.mul (Species.Deriv F) G) (Species.mul F (Species.Deriv G)) U
:= by
  unfold Species.Deriv
  unfold Species.add
  unfold Species.mul
  unfold Species.WithHole
  unfold WithBot
  simp
  constructor
  case toFun =>
    rintro ⟨split, ⟨Fstruct, Gstruct⟩⟩
    let split' := fun u => split (Option.some u)
    -- have foo : ∀u, split' u = split (Option.some u) := by
    cases hs : split Option.none
    . apply Sum.inr
      constructor
      case false.val.fst => exact split'
      case false.val.snd =>
        simp [split']
        constructor
        . apply Species.transportEquiv (foobar hs) Fstruct
        . apply (Species.transportEquiv (barfoo hs)).symm Gstruct
    . apply Sum.inl
      constructor
      case true.val.fst => exact split'
      case true.val.snd =>
        simp[split']
        constructor
        . apply (Species.transportEquiv (barfoo hs)).symm Fstruct
        . apply Species.transportEquiv (foobar hs) Gstruct

  case invFun =>
    rintro (⟨split, ⟨Fstruct, Gstruct⟩⟩ | ⟨split, ⟨Fstruct, Gstruct⟩⟩)
    . constructor
      case inl.fst =>
        rintro (_ | ou)
        . exact true
        . exact split ou
      case inl.snd =>
        constructor
        . apply (Species.transportEquiv e).symm Fstruct
        . apply (Species.transportEquiv f).symm Gstruct
    . constructor
      case inr.fst =>
        rintro (_ | ou)
        . exact false
        . exact split ou
      case inr.snd =>
        constructor
        . apply (Species.transportEquiv f).symm Fstruct
        . apply (Species.transportEquiv e).symm Gstruct
  case right_inv => simp
  case left_inv => sorry
