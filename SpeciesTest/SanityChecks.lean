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





def deriv_mul {U : Type} :
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
        . let subEquiv : { u : Option U // split u = true } ≃ { u : U // split (some u) = true } := {
            toFun := fun ⟨u, h⟩ => match u with
              | some x => ⟨x, h⟩
              | none   => False.elim (by rw [hs] at h; contradiction)
            invFun := fun ⟨x, h⟩ => ⟨some x, h⟩
            left_inv := fun ⟨u, h⟩ => match u with
              | some x => rfl
              | none   => False.elim (by rw [hs] at h; contradiction)
            right_inv := fun ⟨x, h⟩ => rfl
          }
          exact Species.transport subEquiv Fstruct
        .
    . apply Sum.inl
      constructor
      case true.val.fst => exact split'
      case true.val.snd =>
        simp[split']
        constructor



  case invFun =>
  case right_inv =>
  case left_inv =>
