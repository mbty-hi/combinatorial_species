import Species.Basic
import Species.Operations.Deriv
import Species.Operations.Add
import Species.Operations.Mul

namespace Species

variable {U: Type} [Fintype U] {F G: Type → Type}

theorem leibniz_add_eq : Deriv (Add F G) = Add (Deriv F) (Deriv G) := by rfl
def leibniz_add : Deriv (Add F G) U ≃ Add (Deriv F) (Deriv G) U := Equiv.refl _

variable [Species F] [Species G]

def InnerOptionEquiv {U : Type} {d : Option U → Bool} {b: Bool} (h : d none = b)
: { u // d u = !b } ≃ { u : U // d (some u) = !b } where
  toFun
    | ⟨none, hu⟩   => by rw [h] at hu; simp at *
    | ⟨some u, hu⟩ => ⟨u, hu⟩
  invFun x    := ⟨some x.1, x.2⟩
  left_inv    := by rintro ⟨(_ | u), hu⟩ <;> simp; rw [h] at hu; simp at *
  right_inv _ := by rfl

def OuterOptionEquiv {U : Type} {d : Option U → Bool} {b: Bool} (h : d none = b)
: { u // d u = b } ≃ Option { u : U // d (some u) = b } where
  toFun
    | ⟨none, _⟩    => none
    | ⟨some u, hu⟩ => some ⟨u, hu⟩
  invFun
    | none         => ⟨none, h⟩
    | some ⟨u, hu⟩ => ⟨some u, hu⟩
  left_inv := by rintro ⟨(_ | u), hu⟩ <;> rfl
  right_inv := by rintro (_ | ⟨u, hu⟩) <;> rfl

@[simp] theorem transportEquiv_apply {U V} [Finite U] [Finite V] (σ : U ≃ V) (f : F U) :
  transportEquiv σ f = transport σ f := rfl

theorem transport_heq {F : Type → Type} [Species F] {α β : Type} [Finite α] [Finite β]
  (hαβ : α = β) (σ : α ≃ β) (hσ : ∀ a, HEq (σ a) a) (f : F α)
: HEq (Species.transport σ f) f := by
  subst hαβ
  have : σ = Equiv.refl α := Equiv.ext fun a => eq_of_heq (hσ a)
  rw [this, Species.id_transport]

def leibniz_mul : Deriv (Mul F G) U ≃ Add (Mul (Deriv F) G) (Mul F (Deriv G)) U where
  toFun :=
    fun ⟨d, f, g⟩ =>
      match h : d none with
      | true  =>
        .inr ⟨
          fun u => d (some u),
          Species.transportEquiv (InnerOptionEquiv h) f,
          Species.transportEquiv (OuterOptionEquiv h) g
        ⟩
      | false =>
        .inl ⟨
          fun u => d (some u),
          Species.transportEquiv (OuterOptionEquiv h) f,
          Species.transportEquiv (InnerOptionEquiv h) g
        ⟩

  invFun
    | .inl ⟨d, f, g⟩ => ⟨
        fun u =>
          match u with
          | Option.none => false
          | Option.some u => d u,
        Species.transportEquiv (OuterOptionEquiv (b := false) (by rfl)).symm f,
        Species.transportEquiv (InnerOptionEquiv (b := false) (by rfl)).symm g
      ⟩
    | .inr ⟨d, f, g⟩ => ⟨
        fun u =>
          match u with
          | Option.none => true
          | Option.some u => d u,
        Species.transportEquiv (InnerOptionEquiv (b := true) (by rfl)).symm f,
        Species.transportEquiv (OuterOptionEquiv (b := true) (by rfl)).symm g
      ⟩

  -- TODO terrubly ugly, much duplication, cleanup
  left_inv := by
    simp [Function.LeftInverse]
    rintro ⟨d, f, g⟩; simp; split
    . next x d' f' g' heq =>
      split at heq
      . contradiction
      . injection heq with val_eq
        have h: (fun u => match u with | none => false | some u => d' u) = d := by
          ext ⟨x⟩ <;> simp
          . assumption
          . obtain ⟨⟩ := val_eq; simp -- somehow this works?
        congr
        . simp [← h]
        . simp [← h]
        . next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hf
          rw [Species.transport_transport]
          refine Species.transport_heq ?_ _ ?_ f
          · exact congrArg (fun e => { u // e u = false }) h.symm
          . rintro ⟨u, hu⟩
            cases u <;> simp [OuterOptionEquiv]
            . congr
              . funext u; simp; rw [← h]
              . exact proof_irrel_heq _ _
            . congr; funext u; simp; rw [← h]
        . next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hg
          rw [Species.transport_transport]
          refine Species.transport_heq ?_ _ ?_ g
          · exact congrArg (fun e => { u // e u = true }) h.symm
          . rintro ⟨u, hu⟩
            cases u <;> simp [InnerOptionEquiv]
            . simp [val] at hu
            . congr; simp; funext u; simp
              have x := congrFun h u
              exact x
    . next x d' f' g' heq =>
      split at heq
      . injection heq with val_eq
        have h: (fun u => match u with | none => true | some u => d' u) = d := by
          ext ⟨x⟩ <;> simp
          . assumption
          . obtain ⟨⟩ := val_eq; simp -- somehow this works?
        congr
        . simp [← h]
        . simp [← h]
        . next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hf
          rw [Species.transport_transport]
          refine Species.transport_heq ?_ _ ?_ f
          · exact congrArg (fun e => { u // e u = false }) h.symm
          . rintro ⟨u, hu⟩; cases u <;> simp [InnerOptionEquiv]
            . simp [val] at hu
            . congr; funext u; simp; rw [← h]
        . next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hg
          rw [Species.transport_transport]
          refine Species.transport_heq ?_ _ ?_ g
          · exact congrArg (fun e => { u // e u = true }) h.symm
          . rintro ⟨u, hu⟩
            cases u <;> simp [OuterOptionEquiv]
            . congr
              . funext u; simp; rw [← h]
              . exact proof_irrel_heq _ _
            . congr; funext u; simp; rw [← h]
      . contradiction

  right_inv := by
    rintro (⟨d, f, g⟩ | ⟨d, f, g⟩)
    <;> simp [
          Species.transportEquiv_apply, Species.transport_transport, Species.id_transport,
          Equiv.symm_trans_self
        ]


end Species
