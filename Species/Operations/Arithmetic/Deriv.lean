import Species.Basic
import Species.Operations.Deriv
import Species.Operations.Add
import Species.Operations.Mul

namespace Species

variable {U: Type} [Fintype U] {F G: Type → Type}

theorem leibniz_add_eq : Deriv (Add F G) = Add (Deriv F) (Deriv G) := by rfl
def leibniz_add : Deriv (Add F G) U ≃ Add (Deriv F) (Deriv G) U := Equiv.refl _

variable [Species F] [Species G]

def innerOptionEquiv {U : Type} {d : WithHole U → Bool} {b: Bool} (h : d ⟨none⟩ = b)
: { u // d u = !b } ≃ { u : U // d (⟨some u⟩) = !b } where
  toFun
    | ⟨⟨none⟩, hu⟩   => by rw [h] at hu; simp at *
    | ⟨⟨some u⟩, hu⟩ => ⟨u, hu⟩
  invFun x    := ⟨⟨some x.1⟩, x.2⟩
  left_inv    := by rintro ⟨(_ | u), hu⟩ <;> simp; rw [h] at hu; simp at *
  right_inv _ := by rfl

def outerOptionEquiv {U : Type} {d : WithHole U → Bool} {b: Bool} (h : d ⟨none⟩ = b)
: { u // d u = b } ≃ WithHole { u : U // d (⟨some u⟩) = b } where
  toFun
    | ⟨⟨none⟩, _⟩    => ⟨none⟩
    | ⟨⟨some u⟩, hu⟩ => ⟨some ⟨u, hu⟩⟩
  invFun
    | ⟨none⟩         => ⟨⟨none⟩, h⟩
    | ⟨some ⟨u, hu⟩⟩ => ⟨⟨some u⟩, hu⟩
  left_inv := by rintro ⟨(_ | u), hu⟩ <;> rfl
  right_inv := by rintro (_ | ⟨u, hu⟩) <;> rfl

@[simp] theorem transportEquiv_apply {U V} [Finite U] [Finite V] (σ : U ≃ V) (f : F U) :
  transportEquiv σ f = transport σ f := rfl

theorem transport_heq {F : Type → Type} [Species F] {α β : Type} [Finite α] [Finite β]
  (hαβ : α = β) (σ : α ≃ β) (hσ : ∀ a, HEq (σ a) a) (f : F α)
: HEq (transport σ f) f := by
  subst hαβ
  have : σ = Equiv.refl α := Equiv.ext fun a => eq_of_heq (hσ a)
  rw [this, id_transport]

def leibnizMul : Deriv (Mul F G) U ≃ Add (Mul (Deriv F) G) (Mul F (Deriv G)) U where
  toFun :=
    fun ⟨d, f, g⟩ =>
      match h : d ⟨none⟩ with
      | true  =>
        .inr ⟨
          fun u => d (⟨some u⟩),
          transportEquiv (innerOptionEquiv h) f,
          transportEquiv (outerOptionEquiv h) g
        ⟩
      | false =>
        .inl ⟨
          fun u => d (⟨some u⟩),
          transportEquiv (outerOptionEquiv h) f,
          transportEquiv (innerOptionEquiv h) g
        ⟩

  invFun
    | .inl ⟨d, f, g⟩ => ⟨
        fun u =>
          match u with
          | ⟨none⟩ => false
          | ⟨some u⟩ => d u,
        transportEquiv (outerOptionEquiv (b := false) (by rfl)).symm f,
        transportEquiv (innerOptionEquiv (b := false) (by rfl)).symm g
      ⟩
    | .inr ⟨d, f, g⟩ => ⟨
        fun u =>
          match u with
          | ⟨none⟩ => true
          | ⟨some u⟩ => d u,
        transportEquiv (innerOptionEquiv (b := true) (by rfl)).symm f,
        transportEquiv (outerOptionEquiv (b := true) (by rfl)).symm g
      ⟩

  -- TODO terrubly ugly, much duplication, cleanup
  left_inv := by
    rintro ⟨d, f, g⟩; simp; split
    . next x d' f' g' heq =>
      split at heq
      . contradiction
      . injection heq with val_eq
        have h: (fun u => match u with | ⟨none⟩ => false | ⟨some u⟩ => d' u) = d := by
          ext ⟨_ | u⟩ <;> simp
          . assumption
          . obtain ⟨⟩ := val_eq; simp -- somehow this works?
        congr
        . simp [← h]
        . simp [← h]
        . next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hf
          simp [transport_transport]
          refine transport_heq ?_ _ ?_ f
          · exact congrArg (fun e => { u // e u = false }) h.symm
          . rintro ⟨⟨u⟩ , hu⟩
            cases u <;> simp [outerOptionEquiv]
            . congr
              . funext u; simp; rw [← h]
              . exact proof_irrel_heq _ _
            . congr; funext u; simp; rw [← h]
        . next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hg
          rw [transport_transport]
          refine transport_heq ?_ _ ?_ g
          · exact congrArg (fun e => { u // e u = true }) h.symm
          . rintro ⟨⟨u⟩, hu⟩
            cases u <;> simp [innerOptionEquiv]
            . simp [val] at hu
            . congr; simp; funext u; simp
              have x := congrFun h u
              exact x
    . next x d' f' g' heq =>
      split at heq
      . injection heq with val_eq
        have h: (fun u => match u with | ⟨none⟩ => true | ⟨some u⟩ => d' u) = d := by
          ext ⟨⟨x⟩⟩ <;> simp
          . assumption
          . obtain ⟨⟩ := val_eq; simp -- somehow this works?
        congr
        . simp [← h]
        . simp [← h]
        . next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hf
          rw [transport_transport]
          refine transport_heq ?_ _ ?_ f
          · exact congrArg (fun e => { u // e u = false }) h.symm
          . rintro ⟨⟨u⟩, hu⟩; cases u <;> simp [innerOptionEquiv]
            . simp [val] at hu
            . congr; funext u; simp; rw [← h]
        . next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hg
          simp [transport_transport]
          refine transport_heq ?_ _ ?_ g
          · exact congrArg (fun e => { u // e u = true }) h.symm
          . rintro ⟨⟨u⟩, hu⟩
            cases u <;> simp [outerOptionEquiv]
            . congr
              . funext u; simp; rw [← h]
              . exact proof_irrel_heq _ _
            . congr; funext u; simp; rw [← h]
      . contradiction

  right_inv := by
    rintro (⟨d, f, g⟩ | ⟨d, f, g⟩)
    <;> unfold Deriv at *
    <;> simp [transportEquiv, transport_transport, id_transport, Equiv.symm_trans_self]
    <;> congr

end Species
