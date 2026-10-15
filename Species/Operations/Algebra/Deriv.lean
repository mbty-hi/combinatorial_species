module

public import Species.Basic
public import Species.Isomorphism
public import Species.Operations.Deriv
public import Species.Operations.Add
public import Species.Operations.Mul

@[expose] public section

namespace Species

variable {U V : Type} [Finite U] [Finite V] {F G : Type → Type}

theorem leibniz_add_eq : Deriv (Add F G) = Add (Deriv F) (Deriv G) := by rfl

variable [Species F] [Species G]

def leibnizAdd : Iso (Deriv (Add F G)) (Add (Deriv F) (Deriv G)) := Iso.refl _

def innerOptionEquiv {d : WithHole U → Bool} {b: Bool} (h : d ⟨none⟩ = b)
: { u // d u = !b } ≃ { u : U // d (⟨some u⟩) = !b } where
  toFun
    | ⟨⟨none⟩, hu⟩   => by rw [h] at hu; simp only [Bool.eq_not_self] at *
    | ⟨⟨some u⟩, hu⟩ => ⟨u, hu⟩
  invFun x := ⟨⟨some x.1⟩, x.2⟩
  left_inv := by
    rintro ⟨(_ | u), hu⟩ <;> simp only [Subtype.mk.injEq, WithHole.mk.injEq, reduceCtorEq]
    rw [h] at hu; simp only [Bool.eq_not_self] at *
  right_inv _ := by rfl

def outerOptionEquiv {d : WithHole U → Bool} {b : Bool} (h : d ⟨none⟩ = b)
: { u // d u = b } ≃ WithHole { u : U // d (⟨some u⟩) = b } where
  toFun
    | ⟨⟨none⟩, _⟩    => ⟨none⟩
    | ⟨⟨some u⟩, hu⟩ => ⟨some ⟨u, hu⟩⟩
  invFun
    | ⟨none⟩         => ⟨⟨none⟩, h⟩
    | ⟨some ⟨u, hu⟩⟩ => ⟨⟨some u⟩, hu⟩
  left_inv := by rintro ⟨(_ | u), hu⟩ <;> rfl
  right_inv := by rintro (_ | ⟨u, hu⟩) <;> rfl

theorem transport_heq (U_eq_V : U = V) (σ : U ≃ V) (hσ : ∀ a, HEq (σ a) a) (f : F U)
: HEq (transport σ f) f := by
  subst U_eq_V
  have h : σ = Equiv.refl U := Equiv.ext (fun u => eq_of_heq (hσ u))
  rw [h, id_transport]

def leibnizMulEquiv : Deriv (Mul F G) U ≃ Add (Mul (Deriv F) G) (Mul F (Deriv G)) U where
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

  -- TODO terribly ugly, much duplication, cleanup
  left_inv := by
    rintro ⟨d, f, g⟩; simp only [transportEquiv_apply]; split
    · next x d' f' g' heq =>
      split at heq
      · contradiction
      · injection heq with val_eq
        have h: (fun u => match u with | ⟨none⟩ => false | ⟨some u⟩ => d' u) = d := by
          ext ⟨_ | u⟩ <;> simp only [Bool.false_eq]
          · assumption
          · obtain ⟨⟩ := val_eq; simp only -- somehow this works?
        congr
        · simp only [← h]
        · simp only [← h]
        · next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hf
          simp only [transportEquiv_apply, transport_transport]
          refine transport_heq ?_ _ ?_ f
          · exact congrArg (fun e => { u // e u = false }) h.symm
          · rintro ⟨⟨u⟩ , hu⟩
            cases u
              <;> simp only [outerOptionEquiv, Equiv.symm_mk, Equiv.trans_apply, Equiv.coe_fn_mk]
            · congr
              · funext u
                simp only [
                  eq_iff_iff, Bool.coe_false_iff_false, Bool.not_eq_eq_eq_not, Bool.not_not
                ]
                rw [← h]
              · exact proof_irrel_heq _ _
            · congr; funext u
              simp only [eq_iff_iff, Bool.coe_false_iff_false, Bool.not_eq_eq_eq_not, Bool.not_not]
              rw [← h]
        · next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hg
          rw [transport_transport]
          refine transport_heq ?_ _ ?_ g
          · exact congrArg (fun e => { u // e u = true }) h.symm
          · rintro ⟨⟨u⟩, hu⟩
            cases u
              <;> simp only [innerOptionEquiv, Equiv.symm_mk, Equiv.trans_apply, Equiv.coe_fn_mk]
            · simp only [val, Bool.false_eq_true] at hu
            · congr; simp only [Bool.not_false]; funext u; simp only [eq_iff_iff, Bool.coe_iff_coe]
              have x := congrFun h u
              exact x
    · next x d' f' g' heq =>
      split at heq
      · injection heq with val_eq
        have h: (fun u => match u with | ⟨none⟩ => true | ⟨some u⟩ => d' u) = d := by
          ext ⟨⟨x⟩⟩ <;> simp only [Bool.true_eq]
          · assumption
          · obtain ⟨⟩ := val_eq; simp only -- somehow this works?
        congr
        · simp only [← h]
        · simp only [← h]
        · next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hf
          rw [transport_transport]
          refine transport_heq ?_ _ ?_ f
          · exact congrArg (fun e => { u // e u = false }) h.symm
          · rintro ⟨⟨u⟩, hu⟩
            cases u
              <;> simp only [innerOptionEquiv, Equiv.symm_mk, Equiv.trans_apply, Equiv.coe_fn_mk]
            · simp only [val, Bool.true_eq_false] at hu
            · congr; funext u
              simp only [
                Bool.not_true, eq_iff_iff, Bool.coe_false_iff_false, Bool.not_eq_eq_eq_not,
                Bool.not_not
              ]
              rw [← h]
        · next val =>
          injection val_eq        with hd hfg; subst hd
          injection eq_of_heq hfg with hf hg ; subst hg
          simp only [transportEquiv_apply, transport_transport]
          refine transport_heq ?_ _ ?_ g
          · exact congrArg (fun e => { u // e u = true }) h.symm
          · rintro ⟨⟨u⟩, hu⟩
            cases u
              <;> simp only [outerOptionEquiv, Equiv.symm_mk, Equiv.trans_apply, Equiv.coe_fn_mk]
            · congr
              · funext u; simp only [eq_iff_iff, Bool.coe_iff_coe]; rw [← h]
              · exact proof_irrel_heq _ _
            · congr; funext u; simp only [eq_iff_iff, Bool.coe_iff_coe]; rw [← h]
      · contradiction

  right_inv := by
    rintro (⟨d, f, g⟩ | ⟨d, f, g⟩)
    <;> unfold Deriv at *
    <;> simp only [
          transportEquiv, Equiv.symm_symm, Equiv.coe_fn_mk, transport_transport,
          Equiv.symm_trans_self, id_transport
        ]
    <;> congr

def leibnizMul : Iso (Deriv (Mul F G)) (Add (Mul (Deriv F) G) (Mul F (Deriv G))) where
  equiv      U   := leibnizMulEquiv
  naturality σ s := by
    obtain ⟨d, f, g⟩ := s
    simp only [leibnizMulEquiv, Equiv.coe_fn_mk]
    split
    sorry

end Species
end
