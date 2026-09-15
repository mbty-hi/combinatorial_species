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


-- `noncomputable`: we can't go
noncomputable def deriv_Cycle_is_LinearOrder: Deriv C U ≃ L U where
  toFun := by
    unfold Deriv; rintro ⟨x, ⟨nonempty, same_cycle⟩⟩
    -- Missing: cycle from deriv
    obtain ⟨x, hx⟩ := x
    /- Cut at `*`, remove useless arrows to and from it -/
    refine ⟨
      , -- list
      ?_, -- nodup
      ?_ -- complete
    ⟩

  invFun      := sorry
  right_inv   := by sorry
  left_inv    := by sorry
