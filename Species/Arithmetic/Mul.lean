import Species.Basic
import Species.Operations.Mul
import Species.Instances.One
import Species.Instances.Zero

namespace Species
  theorem transportEquiv_symm {U V} {F: Type → Type} [Finite U] [Finite V] [Species F] (σ : U ≃ V) :
    (Species.transportEquiv σ.symm : F V ≃ F U) = (Species.transportEquiv σ).symm :=
    Equiv.ext fun _ => rfl

  def one_mul (S: Type → Type) [Species S] U [Finite U] : (Species.mul SOne S) U ≃ S U where
    toFun := fun x =>
      Species.transportEquiv
        (Equiv.subtypeUnivEquiv fun u => by rcases h : x.1 u; rfl; nomatch x.2.1 ⟨u, h⟩)
        x.2.2

    invFun := fun s => ⟨
      fun _ => false,
      fun x => Bool.noConfusion x.2,
      Species.transportEquiv (Equiv.subtypeUnivEquiv (fun _ => rfl)).symm s
    ⟩

    left_inv := by
      rintro ⟨d, fst, snd⟩
      obtain rfl : d = fun _ => false := funext fun u => by
        rcases h : d u; rfl; nomatch fst ⟨u, h⟩
      simp; congr 2
      · funext x; exact (fst x).elim
      · rw [transportEquiv_symm, Equiv.symm_apply_apply]

    right_inv := by intros _; simp [transportEquiv_symm, Equiv.apply_symm_apply]

  def mul_one (S : Type → Type) [Species S] U [Finite U] : (Species.mul S SOne) U ≃ S U where
    toFun := fun ⟨d, fst, snd⟩ =>
      Species.transportEquiv
        (Equiv.subtypeUnivEquiv fun u => by rcases h : d u; nomatch snd ⟨u, h⟩; rfl)
        fst

    invFun := fun s => ⟨
      fun _ => true,
      Species.transportEquiv (Equiv.subtypeUnivEquiv (fun _ => rfl)).symm s,
      fun x => Bool.noConfusion x.2
    ⟩

    left_inv := by
      rintro ⟨d, fst, snd⟩
      obtain rfl : d = fun _ => true := funext fun u => by
        rcases h : d u; nomatch snd ⟨u, h⟩; rfl
      simp; congr 2
      · rw [transportEquiv_symm, Equiv.symm_apply_apply]
      · funext x; exact (snd x).elim

    right_inv := by intros _; simp; rw [transportEquiv_symm, Equiv.apply_symm_apply]
end Species
