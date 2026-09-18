import Species.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite

namespace Species

/- We define the linear order on `U` as a bijection with `Fin (Nat.card U)` (though we do not
   actually use `Nat.card`, as we care about computability). -/
structure L (U : Type) where
  card : ℕ
  ord  : U ≃ Fin card

/- TODO use namespaces in other instances -/
namespace L

variable {U V : Type}

def order (x : L U) : List U := (List.finRange x.card).map x.ord.symm

lemma order_injective : Function.Injective (L.order (U := U)) := by
  intro ⟨n₁, e₁⟩ ⟨n₂, e₂⟩ h
  have hn : n₁ = n₂ := by simpa [order] using congrArg List.length h
  subst hn; congr 1
  have hs : e₁.symm = e₂.symm := Equiv.ext fun i => List.map_inj_left.mp h i (List.mem_finRange i)
  simpa using congrArg Equiv.symm hs

/- Display related instances -/
instance instReprL {U} [Repr U] : Repr (L U) where
  reprPrec x prec := reprPrec x.order prec
instance instLinearOrderL {U} [LinearOrder U] : LinearOrder (L U) :=
  LinearOrder.lift' L.order L.order_injective

def transport (σ : U ≃ V) (x : L U) : L V := ⟨x.card, σ.symm.trans x.ord⟩

end L

instance instFintypeL {U} [DecidableEq U] [Fintype U] : Fintype (L U) :=
  Fintype.ofEquiv
    (U ≃ Fin (Fintype.card U))
    {
      toFun     := fun e => ⟨_, e⟩
      invFun    := fun x => x.ord.trans (finCongr (by simpa using (Fintype.card_congr x.ord).symm))
      left_inv  := fun e => by ext i; simp
      right_inv := fun ⟨n, e⟩ => by
        have h : n = Fintype.card U := by simpa using (Fintype.card_congr e).symm
        subst h; congr 1
    }

instance instSpeciesL : Species L where
  finite := by
    intros U _
    have : Fintype U := Fintype.ofFinite U
    classical
    infer_instance
  transport      := fun σ => L.transport σ
  id_transport   := fun x => by congr
  comp_transport := fun σ τ ⟨card, ord⟩ => by rw [Function.comp_apply, L.transport]; congr 1

instance instDecEqL {U} [DecidableEq U] [Fintype U] : DecidableEq (L U) :=
  fun ⟨n₁, e₁⟩ ⟨n₂, e₂⟩ =>
    if h : n₁ = n₂ then by
      subst h; exact decidable_of_iff (e₁ = e₂) ⟨by intro rfl; simp, fun h => by cases h; rfl⟩
    else isFalse fun heq => h (congrArg L.card heq)

instance instSpeciesCompL : SpeciesComp L where
  fintype := inferInstance
  decEq   := inferInstance

end Species
