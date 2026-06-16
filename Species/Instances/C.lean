import Species.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Data.Fintype.Perm

/- The species of cycles is defined as `Equiv.Perm α` (i.e., `α ≃ α`) with some restrictions:
   * `Nonempty` blocks the definition of cycles of length zero (remember that permutations can be
     defined as E∘C).
   * `SameCycle` ensures that the cycle covers all elements. -/
def SCycle (α : Type) := {σ : Equiv.Perm α // Nonempty α ∧ ∀ x y, σ.SameCycle x y}

/- Display related instances -/
/- instance instReprSCycle {α} [Fintype α] [LinearOrder α] [Repr α] : Repr (SCycle α) where -/
/-   reprPrec s _ := repr ((Finset.univ.sort (· ≤ ·)).map (fun x => (x, s.1 x))) -/
-- Representation in cycle form (e.g., (1, 3, 2))
instance instReprSCycle {α} [Fintype α] [LinearOrder α] [Repr α] : Repr (SCycle α) where
  reprPrec s _ :=
    let anchor := Finset.univ.min' (Finset.univ_nonempty_iff.mpr s.2.1)
    let cyc := s.1.toList anchor
    let cyc := if cyc.isEmpty then [anchor] else cyc
    "(" ++ Std.Format.joinSep (cyc.map repr) ", " ++ ")"

-- LinearOrder: lift along the (injective) image list into the lex order on List α.
instance instLinearOrderSCycle {α} [Fintype α] [LinearOrder α] : LinearOrder (SCycle α) :=
  LinearOrder.lift'
    (fun s => (Finset.univ.sort (· ≤ ·)).map s.1)
    (fun s t h => by
      apply Subtype.ext; ext x
      have hx : x ∈ Finset.univ.sort (· ≤ ·) :=
        (Finset.mem_sort _).mpr (Finset.mem_univ x)
      obtain ⟨i, hlt, hi⟩ := List.mem_iff_getElem.mp hx
      have hmap := congrArg (·[i]?) h
      simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, hi] at hmap
      simpa using hmap)

/- Species instance -/
private lemma permCongr_zpow {α β : Type} (e : α ≃ β) (p : Equiv.Perm α) (i : ℤ)
: (e.permCongr p) ^ i = e.permCongr (p ^ i) :=
  (map_zpow (MulEquiv.mk' e.permCongr e.permCongr_mul) p i).symm

private lemma permCongr_sameCycle
  {α β : Type} (e : α ≃ β) (p : Equiv.Perm α) {x y : β} (h : p.SameCycle (e.symm x) (e.symm y))
: (e.permCongr p).SameCycle x y := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rw [permCongr_zpow, Equiv.permCongr_apply, hi, Equiv.apply_symm_apply]⟩

instance instSpeciesSCycle : @Species SCycle where
  fintype := by
    intros α _
    haveI : Decidable (Nonempty α) := decidable_of_iff (0 < Fintype.card α) Fintype.card_pos_iff
    exact inferInstanceAs (Fintype {σ : Equiv.Perm α // Nonempty α ∧ ∀ x y, σ.SameCycle x y})
  transport := fun σ s =>
    ⟨σ.permCongr s.1, s.2.1.map σ,
     fun x y => permCongr_sameCycle σ s.1 (s.2.2 (σ.symm x) (σ.symm y))⟩
  transport_trans := fun σ τ s =>
    Subtype.ext (by
      show (σ.trans τ).permCongr s.1 = τ.permCongr (σ.permCongr s.1)
      ext x; simp [Equiv.permCongr_apply, Equiv.trans_apply, Equiv.symm_trans_apply]
    )
  transport_id := fun s => Subtype.ext (by show (Equiv.refl _).permCongr s.1 = s.1; ext x; simp)
