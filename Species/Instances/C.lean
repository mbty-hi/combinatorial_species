module

public import Species.Basic
public import Species.Computable
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace Species

/- The species of cycles is defined as `Equiv.Perm U` (i.e., `U ≃ U`) with some restrictions:
   * `Nonempty` blocks the definition of cycles of length zero (remember that permutations can be
     defined as E∘C).
   * `SameCycle` ensures that the cycle covers all elements. -/
def C (U : Type) := {σ : Equiv.Perm U // Nonempty U ∧ ∀ x y, σ.SameCycle x y}

namespace C

/- Display related instances -/
-- Representation in cycle form (e.g., (1, 3, 2))
instance instRepr {U} [Fintype U] [LinearOrder U] [Repr U] : Repr (C U) where
  reprPrec s _ :=
    let anchor := Finset.univ.min' (Finset.univ_nonempty_iff.mpr s.2.1)
    let cyc := s.1.toList anchor
    let cyc := if cyc.isEmpty then [anchor] else cyc
    "(" ++ Std.Format.joinSep (cyc.map repr) ", " ++ ")"

-- LinearOrder: lift along the (injective) image list into the lex order on List α.
instance instLinearOrder {U} [Fintype U] [LinearOrder U] : LinearOrder (C U) :=
  LinearOrder.lift'
    (fun s => (Finset.univ.sort (· ≤ ·)).map s.1)
    (fun s t h => by
      apply Subtype.ext; ext x
      have hx : x ∈ Finset.univ.sort (· ≤ ·) :=
        (Finset.mem_sort _).mpr (Finset.mem_univ x)
      obtain ⟨i, hlt, hi⟩ := List.mem_iff_getElem.mp hx
      have hmap := congrArg (·[i]?) h
      simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, hi] at hmap
      simpa only [Option.map_some, Option.some.injEq] using hmap)

/- Species instance -/
lemma permCongr_zpow {U V : Type} (e : U ≃ V) (p : Equiv.Perm U) (i : ℤ)
: (e.permCongr p) ^ i = e.permCongr (p ^ i) :=
  (map_zpow (MulEquiv.mk' e.permCongr e.permCongr_mul) p i).symm

lemma permCongr_sameCycle
  {U V : Type} (e : U ≃ V) (p : Equiv.Perm U) {x y : V} (h : p.SameCycle (e.symm x) (e.symm y))
: (e.permCongr p).SameCycle x y := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rw [permCongr_zpow, Equiv.permCongr_apply, hi, Equiv.apply_symm_apply]⟩

instance instSpecies : Species C where
  finite := by unfold C; infer_instance
  transport := fun σ s =>
    ⟨σ.permCongr s.1, s.2.1.map σ,
     fun x y => permCongr_sameCycle σ s.1 (s.2.2 (σ.symm x) (σ.symm y))⟩
  id_transport := fun s =>
    Subtype.ext
      (by
        show (Equiv.refl _).permCongr s.1 = s.1; ext x
        simp only [
          Equiv.permCongr_eq_mul, Equiv.Perm.coe_mul, Equiv.coe_refl, CompTriple.comp_eq,
          Equiv.Perm.coe_inv, Equiv.refl_symm, Function.comp_apply, id_eq
        ]
      )
  comp_transport := fun σ τ s =>
    Subtype.ext (by
      show (σ.trans τ).permCongr s.1 = τ.permCongr (σ.permCongr s.1)
      ext x; simp only [Equiv.permCongr_apply, Equiv.symm_trans, Equiv.trans_apply]
    )

instance instComputableSpecies : ComputableSpecies C where
  fintype := by
    intros α _
    haveI _ : Decidable (Nonempty α) := decidable_of_iff (0 < Fintype.card α) Fintype.card_pos_iff
    exact inferInstanceAs (Fintype {σ : Equiv.Perm α // Nonempty α ∧ ∀ x y, σ.SameCycle x y})
  decEq := inferInstance

end C
end Species
end
