module

public import Species.Basic
public import Species.Computable
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section

namespace Species

def S := Equiv.Perm

namespace S

instance insetFintype {U} [Fintype U] [DecidableEq U] : Fintype (S U) :=
  inferInstanceAs (Fintype (Equiv.Perm U))

/- List of orbits ordered by length and contents -/
def orbits {U} [Fintype U] [LinearOrder U] (p : S U) : List (List U) :=
  let labels : List U := Finset.univ.sort (· ≤ ·)
  let orbits : List (List U) :=
    -- Handling things one orbit at a time. We fold over all elements of type α to ensure that we
    -- meet every orbit.
    (labels.foldl
      -- acc : elements whose orbits have been seen × orbits
      (fun (acc : List U × List (List U)) (x : U) =>
        if x ∈ acc.1 then acc -- containing orbit already seen: skip
        else
          let orbit_raw := p.toList x -- returns the one orbit that contains x
          let orbit     := if orbit_raw.isEmpty then [x] else orbit_raw -- print fixed points
          (acc.1 ++ orbit, acc.2 ++ [orbit]))
      ([], [])
    ).2
  orbits.mergeSort (fun a b => a.length ≤ b.length) -- shorter orbits first

/- Display related instances -/
instance instRepr {U} [Fintype U] [LinearOrder U] [Repr U]
: Repr (S U) where
  reprPrec p _ := -- representation for a specific S
    Std.Format.join ((orbits p).map fun c => "(" ++ Std.Format.joinSep (c.map repr) ", " ++ ")")

-- Sorting only by (number of orbits) × contents
instance instLinearOrder {U} [Fintype U] [LinearOrder U]
: LinearOrder (S U) :=
  LinearOrder.lift'
    (fun p =>
      let orbits := (orbits p).mergeSort (fun a b => decide (a.length ≤ b.length))
      toLex (orbits.map List.length, (Finset.univ.sort (· ≤ ·)).map p.1))
      (fun p₁ p₂ h => by
        have h2 : (Finset.univ.sort (· ≤ ·)).map p₁.1 = (Finset.univ.sort (· ≤ ·)).map p₂.1 :=
          congrArg (fun p => (ofLex p).2) h
        refine Equiv.ext (fun x => ?_)
        show p₁.1 x = p₂.1 x
        have hx : x ∈ Finset.univ.sort (· ≤ ·) := (Finset.mem_sort _).mpr (Finset.mem_univ x)
        obtain ⟨i, hlt, hi⟩ := List.mem_iff_getElem.mp hx
        have hmap := congrArg (·[i]?) h2
        simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, hi] at hmap
        simpa using hmap)

-- Sorting by (number of orbits) × (list of sizes of these orbits) × (contents).
-- Leads to stack overflows even with very small sizes, the underlying issue is hard to pinpoint.
-- Ideally, we would prove the `orbits` function injective and just sort on
-- `(orbits p).mergeSort (fun a b => decide (a.length ≤ b.length))`.
/- instance instLinearOrder {U} [Fintype U] [LinearOrder U] -/
/- : LinearOrder (S U) := -/
/-   LinearOrder.lift' -/
/-     (fun p => -/
/-       let orbits := (orbits p).mergeSort (fun a b => decide (a.length ≤ b.length)) -/
/-       toLex (orbits.map List.length, toLex (orbits, (Finset.univ.sort (· ≤ ·)).map p.1))) -/
/-     (fun p₁ p₂ h => by -/
/-       have h2 : (Finset.univ.sort (· ≤ ·)).map p₁.1 = (Finset.univ.sort (· ≤ ·)).map p₂.1 := -/
/-         congrArg (fun p => (ofLex (ofLex p).2).2) h -/
/-       refine Equiv.ext (fun x => ?_) -/
/-       show p₁.1 x = p₂.1 x -/
/-       have hx : x ∈ Finset.univ.sort (· ≤ ·) := (Finset.mem_sort _).mpr (Finset.mem_univ x) -/
/-       obtain ⟨i, hlt, hi⟩ := List.mem_iff_getElem.mp hx -/
/-       have hmap := congrArg (·[i]?) h2 -/
/-       simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, hi] at hmap -/
/-       simpa using hmap) -/

/- Species instance -/
instance instSpecies : Species S where
  finite         := by unfold S; infer_instance
  transport      := fun σ   p => σ.permCongr p
  id_transport   := fun     p => by rfl
  comp_transport := fun σ τ p => by rfl

instance instComputableSpecies : ComputableSpecies S where
  fintype := inferInstance
  decEq   := inferInstance

end S
end Species
end
