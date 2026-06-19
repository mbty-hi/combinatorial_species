import Species.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete

def SPermutation := Equiv.Perm

instance insetFintypeSPermutation {α} [Fintype α] [DecidableEq α] : Fintype (SPermutation α) :=
  inferInstanceAs (Fintype (Equiv.Perm α))

/- List of orbits ordered by length and contents -/
private def orbits {α} [Fintype α] [LinearOrder α] (p : SPermutation α) : List (List α) :=
  let labels : List α := Finset.univ.sort (· ≤ ·)
  let orbits : List (List α) :=
    -- Handling things one orbit at a time. We fold over all elements of type α to ensure that we
    -- meet every orbit.
    (labels.foldl
      -- acc : elements whose orbits have been seen × orbits
      (fun (acc : List α × List (List α)) (x : α) =>
        if x ∈ acc.1 then acc -- containing orbit already seen: skip
        else
          let orbit_raw := p.toList x -- returns the one orbit that contains x
          let orbit     := if orbit_raw.isEmpty then [x] else orbit_raw -- print fixed points
          (acc.1 ++ orbit, acc.2 ++ [orbit]))
      ([], [])
    ).2
  orbits.mergeSort (fun a b => a.length ≤ b.length) -- shorter orbits first

/- Display related instances -/
instance instReprSPermutation {α} [Fintype α] [LinearOrder α] [Repr α]
: Repr (SPermutation α) where
  reprPrec p _ := -- representation for a specific SPermutation
    Std.Format.join ((orbits p).map fun c => "(" ++ Std.Format.joinSep (c.map repr) ", " ++ ")")

-- Sorting only by number of orbits × contents
instance instLinearOrderSPermutation {α} [Fintype α] [LinearOrder α]
: LinearOrder (SPermutation α) :=
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

-- Sorting by number of orbits × size of these orbits × contents.
-- Leads to stack overflows even with very small sizes, the underlying issue is hard to pinpoint.
-- Ideally, we would prove the `orbits` function injective and just sort on
-- `(orbits p).mergeSort (fun a b => decide (a.length ≤ b.length))`.
/- instance instLinearOrderSPermutation {α} [Fintype α] [LinearOrder α] -/
/- : LinearOrder (SPermutation α) := -/
/-   LinearOrder.lift' -/
/-     (fun p => -/
/-       let orbits := (orbits p).mergeSort (fun a b => decide (a.length ≤ b.length)) -/
/-       toLex (orbits.map List.length, toLex (orbits, (Finset.univ.sort (· ≤ ·)).map p))) -/
/-     (fun p₁ p₂ h => by -/
/-       have h2 : (Finset.univ.sort (· ≤ ·)).map p₁ = (Finset.univ.sort (· ≤ ·)).map p₂ := -/
/-         congrArg (fun p => (ofLex (ofLex p).2).2) h -/
/-       ext x -/
/-       have hx : x ∈ Finset.univ.sort (· ≤ ·) := (Finset.mem_sort _).mpr (Finset.mem_univ x) -/
/-       obtain ⟨i, hlt, hi⟩ := List.mem_iff_getElem.mp hx -/
/-       have hmap := congrArg (·[i]?) h2 -/
/-       simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, hi] at hmap -/
/-       simpa using hmap) -/

/- Species instance -/
instance instSpeciesSPermutation : @Species SPermutation where
  fintype         := inferInstance
  transport       := fun σ   p => σ.permCongr p
  transport_trans := fun σ τ p => by apply Equiv.ext; simp
  transport_id    := fun     p => by apply Equiv.ext; simp
