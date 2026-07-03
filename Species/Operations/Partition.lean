import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Species.Labels.LabelType
import Species.Labels.Canonical
import Mathlib.Combinatorics.Colex

abbrev baz := (Fintype.elems (α := Fin 8))
def baz_list := baz.sort (· ≤ ·)

def setSplits2 {α : Type} [LabelType α] (s : Finset α) : List (Finset α × Finset α) :=
  let base := s.sort (· ≤ ·)
  let raw :=
    base.sublists.map
      (fun sub =>
        let comp := base.filter (fun x => decide (x ∉ sub))
        if sub ≤ comp then (sub.toFinset, comp.toFinset) else (comp.toFinset, sub.toFinset)
      )
  raw.dedup

/- lemma setSplits2_complete -/
/-   {α : Type} [LabelType α] (s : Finset α) {res : List (Finset α × Finset α)} -/
/-   (res_is_res : setSplits2 s = res) -/
/- : ∀ pair ∈ res, ∀ x ∈ s, x ∈ pair.1 ∨ x ∈ pair.2 := by -/
/-   intros pair pair_in_res x x_in_s -/

def fs_baz := setSplits2 baz

#eval (setSplits2 baz)

def part_type {α : Type} [DecidableEq α] (s : (Finset α × Finset α)) : Type × Type :=
  ({x : α // x ∈ s.1}, {x : α // x ∈ s.2})

def foo := List.map part_type fs_baz
