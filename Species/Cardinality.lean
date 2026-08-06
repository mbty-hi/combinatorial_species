import Species.Basic
import Species.Labels.Canonical
import Mathlib.Data.Finset.Sort

/- TODO find a better name for this file -/

/- Finset of all `F`-structures on `n` labels. -/
def structures_fset (F : Type → Type) [SpeciesComp F] (LabelT : Type) [LabelType LabelT]
: Finset (F LabelT) :=
  Finset.univ
def structures_canonical_fset (F : Type → Type) [SpeciesComp F] (n : ℕ) : Finset (F (Canonical n)) :=
  structures_fset F (Canonical n)

/- List of all `F`-structures on `n` labels. Requires LinearOrder on (F LabelT) -/
def structures
  (F : Type → Type) [SpeciesComp F] (LabelT : Type) [LabelType LabelT] [LinearOrder (F (LabelT))]
: List (F LabelT) :=
  (structures_fset F LabelT).sort (· ≤ ·)
def structures_canonical (F : Type → Type) (n : ℕ) [SpeciesComp F] [LinearOrder (F (Canonical n))]
: List (F (Canonical n)) :=
  structures F (Canonical n)

/- Number of `F`-structures on `n` labels. -/
def card (F : Type → Type) [SpeciesComp F] (n : ℕ) : ℕ := Fintype.card (F (FinNat n))

/- The first `n` terms of `F`'s counting sequence. -/
def seq (F : Type → Type) [SpeciesComp F] (n : ℕ) : List ℕ := (List.range n).map (card F)
