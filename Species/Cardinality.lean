import Mathlib.Data.Finset.Sort
import Species.Computable
import Species.Labels.Canonical

namespace Species

variable (F : Type → Type) [ComputableSpecies F] (U : Type) [LabelType U]

/-- Finset of all `F`-structures on `n` labels. -/
def structures_fset : Finset (F U) := Finset.univ
/-- Finset of all `F`-structures on the canonical label type with `n` labels. -/
def structures_canonical_fset (n : ℕ) : Finset (F (Canonical n)) := structures_fset F (Canonical n)

/- List of all `F`-structures on `n` labels. -/
def structures [LinearOrder (F U)] : List (F U) := (structures_fset F U).sort (· ≤ ·)
/- List of all `F`-structures on the canonical label type with `n` labels. -/
def structures_canonical (n : ℕ) [LinearOrder (F (Canonical n))] : List (F (Canonical n)) :=
  structures F (Canonical n)

/-- Number of `F`-structures on `n` labels. -/
def card (n : ℕ) : ℕ := Fintype.card (F (Fin n))

/-- The first `n` terms of `F`'s counting sequence. -/
def seq (n : ℕ) : List ℕ := (List.range n).map (card F)

end Species
