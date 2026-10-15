module

public import Species.Basic
public import Species.Labels.LabelType

/-!
# Computable combinatorial species
This file defines a *computable* extension to combinatorial species.

## Important definitions
* `ComputableSpecies` : the class of *computable* species, which we can use to generate, e.g., all
  `F`-structures on a specific set of labels

## Implementation notes
We rely on `LabelType` for the label type `U`, which is therefore enumerable and linearly ordered.
The linear order on `U` is what makes it possible to use `Finset.sort` to extract a list of
`F`-structures on `U` computably (see `structures` in `Cardinality.lean`, which additionally
requires a `LinearOrder` on `F U` to control the presentation order).
-/

@[expose] public section

/-- A *computable* combinatorial species providing an enumeration and a decidable equality for the
`F`-structures on label types `U` that are enumerable and linearly ordered (`LabelType`). -/
class ComputableSpecies (F : Type → Type) extends Species F where
  /-- Enumeration of the `F`-structures on `U`.  -/
  fintype : {U : Type} → [LabelType U] → Fintype (F U)
  /-- The equality of the `F`-structures on `U` must be decidable. -/
  decEq : {U : Type} → [LabelType U] → DecidableEq (F U)

namespace ComputableSpecies

variable {F : Type → Type} [ComputableSpecies F] {U : Type} [LabelType U]

instance instFintype : Fintype     (F U) := fintype
instance instDecEq   : DecidableEq (F U) := decEq

/-- The finite set of `F`-structures on label type `U`. -/
def structures : Finset (F U) := Finset.univ

end ComputableSpecies
end
