import Species.Basic
import Species.Labels.LabelType

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
