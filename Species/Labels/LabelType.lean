import Mathlib.Data.Finset.Functor

/- A label type: finite, linearly ordered. The order is required for computationality (`Finset`
   exposes a `sort` function that gives a list of its members, and it requires `LinearOrder`). -/
class LabelType (U: Type) extends Fintype U, LinearOrder U

/- Build `LabelType` from its parents. -/
instance {U: Type} [Fintype U] [LinearOrder U] : LabelType U where
  toFintype     := inferInstance
  toLinearOrder := inferInstance
