import Mathlib.Data.Finset.Functor

/- A label type: finite, linearly ordered. The order is required for computability (`Finset`
   exposes a `sort` function that gives a list of its members, and it requires `LinearOrder`). -/
class LabelType (α : Type) extends Fintype α, LinearOrder α

/- Build `LabelType` from its parents. -/
instance {α : Type} [Fintype α] [LinearOrder α] : LabelType α where
  toFintype     := inferInstance
  toLinearOrder := inferInstance
