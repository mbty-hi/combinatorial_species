import Species.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

abbrev SPowerset : Type → Type := Finset

/- Display related instances -/
namespace Display
instance instReprSPowerset {α : Type} [LinearOrder α] [Repr α] : Repr (SPowerset α) where
  reprPrec s _ := "{" ++ Std.Format.joinSep ((s.sort (· ≤ ·)).map repr) ", " ++ "}"
instance instLinearOrderSPowerset {α} [LinearOrder α] : LinearOrder (SPowerset α) :=
  -- use lexicographic order
  LinearOrder.lift'
    (fun s => (toLex (s.card, s.sort (· ≤ ·)) : ℕ ×ₗ List α))
    (fun _ _ h =>
      (Function.LeftInverse.injective (fun s => Finset.sort_toFinset s (· ≤ ·)))
        (congrArg (fun p => (ofLex p).2) h))
end Display

/- Species instance -/
instance instSpeciesSPowerset : Species SPowerset where
  fintype         := inferInstance
  transport       := fun σ s => s.map σ.toEmbedding
  transport_trans := by intro _ _ _ σ τ f; simp [Finset.map_map]
  transport_id    := by intro _ f; simp
