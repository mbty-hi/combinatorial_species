import Species.Basic
import Species.Computable
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

namespace Species

def Powerset : Type → Type := Finset

namespace Powerset

instance instFintype {U} [Fintype U] : Fintype (Powerset U) :=
  inferInstanceAs (Fintype (Finset U))

/- Display related instances -/
namespace Display
instance instRepr {U : Type} [LinearOrder U] [Repr U] : Repr (Powerset U) where
  reprPrec s _ := "{" ++ Std.Format.joinSep ((s.sort (· ≤ ·)).map repr) ", " ++ "}"
instance instLinearOrder {U} [LinearOrder U] : LinearOrder (Powerset U) :=
  -- use lexicographic order
  LinearOrder.lift'
    (fun s => (toLex (s.card, s.sort (· ≤ ·)) : ℕ ×ₗ List U))
    (fun _ _ h =>
      (Function.LeftInverse.injective (fun s => Finset.sort_toFinset s (· ≤ ·)))
        (congrArg (fun p => (ofLex p).2) h))
end Display

/- Species instance -/
instance instSpecies : Species Powerset where
  finite := by
    intros U _
    have : Fintype U := Fintype.ofFinite U
    infer_instance
  transport      := fun σ s => s.map σ.toEmbedding
  id_transport   := by intro _ _ f; exact Finset.map_refl
  comp_transport := by
    intro _ _ _ _ _ _ σ τ f
    unfold Powerset at *; simp [Function.comp_def, Finset.map_map]

instance instComputableSpecies : ComputableSpecies Powerset where
  fintype := inferInstance
  decEq   := inferInstance

end Powerset

end Species
