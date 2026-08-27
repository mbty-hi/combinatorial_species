import Species.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

namespace Species

def Powerset : Type → Type := Finset

instance instFintypePowerset {U} [Fintype U] : Fintype (Powerset U) :=
  inferInstanceAs (Fintype (Finset U))

/- Display related instances -/
namespace Display
instance instReprPowerset {U : Type} [LinearOrder U] [Repr U] : Repr (Powerset U) where
  reprPrec s _ := "{" ++ Std.Format.joinSep ((s.sort (· ≤ ·)).map repr) ", " ++ "}"
instance instLinearOrderPowerset {U} [LinearOrder U] : LinearOrder (Powerset U) :=
  -- use lexicographic order
  LinearOrder.lift'
    (fun s => (toLex (s.card, s.sort (· ≤ ·)) : ℕ ×ₗ List U))
    (fun _ _ h =>
      (Function.LeftInverse.injective (fun s => Finset.sort_toFinset s (· ≤ ·)))
        (congrArg (fun p => (ofLex p).2) h))
end Display

/- Species instance -/
instance instSpeciesPowerset : Species Powerset where
  finite := by
    intros U _
    haveI : Fintype U := Fintype.ofFinite U
    infer_instance
  transport      := fun σ s => s.map σ.toEmbedding
  id_transport   := by intro _ f; simp
  comp_transport := by intro _ _ _ σ τ f; simp [Finset.map_map]

instance instSpeciesCompPowerset : SpeciesComp Powerset where
  fintype := inferInstance
  decEq   := inferInstance

end Species
