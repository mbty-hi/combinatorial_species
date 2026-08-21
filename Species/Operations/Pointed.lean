import Species.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Prod.Lex

namespace Species

variable {F : Type → Type} [Species F] {U : Type}

def Pointed (F : Type → Type) (U : Type) : Type := U × F U

instance instSpeciesPointed : Species (Pointed F) where
  finite := by
    intros U _; unfold Pointed
    haveI := Species.finite (F := F) (U := U)
    infer_instance
  transport      := fun {U V} _ _ σ x       => (σ x.1, Species.transport σ x.2)
  id_transport   := fun {U} _ f             => by simp [Species.id_transport]
  comp_transport := fun {U V W} _ _ _ σ τ f => by simp [Species.comp_transport]

instance instSpeciesCompPointed [SpeciesComp F] : SpeciesComp (Pointed F) where
  fintype := fun {U} _  => show Fintype (U × F U) from inferInstance
  decEq := by
    intros U _; unfold Pointed
    haveI := SpeciesComp.decEq (F := F) (U := U)
    infer_instance

end Species
