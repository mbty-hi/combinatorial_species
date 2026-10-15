module

public import Species.Basic
public import Species.Computable
public import Mathlib.Data.Fintype.Perm

@[expose] public section

namespace Species

/-- Singletons -/
def X (U : Type) := Fin 1 ≃ U

namespace X

instance instFintype {U} [Fintype U] [DecidableEq U] : Fintype (X U) :=
  inferInstanceAs (Fintype (Fin 1 ≃ U))
instance instSubsingleton {U} : Subsingleton (X U) :=
  inferInstanceAs (Subsingleton (Fin 1 ≃ U))

section Display

instance instRepr {U} [Repr U] : Repr (X U) where reprPrec x _ := reprPrec (x.1 0) 0
instance instLinearOrder {U} : LinearOrder (X U) := .ofSubsingleton

end Display

instance instSpecies : Species X where
  finite         := inferInstance
  transport      := fun σ e => e.trans σ
  id_transport   := by intro _ _ e; rfl
  comp_transport := by intro _ _ _ _ _ _ σ τ e; unfold X at *; simp only [Equiv.trans_assoc]

instance instComputableSpecies : ComputableSpecies X where
  fintype := inferInstance
  decEq   := inferInstance

end X
end Species
end
