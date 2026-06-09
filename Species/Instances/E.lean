import Species.Basic

/- Note that we do not store labels explicitly. If `_U` is a LabelType, we can recover them
   anyway. -/
abbrev SE (_U : Type) : Type := Unit

instance SESpecies : Species SE where
  fintype         := inferInstance
  transport       := fun _ _ => ()
  transport_trans := fun _ _ _ => rfl
  transport_id    := fun _     => Subsingleton.elim _ _
