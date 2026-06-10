import Species.Basic

/- Note that we do not store labels explicitly. Assuming that the type this is applied to is a
   `LabelType` (which it should be), we can easily recover them anyway. -/
abbrev SE : Type → Type := fun _ => Unit

instance SESpecies : Species SE where
  fintype         := inferInstance
  transport       := fun _ _   => ()
  transport_trans := fun _ _ _ => rfl
  transport_id    := fun _     => Subsingleton.elim _ _
