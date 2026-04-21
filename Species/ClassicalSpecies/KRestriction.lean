import Species.Basic

instance (F: Type → Type) [FS: @Species F] (k: ℕ) : @Species F where
  structures :=
    fun labels =>
      if labels.card == k
      then @Species.structures F FS _ _ labels
      else {}
  transport := by
    intros U V σ σ_bij fu
    apply Species.transport σ_bij fu
  transport_trans := by
    intros U V W σ σ_bij τ τ_bij fu
    apply Species.transport_trans
  transport_id := by
    intros U fu
    apply Species.transport_id
