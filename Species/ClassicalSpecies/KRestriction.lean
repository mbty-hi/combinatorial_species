import Species.Basic

instance KRestriction (F: Type → Type) [FS: @Species F] (k: ℕ) : @Species F where
  structures :=
    fun labels =>
      if labels.card == k
      then @Species.structures F FS _ _ labels
      else {}
  transport       := fun σ_bij fu => Species.transport σ_bij fu
  transport_trans := fun σ_bij τ_bij fu => Species.transport_trans σ_bij τ_bij fu
  transport_id    := fun fu => Species.transport_id fu

instance KRestrictionToZero (F: Type → Type) [FS: @Species F] : @Species F := KRestriction F 0
instance KRestrictionToOne  (F: Type → Type) [FS: @Species F] : @Species F := KRestriction F 1
