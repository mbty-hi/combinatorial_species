import Species.Basic

structure SSingleton {U: Type} where
  value : U
open SSingleton

instance : @Species @SSingleton where
  structures :=
    fun labels => by
      apply Finset.map
      . constructor; rotate_left; apply SSingleton.mk
        unfold Function.Injective; intros a₁ a₂ h; lia
      . apply labels
  transport := by
    intros U V σ σ_bij ssing_u
    constructor; apply (σ ssing_u.value)
  transport_trans := by simp
  transport_id := by simp
