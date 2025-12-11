import Init.Control.Lawful.Basic
import Init.Data.List.Perm
import Init.Data.List.Find
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Functor
import Mathlib.Data.List.Permutation
import Mathlib.Logic.Equiv.Embedding
import Mathlib.Order.Defs.LinearOrder
import Species.Basic

-- Linear orders
class StrictLinOrder (α: Type) where
  lt: α → α → Prop
  lt_asymmetric: ∀a b, lt a b → ¬(lt b a)
  lt_irreflexive: ∀a, ¬(lt a a)
  lt_trans: ∀a b c, lt a b → lt b c → lt a c
  lt_connected: ∀a b, a ≠ b → lt a b ∨ lt b a
  -- TODO Only asymmetry and connectedness are strictly required

structure StrictLinOrder_concrete (U: Type) where
  order: List U
  order_nodup: List.Nodup order

/- instance : StrictLinOrder StrictLinOrder_concrete where -/
/-   lt: -/ 

instance (F: Type → Type) (α: ∀U, LinearOrder (F U)) : @Species F where
  structures := fun labels =>
    let ls_list := Finset.toList labels
    let ls_list_Nodup : ls_list.Nodup := by {
      unfold ls_list; apply Finset.nodup_toList
    }
    let perms := ls_list.permutations
    let perms_Nodup : ∀p ∈ perms, p.Nodup := by {
      intro p p_in_perms
      sorry
    }
    {List.map
      (StrictLinOrder_concrete 

      )
      (List.permutations (Finset.toList ls))}
  transport := by
    intro U V σ σ_bij fu
    apply (Set.image σ fu)
  transport_trans := by
    intro U V W σ σ_bij τ τ_bij f
    simp; rw [Set.image_image]
  transport_id := by simp
