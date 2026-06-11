import Species.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Sort

/- Arrangement: concrete ordering of the elements of the type. -/
@[ext] -- Automatically generate Arrangement.ext
structure Arrangement (U: Type) where
  order   : List U
  nodup   : order.Nodup
  complete: ∀u, u ∈ order

instance instDecEqArrangement {U} [DecidableEq U] : DecidableEq (Arrangement U) :=
  fun a b => decidable_of_iff (a.order = b.order)
    ⟨Arrangement.ext, fun h => congrArg Arrangement.order h⟩

lemma permutations_preserves_nodup {α: Type} {l: List α}:
  l.Nodup → ∀l' ∈ l.permutations, l'.Nodup
:= fun lnd l' l'_in_lp =>
  let lpl' : l.Perm l' := (l'.mem_permutations.1 l'_in_lp).symm
  lnd.perm lpl'

instance instFintypeArrangement {U} [LabelType U] : Fintype (Arrangement U) where
  elems := (
    let base := (Finset.univ (α := U)).sort (· ≤ ·)
    have base_nd : base.Nodup := Finset.sort_nodup _ _
    have base_complete : ∀u, u ∈ base := fun u => (Finset.mem_sort _).mpr (Finset.mem_univ u)
    let perms := base.permutations
    have perms_elements_nd : ∀p ∈ perms, p.Nodup := permutations_preserves_nodup base_nd
    have perms_elements_complete : ∀p ∈ perms, ∀u, u ∈ p :=
      fun p pip u => ((List.mem_permutations.1 pip).mem_iff).mpr (base_complete u)
    let pperms : List (Arrangement U) :=
      perms.pmap
        (fun p hp => ({
          order    := p
          nodup    := perms_elements_nd p hp
          complete := perms_elements_complete p hp
        }: Arrangement U))
        (fun _ h => h)
    pperms.toFinset
  )
  complete := by
    intro o
    have hmem : o.order ∈ ((Finset.univ (α := U)).sort (· ≤ ·)).permutations :=
      List.mem_permutations.mpr
        ((List.perm_ext_iff_of_nodup o.nodup (Finset.sort_nodup _ _)).mpr
          (fun a => by
            rw [Finset.mem_sort]
            exact ⟨fun _ => Finset.mem_univ a, fun _ => o.complete a⟩))
    simp only [List.mem_toFinset]
    exact List.mem_pmap.mpr ⟨o.order, hmem, Arrangement.ext rfl⟩

def transport_Arrangement {U V: Type} (a: Arrangement U) (σ: U ≃ V) : Arrangement V := {
  order    := a.order.map σ
  nodup    := a.nodup.map σ.injective
  complete := fun v => List.mem_map.mpr ⟨σ.symm v, a.complete _, σ.apply_symm_apply v⟩
}

/- Display related instances -/
instance instReprArrangement {U} [Repr U] : Repr (Arrangement U) where
  reprPrec a prec := reprPrec a.order prec
instance instLinearOrderArrangement {U} [LinearOrder U] : LinearOrder (Arrangement U) :=
  LinearOrder.lift' Arrangement.order (fun _ _ h => Arrangement.ext h)

/- Species instance -/
instance instSpeciesArrangement: @Species Arrangement where
  fintype         := inferInstance
  transport       := fun σ s => transport_Arrangement s σ
  transport_trans := by simp [transport_Arrangement]
  transport_id    := by simp [transport_Arrangement]
