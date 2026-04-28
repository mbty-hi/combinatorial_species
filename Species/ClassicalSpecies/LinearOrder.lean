import Species.Basic

structure FinStrictLinOrder (U: Type) where
  order: List U
  order_Nodup: order.Nodup

lemma permutations_preserves_nodup:
  ∀ {α: Type} {l: List α},
  l.Nodup → ∀l' ∈ l.permutations, l'.Nodup
:= by
  intro α l lnd
  induction l with
  | nil => simp
  | cons h t =>
    intro l' l'inp
    apply List.mem_permutations.1 at l'inp
    apply List.Nodup.perm lnd (List.Perm.symm l'inp)

def Nodup_List_to_Finset {α: Type} (l: List α) (lnd: l.Nodup) : Finset α := {
  val := Multiset.ofList l,
  nodup := lnd
}

def transport_FinStrictLinOrder
  {U V: Type} (F: FinStrictLinOrder U) {σ: U → V} (σ_bij: σ.Bijective)
: FinStrictLinOrder V := {
  order := F.order.map σ
  order_Nodup := by
    generalize oh : F.order = o
    have ndh : o.Nodup := by rw [← oh]; apply F.order_Nodup
    clear oh
    induction o with
    | nil => simp
    | cons h t ih =>
      simp
      constructor
      . intro x x_in_t ctr
        apply List.nodup_cons.1 at ndh
        obtain ⟨h_nin_t, _⟩ := ndh
        have x_neq_h : x ≠ h := by
          intro ctr; subst ctr; contradiction
        apply Function.Bijective.injective at σ_bij
        apply Function.Injective.eq_iff at σ_bij
        apply σ_bij.1 at ctr; contradiction
      . apply ih (List.Nodup.of_cons ndh)
}

/- TODO workaround noncomputability -/
noncomputable instance LinearOrderSpecies: @Species FinStrictLinOrder where
  structures := fun labels =>
    let ls_list := Finset.toList labels
    let ls_list_Nodup : ls_list.Nodup := by {
      unfold ls_list; apply Finset.nodup_toList
    }
    let perms := ls_list.permutations
    let perms_Nodup_internal : ∀p ∈ perms, p.Nodup := permutations_preserves_nodup (ls_list_Nodup)
    let perms_Nodup_external : perms.Nodup := by
      unfold perms; apply List.nodup_permutations; assumption
    let f := (fun x xinp => FinStrictLinOrder.mk x (perms_Nodup_internal x xinp))
    let perms_ls : List (FinStrictLinOrder _) :=
      List.pmap
        (fun x xinp => FinStrictLinOrder.mk x (perms_Nodup_internal x xinp))
        perms (fun _ is_in => is_in)
    let perms_ls_Nodup : perms_ls.Nodup := by
      apply List.Nodup.pmap
      . intro m n x y eq; simp at eq; subst eq; rfl
      . assumption
    Nodup_List_to_Finset perms_ls perms_ls_Nodup
  transport := by
    intro U V σ σ_bij fu
    apply transport_FinStrictLinOrder fu σ_bij
  transport_trans := by
    unfold transport_FinStrictLinOrder
    simp
  transport_id := by
    unfold transport_FinStrictLinOrder
    simp
