module

public import Species.Basic
public import Species.Computable
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.List.Basic
public import Mathlib.Order.Prod.Lex.Basic

@[expose] public section

namespace Species

def Mul (F G : Type → Type) (U : Type) : Type :=
  Σ (d : U → Bool), F {u // d u = false} × G {u // d u = true}

namespace Mul

variable {F G : Type → Type} [Species F] [Species G] {U V : Type} [Finite U] [Finite V]

/- Relabelling a split: `v` falls in the same block as its `σ`-preimage. -/
abbrev transportSplit {U V : Type} (σ : U ≃ V) (split : U → Bool) : V → Bool :=
  split ∘ σ.symm

/- There is a bijection between blocks before and after transport. -/
def blockEquiv {U V} (σ : U ≃ V) (split : U → Bool) (b : Bool)
: {u // split u = b} ≃ {v // transportSplit σ split v = b} :=
  σ.subtypeEquiv (fun u => by simp only [Function.comp_apply, Equiv.symm_apply_apply])

@[simp] def deciderCast {U : Type} {d d' : U → Bool} (h : d = d') (b : Bool)
: {u // d u = b} ≃ {u // d' u = b} :=
  Equiv.subtypeEquivRight fun u => by rw [h]

@[simp] theorem deciderCast_rfl {U : Type} (d : U → Bool) (b : Bool)
: deciderCast (rfl : d = d) b = Equiv.refl _ :=
  Equiv.ext fun _ => Subtype.ext rfl

theorem ext
  {d d' : U → Bool}
  {f : F {u // d u = false}} {f' : F {u // d' u = false}}
  {g : G {u // d u = true}}  {g' : G {u // d' u = true}}
  (hd : d = d')
  (hf : transport (deciderCast hd false) f = f')
  (hg : transport (deciderCast hd true ) g = g')
: (⟨d, (f, g)⟩ : Mul F G U) = ⟨d', (f', g')⟩ := by
  subst hd; simp only [deciderCast_rfl, id_transport] at hf hg; rw [hf, hg]

instance instSpecies : Species (Mul F G) where
  finite := by
    intros U _; unfold Mul
    /- Surface instances -/
    have _ : ∀ (d : U → Bool), Finite (F {u // d u = false}) :=
      fun d => finite (F := F) (U := {u // d u = false})
    have _ : ∀ (d : U → Bool), Finite (G {u // d u = true}) :=
      fun d => finite (F := G) (U := {u // d u = true})
    infer_instance
  transport := fun σ ⟨split, f_struct, g_struct⟩ => ⟨
    transportSplit σ split,
    transport (blockEquiv σ split false) f_struct,
    transport (blockEquiv σ split true) g_struct
  ⟩
  id_transport := by
    rintro U _ ⟨d, f, g⟩; simp only [Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply]
    refine Sigma.ext rfl (heq_of_eq ?_)
    ext
    · simp only [
        blockEquiv, Equiv.subtypeEquiv, Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply,
        Subtype.coe_eta
      ]; apply id_transport
    · simp only [blockEquiv, Equiv.subtypeEquiv, Function.comp_apply, Equiv.refl_symm,
      Equiv.refl_apply, Subtype.coe_eta]; apply id_transport
  comp_transport := by
    rintro U V W _ _ _ σ τ ⟨d, f, g⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Prod.ext <;> apply comp_transport (blockEquiv σ d _) (blockEquiv τ (d ∘ σ.symm) _)

instance instComputable {F G : Type → Type} [ComputableSpecies F] [ComputableSpecies G]
: ComputableSpecies (Mul F G) where
  fintype := fun {U} _ => by unfold Mul; infer_instance
  decEq := by
    intros U _; unfold Mul
    /- Surface instances -/
    haveI _ : ∀ (d : U → Bool), DecidableEq (F {u // d u = false}) :=
      fun d => ComputableSpecies.decEq (F := F) (U := {u // d u = false})
    haveI _ : ∀ (d : U → Bool), DecidableEq (G {u // d u = true}) :=
      fun d => ComputableSpecies.decEq (F := G) (U := {u // d u = true})
    infer_instance

@[simp] lemma transport_mk
  (σ : U ≃ V) (d : U → Bool) (f : F {u // d u = false}) (g : G {u // d u = true})
: transport (F := Mul F G) σ (⟨d, (f, g)⟩ : Mul F G U)
  = ⟨transportSplit σ d, (transport (blockEquiv σ d false) f, transport (blockEquiv σ d true) g)⟩
:= rfl

section Display

variable
  {F G : Type → Type} [ComputableSpecies F] [ComputableSpecies G] {U V : Type}
  [LabelType U] [LabelType V]
  [∀ d : U → Bool, LinearOrder (F {u // d u = false})]
  [∀ d : U → Bool, LinearOrder (G {u // d u = true})]
  /- Note that `[∀ d : U → Bool, ∀ b : Bool, LinearOrder (F {u // d u = b})]` would not work. -/

instance instRepr
  [Repr U]
  [∀ d : U → Bool, Repr (F {u // d u = false})]
  [∀ d : U → Bool, Repr (G {u // d u = true })]
: Repr ((Mul F G) U) where
  reprPrec x p :=
    let left  := (Finset.univ.filter (x.1 · = false)).sort (· ≤ ·)
    let right := (Finset.univ.filter (x.1 · = true )).sort (· ≤ ·)
    Repr.addAppParen f!"{repr left} ↦ {reprArg x.2.1} · {repr right} ↦ {reprArg x.2.2}" p

-- Get the rank of some value of an ordered finite type (position in the associated order).
def rankOf {α : Type} [Fintype α] [LinearOrder α] (y : α) : ℕ :=
  ((Finset.univ : Finset α).sort (· ≤ ·)).idxOf y

lemma rankOf_inj {α} [Fintype α] [LinearOrder α]
: Function.Injective (rankOf (α := α)) := by
  intro a b h
  have ha : a ∈ (Finset.univ : Finset α).sort (· ≤ ·) := by
    simp only [Finset.mem_sort, Finset.mem_univ]
  exact (List.idxOf_inj ha).mp h

-- We order the components our species according to the labels assigned to the false block and the
-- ranks of their components in according to their own order.
def mulKey (x : Mul F G U) : List U ×ₗ (ℕ ×ₗ ℕ) :=
  toLex ((Finset.univ.filter (x.1 · = false)).sort (· ≤ ·), toLex (rankOf x.2.2, rankOf x.2.1))

lemma false_block_contents_determines_split {split₁ split₂ : U → Bool}
  (h :
    (Finset.univ.filter (split₁ · = false)).sort (· ≤ ·)
    = (Finset.univ.filter (split₂ · = false)).sort (· ≤ ·)
  )
: split₁ = split₂ := by
  have hset : Finset.univ.filter (split₁ · = false) = Finset.univ.filter (split₂ · = false) := by
    have := congrArg List.toFinset h
    simpa only [Finset.sort_toFinset] using this
  funext u
  have := Finset.ext_iff.mp hset u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  cases hu1 :
    split₁ u <;> cases hu2 : split₂ u <;>
    simp_all only [Bool.true_eq_false, iff_false, not_true_eq_false]

lemma mulKey_inj : Function.Injective (mulKey (F := F) (G := G) (U := U)) := by
  rintro ⟨d₁, f₁, g₁⟩ ⟨d₂, f₂, g₂⟩ h
  simp only [mulKey, toLex_inj, Prod.ext_iff] at h
  obtain ⟨hL, hf, hg⟩ := h
  have hd : d₁ = d₂ := false_block_contents_determines_split hL
  subst hd
  have roi_f := rankOf_inj hf
  have roi_g := rankOf_inj hg
  subst_vars; rfl

instance instLinearOrder : LinearOrder ((Mul F G) U) :=
  LinearOrder.lift' mulKey mulKey_inj

end Display
end Mul
end Species
end
