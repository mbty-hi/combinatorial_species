import Species.Basic
import Species.Computable
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Basic
import Mathlib.Data.Prod.Lex

namespace Species

def Mul (F G : Type → Type) (U : Type) : Type :=
  Σ d : U → Bool, F {u // d u = false} × G {u // d u = true}

namespace Mul

variable {F G : Type → Type} [Species F] [Species G] {U V : Type}

/- Relabelling a split: `v` falls in the same block as its `σ`-preimage. -/
abbrev transportSplit {U V : Type} (σ : U ≃ V) (split : U → Bool) : V → Bool :=
  split ∘ σ.symm

/- There is a bijection between blocks before and after transport. -/
def blockEquiv {U V} (σ : U ≃ V) (split : U → Bool) (b : Bool)
: {u // split u = b} ≃ {v // transportSplit σ split v = b} :=
  σ.subtypeEquiv (fun u => by simp [Equiv.symm_apply_apply])

/- Species instance -/
instance instSpecies : Species (Mul F G) where
  finite := by
    intros U _; unfold Mul
    /- Surface instances -/
    have : ∀ d : U → Bool, Finite (F {u // d u = false}) :=
      fun d => Species.finite (F := F) (U := {u // d u = false})
    have : ∀ d : U → Bool, Finite (G {u // d u = true}) :=
      fun d => Species.finite (F := G) (U := {u // d u = true})
    infer_instance
  transport := fun σ ⟨split, f_struct, g_struct⟩ => ⟨
    transportSplit σ split,
    Species.transport (blockEquiv σ split false) f_struct,
    Species.transport (blockEquiv σ split true) g_struct
  ⟩
  id_transport := by
    rintro U _ ⟨d, f, g⟩; simp [Equiv.refl_symm]
    refine Sigma.ext rfl (heq_of_eq ?_)
    ext <;> simp [blockEquiv, Equiv.subtypeEquiv] <;> apply Species.id_transport
  comp_transport := by
    rintro U V W _ _ _ σ τ ⟨d, f, g⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Prod.ext
      <;> apply Species.comp_transport (blockEquiv σ d _) (blockEquiv τ (d ∘ σ.symm) _)

instance instComputable {F G : Type → Type} [ComputableSpecies F] [ComputableSpecies G]
: ComputableSpecies (Mul F G) where
  fintype := fun {U} _ => by unfold Mul; infer_instance
  decEq := by
    intros U _; unfold Mul
    /- Surface instances -/
    haveI : ∀ d : U → Bool, DecidableEq (F {u // d u = false}) :=
      fun d => ComputableSpecies.decEq (F := F) (U := {u // d u = false})
    haveI : ∀ d : U → Bool, DecidableEq (G {u // d u = true}) :=
      fun d => ComputableSpecies.decEq (F := G) (U := {u // d u = true})
    infer_instance

/- Display related instances -/
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
  have ha : a ∈ (Finset.univ : Finset α).sort (· ≤ ·) := by simp
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
    simpa [Finset.sort_toFinset] using this
  funext u
  have := Finset.ext_iff.mp hset u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  cases hu1 : split₁ u <;> cases hu2 : split₂ u <;> simp_all

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

-- Other results
@[simp] def deciderCast {U : Type} {d d' : U → Bool} (h : d = d') (b : Bool)
: {u // d u = b} ≃ {u // d' u = b} :=
  Equiv.subtypeEquivRight fun u => by rw [h]

@[simp] theorem deciderCast_rfl {U : Type} (d : U → Bool) (b : Bool)
: deciderCast (rfl : d = d) b = Equiv.refl _ :=
  Equiv.ext fun _ => Subtype.ext rfl

theorem mul_ext {S T : Type → Type} [Species S] [Species T] {U : Type} [Finite U]
  {d d' : U → Bool}
  {s : S {u // d u = false}} {s' : S {u // d' u = false}}
  {t : T {u // d u = true}}  {t' : T {u // d' u = true}}
  (hd : d = d')
  (hs : Species.transport (deciderCast hd false) s = s')
  (ht : Species.transport (deciderCast hd true) t = t')
: (⟨d, (s, t)⟩ : Mul S T U) = ⟨d', (s', t')⟩ := by
  subst hd
  simp only [deciderCast_rfl, Species.id_transport] at hs ht
  rw [hs, ht]

theorem mul_transport_mk
  {S T : Type → Type} [Species S] [Species T] {α β : Type} [Finite α] [Finite β]
  (σ : α ≃ β) (d : α → Bool) (s : S {u // d u = false}) (t : T {u // d u = true})
: Species.transport (F := Mul S T) σ ⟨d, (s, t)⟩
  = ⟨
    transportSplit σ d,
    (Species.transport (blockEquiv σ d false) s,
    Species.transport (blockEquiv σ d true) t)
  ⟩
:= rfl

end Mul

end Species
