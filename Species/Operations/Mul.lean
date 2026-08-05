import Species.Basic
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Basic
import Mathlib.Data.Prod.Lex

namespace Species

variable {F G : Type → Type} [Species F] [Species G] {U V : Type}

def mul (F G : Type → Type) (U : Type) : Type :=
  Σ d : U → Bool, F {u // d u = true} × G {u // d u = false}

/- Relabelling a split: `v` falls in the same block as its `σ`-preimage. -/
abbrev transportSplit {U V : Type} (σ : U ≃ V) (split : U → Bool) : V → Bool :=
  split ∘ σ.symm

/- There is a bijection between blocks before and after transport. -/
def blockEquiv {U V} (σ : U ≃ V) (split : U → Bool) (b : Bool)
: {u // split u = b} ≃ {v // transportSplit σ split v = b} :=
  σ.subtypeEquiv (fun u => by simp [Equiv.symm_apply_apply])

/- Species instance -/
instance instSpeciesMul : Species (mul F G) where
  finite := by
    intros U _; unfold mul
    /- Surface instances -/
    haveI : ∀ d : U → Bool, Finite (F {u // d u = true}) :=
      fun d => Species.finite (F := F) (U := {u // d u = true})
    haveI : ∀ d : U → Bool, Finite (G {u // d u = false}) :=
      fun d => Species.finite (F := G) (U := {u // d u = false})
    infer_instance
  transport := fun σ ⟨split, f_struct, g_struct⟩ => ⟨
    transportSplit σ split,
    Species.transport (blockEquiv σ split true) f_struct,
    Species.transport (blockEquiv σ split false) g_struct
  ⟩
  transport_id := by
    rintro U _ ⟨d, f, g⟩; simp [Equiv.refl_symm]
    refine Sigma.ext rfl (heq_of_eq ?_)
    ext <;> simp [blockEquiv, Equiv.subtypeEquiv] <;> apply Species.transport_id
  transport_trans := by
    rintro U V W _ _ _ σ τ ⟨d, f, g⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply Prod.ext
      <;> apply Species.transport_trans (blockEquiv σ d _) (blockEquiv τ (d ∘ σ.symm) _)

instance instSpeciesCompMul [SpeciesComp F] [SpeciesComp G] : SpeciesComp (mul F G) where
  fintype := fun {U} _ => by unfold mul; infer_instance
  decEq := by
    intros U _; unfold mul
    /- Surface instances -/
    haveI : ∀ d : U → Bool, DecidableEq (F {u // d u = true}) :=
      fun d => SpeciesComp.decEq (F := F) (U := {u // d u = true})
    haveI : ∀ d : U → Bool, DecidableEq (G {u // d u = false}) :=
      fun d => SpeciesComp.decEq (F := G) (U := {u // d u = false})
    infer_instance

/- Display related instances -/
variable
  [LabelType U] [LabelType V]
  [∀ d : U → Bool, LinearOrder (F {u // d u = true})]
  [∀ d : U → Bool, LinearOrder (G {u // d u = false})]
  [SpeciesComp F] [SpeciesComp G]
  /- Note that `[∀ d : U → Bool, ∀ b : Bool, LinearOrder (F {u // d u = b})]` would not work. -/

instance instReprMul
  {F G : Type → Type} {U : Type} [LabelType U] [Repr U]
  [∀ d : U → Bool, Repr (F {u // d u = true})]
  [∀ d : U → Bool, Repr (G {u // d u = false})]
: Repr ((mul F G) U) where
  reprPrec x p :=
    let left  := (Finset.univ.filter (x.1 · = true )).sort (· ≤ ·)
    let right := (Finset.univ.filter (x.1 · = false)).sort (· ≤ ·)
    Repr.addAppParen f!"{repr left} ↦ {reprArg x.2.1} · {repr right} ↦ {reprArg x.2.2}" p

-- Get the rank of some value of an ordered finite type (position in the associated order).
def rankOf {α : Type} [Fintype α] [LinearOrder α] (y : α) : ℕ :=
  ((Finset.univ : Finset α).sort (· ≤ ·)).idxOf y

lemma rankOf_injective {α} [Fintype α] [LinearOrder α]
: Function.Injective (rankOf (α := α)) := by
  intro a b h
  have ha : a ∈ (Finset.univ : Finset α).sort (· ≤ ·) := by simp
  exact (List.idxOf_inj ha).mp h

-- We order the components our species according to the labels assigned to the true block and the
-- ranks of their components in according to their own order.
def mulKey (x : mul F G U) : List U ×ₗ (ℕ ×ₗ ℕ) :=
  toLex ((Finset.univ.filter (x.1 · = true)).sort (· ≤ ·), toLex (rankOf x.2.1, rankOf x.2.2))

lemma true_block_contents_determines_split {split₁ split₂ : U → Bool}
  (h :
    (Finset.univ.filter (split₁ · = true)).sort (· ≤ ·)
    = (Finset.univ.filter (split₂ · = true)).sort (· ≤ ·)
  )
: split₁ = split₂ := by
  have hset : Finset.univ.filter (split₁ · = true) = Finset.univ.filter (split₂ · = true) := by
    have := congrArg List.toFinset h
    simpa [Finset.sort_toFinset] using this
  funext u
  have := Finset.ext_iff.mp hset u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
  cases hu1 : split₁ u <;> cases hu2 : split₂ u <;> simp_all

omit [Species F] [Species G] in
lemma mulKey_injective : Function.Injective (mulKey (F := F) (G := G) (U := U)) := by
  rintro ⟨d₁, f₁, g₁⟩ ⟨d₂, f₂, g₂⟩ h
  rw [Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨hL, hf, hg⟩ := h
  have hd : d₁ = d₂ := true_block_contents_determines_split hL
  subst hd
  have roi_f := rankOf_injective hf
  have roi_g := rankOf_injective hg
  subst_vars; simp

instance instLinearOrderMul
  {F G : Type → Type} {α : Type}
  [Species F] [Species G] [SpeciesComp F] [SpeciesComp G] [LabelType α]
  [∀ d : α → Bool, LinearOrder (F {u // d u = true})]
  [∀ d : α → Bool, LinearOrder (G {u // d u = false})]
: LinearOrder ((mul F G) α) :=
  LinearOrder.lift' mulKey mulKey_injective
end Species
