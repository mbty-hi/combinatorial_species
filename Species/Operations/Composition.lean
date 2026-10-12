import Species.Basic
import Species.Labels.LabelType
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Sigma.Order
import Mathlib.Order.PiLex

namespace Species

/- We encode composition as a decidable equivalence relation on the label type (U → U → Bool)
   (like a coloring, except that there is no order between equivalence classes, so we do not need to
   manually correct for overcounting). -/

/- To define this, we first need a notion of a decidable equivalence relation. A setoid almost fits
   the bill, but we care about computability, so we use `(U → U → Bool)` instead of
   `U → U → Prop`. -/
structure DecSetoid (α : Type) where
  d     : α → α → Bool
  iseqv : Equivalence (fun x y => d x y = true)

namespace DecSetoid
variable {α β : Type}

-- We can easily get a standard setoid from a decidable one.
def toSetoid (s : DecSetoid α) : Setoid α :=
  ⟨fun x y => s.d x y = true, s.iseqv⟩

-- We need a way of remapping `DecSetoid`s to define `transport`.
def map (s : DecSetoid α) (σ : α ≃ β) : DecSetoid β where
  d     := fun x y => s.d (σ.symm x) (σ.symm y)
  iseqv := (s.toSetoid.comap σ.symm).iseqv

/- Interactions with quotienting arise in the `Composition` species since the set of blocks is
   defined via the quotienting of `U` by `d`. -/

-- Transporting the `DecSetoid` along `σ` transports the quotient along `σ`.
def quotEquiv (s : DecSetoid α) (σ : α ≃ β)
: Quotient s.toSetoid ≃ Quotient (s.map σ).toSetoid := by
  apply Quotient.congr σ; intro x y
  unfold toSetoid map; simp

/- `s.quotEquiv` at `Equiv.refl` is just the identity equiv (i.e., remapping along `Equiv.refl`
   leaves the `DecSetoid` unchanged). -/
@[simp] theorem quotEquiv_refl (s : DecSetoid α)
: s.quotEquiv (Equiv.refl α) = Equiv.refl (Quotient s.toSetoid) := by
  ext ⟨q⟩ -- for `Equiv`s, showing that the `toFun`s agree pointwise is sufficient
  rfl

/- The `α`s that land in `block` after relabelling by `σ` correspond exactly to the `β`s that are
   already in it. -/
def blockEquiv (s : DecSetoid α) (σ : α ≃ β) (block : Quotient (s.map σ).toSetoid)
: {x // Quotient.mk s.toSetoid x = (s.quotEquiv σ).symm block}
  ≃ {x // Quotient.mk (s.map σ).toSetoid x = block}
where
  toFun := by
    rintro ⟨block_rep, hblock_rep⟩; constructor
    case val      => exact σ block_rep
    case property => have h := congrArg (s.quotEquiv σ) hblock_rep; simp [quotEquiv] at h; exact h
  invFun := by
    rintro ⟨block_rep, hblock_rep⟩; constructor
    case val      => exact σ.symm block_rep
    case property => subst block; apply (s.quotEquiv σ).injective; simp [quotEquiv]
  left_inv  := fun ⟨block, _⟩ => Subtype.ext (σ.symm_apply_apply block)
  right_inv := fun ⟨block, _⟩ => Subtype.ext (σ.apply_symm_apply block)

/- In the rest of the `DecSetoid` section, we construct a series of objects, culminating in a
   `LinearOrder` instance. This is something that the definition of the computable extension of the
   composition species requires. -/

-- We assume that `α` is now a `LabelType`, as this is meant for a `SpeciesComp` context.
variable [LabelType α]

-- Decidable equality for blocks based on the decidability of `s.d x y = true`.
instance instDecEqQuot (s : DecSetoid α) : DecidableEq (Quotient s.toSetoid) :=
  @Quotient.decidableEq α s.toSetoid (fun x y => inferInstanceAs (Decidable (s.d x y = true)))

-- Extract all labels belonging to the given block.
def blockFinset (s : DecSetoid α) (block : Quotient s.toSetoid) : Finset α :=
  Finset.univ.filter (fun x => Quotient.mk s.toSetoid x = block)

-- Blocks are non-empty (obviously).
theorem blockFinset_nonempty (s : DecSetoid α) (block : Quotient s.toSetoid)
: (s.blockFinset block).Nonempty := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep block
  exact ⟨x, by simp [blockFinset]⟩

-- Get the minimum item of a given block according to `α`'s order.
def blockMin (s : DecSetoid α) (block : Quotient s.toSetoid) : α :=
  (s.blockFinset block).min' (s.blockFinset_nonempty block)

-- A block is fully determined by its minimum.
theorem blockMin_mk (s : DecSetoid α) (block : Quotient s.toSetoid)
: Quotient.mk s.toSetoid (s.blockMin block) = block := by
  have h := Finset.min'_mem (s.blockFinset block) (s.blockFinset_nonempty block)
  simp [blockFinset] at h; exact h

theorem blockMin_injective (s : DecSetoid α) : Function.Injective s.blockMin := by
  intros block₁ block₂ h
  rw [← s.blockMin_mk block₁, ← s.blockMin_mk block₂, h]

-- This linear order ranks blocks based on their minimal item in `α`'s order.
instance instLinearOrderQuot (s : DecSetoid α) : LinearOrder (Quotient s.toSetoid) :=
  LinearOrder.lift' s.blockMin s.blockMin_injective

-- Since `α` is a `LabelType`, we can build a matrix summarizing the results of all possible
-- applications of `s.d` following `α`'s linear order.
def explicit_mapping (s : DecSetoid α) : List (List Bool) :=
  let labels := (Finset.univ : Finset α).sort (· ≤ ·)
  labels.map (fun x => labels.map (s.d x))

-- That mapping is injective.
theorem explicit_mapping_injective : Function.Injective (explicit_mapping (α := α)) := by
  intro ⟨sd, seq⟩ ⟨td, teq⟩ h; simp [explicit_mapping] at *
  funext a a'; exact h a a'

-- We also need an order for comparing different `DecSetoid`s in addition to the one for blocks.
instance instLinearOrderDecSetoid : LinearOrder (DecSetoid α) :=
  LinearOrder.lift' explicit_mapping explicit_mapping_injective

end DecSetoid

-- The actual operation definition.
structure Composition (F G: Type → Type) (U: Type) where
  partition: DecSetoid U
  outer    : F (Quotient partition.toSetoid)
  inner    : Π (eqv_class : Quotient partition.toSetoid), G { x // ⟦x⟧ = eqv_class }

namespace Composition
variable {U V W : Type} [Finite U] [Finite V] [Finite W]
variable {F G : Type → Type} [Species F] [Species G]

def transport (σ : U ≃ V) (c : Composition F G U) : Composition F G V where
  partition := c.partition.map σ
  outer     := Species.transport (c.partition.quotEquiv σ) c.outer
  inner     :=
    fun b =>
      Species.transport
        (c.partition.blockEquiv σ b)
        (c.inner ((c.partition.quotEquiv σ).symm b))

theorem id_transport (c : Composition F G U) : transport (Equiv.refl U) c = c := by
  obtain ⟨p, o, i⟩ := c; simp only [transport, Composition.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  . apply heq_of_eq; rw [DecSetoid.quotEquiv_refl]; exact Species.id_transport o
  . apply heq_of_eq; funext b; refine Quotient.inductionOn b fun x => Species.id_transport _

theorem comp_transport (σ : U ≃ V) (τ : V ≃ W) (c : Composition F G U)
: transport (σ.trans τ) c = (transport τ ∘ transport σ) c := by
  obtain ⟨p, o, i⟩ := c
  simp only [transport, Function.comp_apply, Composition.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  . apply heq_of_eq
    have foo := Species.comp_transport (p.quotEquiv σ) ((p.map σ).quotEquiv τ) o; simp [← foo]
    congr; ext ⟨q⟩; rfl
  . apply heq_of_eq
    apply (funext fun b => ?_)
    refine Quotient.inductionOn b fun z => ?_
    exact Species.comp_transport
      (p.blockEquiv σ (((p.map σ).quotEquiv τ).symm (Quotient.mk _ z)))
      ((p.map σ).blockEquiv τ (Quotient.mk _ z)) _

-- Expressing composition as a dependent triple.
def equivSigma
: Composition F G U
  ≃ Σ s : DecSetoid U, F (Quotient s.toSetoid) × ∀ b, G {x // Quotient.mk s.toSetoid x = b}
where
  toFun c     := ⟨c.partition, c.outer, c.inner⟩
  invFun      := fun ⟨s, f, g_blocks⟩ => ⟨s, f, g_blocks⟩
  left_inv _  := rfl
  right_inv _ := rfl

-- Required for `Finite.of_equiv`.
instance instFiniteDecSetoid {α : Type} [Finite α] : Finite (DecSetoid α) :=
  Finite.of_injective (fun s => s.d) (fun s₁ s₂ h => by cases s₁; cases s₂; simpa using h)

example {U : Type} [Finite U] (s : DecSetoid U) : True := by
  have h1 : Finite (Quotient s.toSetoid) := by infer_instance
  have h2 : Finite (F (Quotient s.toSetoid)) := by infer_instance
  have h3 : Finite ((b : Quotient s.toSetoid) → G { x // ⟦x⟧ = b }) := by infer_instance
  trivial

instance instSpeciesComposition : Species (Composition F G) where
  finite         := Finite.of_equiv _ equivSigma.symm
  transport      := transport
  id_transport   := id_transport
  comp_transport := comp_transport

/- We are missing a bunch of instances for the definition of the computable extension of the
   `Composition` species to go through. Most of these are just glue. -/

instance {α : Type} [LabelType α] : DecidableEq (DecSetoid α) :=
  fun s₁ s₂ =>
    decidable_of_iff (∀ x y, s₁.d x y = s₂.d x y)
      ⟨fun h => by cases s₁; cases s₂; congr 1; funext x y; exact h x y,
       fun h _ _ => by rw [h]⟩

instance decidableEquivalenceBool {α : Type} [Fintype α] [DecidableEq α] (f : α → α → Bool)
: Decidable (Equivalence (fun x y => f x y = true)) :=
  decidable_of_iff
    ((∀ x, f x x = true) -- reflexive
      ∧ (∀ x y, f x y = true → f y x = true) -- symmetric
      ∧ (∀ x y z, f x y = true → f y z = true → f x z = true) -- transitive
    )
    ⟨fun ⟨hr, hs, ht⟩ =>
      ⟨hr, fun {x y} h => hs x y h, fun {x y z} h h' => ht x y z h h'⟩,
      fun h => ⟨h.refl, fun _ _ => h.symm, fun _ _ _ => h.trans⟩
    ⟩

instance instDecEqOfSpecies {F : Type → Type} [SpeciesComp F] {U : Type} [LabelType U]
: DecidableEq (F U) :=
  SpeciesComp.decEq

instance instFintypeQuot {α : Type} [LabelType α] (s : DecSetoid α)
: Fintype (Quotient s.toSetoid) :=
  @Quotient.fintype α _ s.toSetoid (fun x y => inferInstanceAs (Decidable (s.d x y = true)))

instance instFintypeDecSetoid {α : Type} [LabelType α] : Fintype (DecSetoid α) :=
  Fintype.ofSurjective
    (fun p : {f : α → α → Bool // Equivalence (fun x y => f x y = true)} => ⟨p.1, p.2⟩)
    (fun s => ⟨⟨s.d, s.iseqv⟩, rfl⟩)

instance instDecEqCompFiber
  {U : Type} [LabelType U] {F G : Type → Type} [SpeciesComp F] [SpeciesComp G] (s : DecSetoid U)
: DecidableEq
  (F (Quotient s.toSetoid) × ((b : Quotient s.toSetoid) → G {x // Quotient.mk s.toSetoid x = b})) :=
instDecidableEqProd

instance instSpeciesCompComposition {F G : Type → Type} [SpeciesComp F] [SpeciesComp G]
: SpeciesComp (Composition F G) where
  fintype := Fintype.ofEquiv _ equivSigma.symm
  decEq   := Equiv.decidableEq equivSigma
end Composition

/- Display related instances -/
/- We display via `F`'s representation, with each block printed as, e.g.,
  `<[1, 3] ↦ "G block on {1, 3}">`.
   Just like for `Mul`, we must be careful about typeclass constraints.
   For instance, the natural `[∀ (X : Type) [LinearOrder X], LinearOrder (F X)]` is too complex for
   typeclass synthesis: we can generate a perfectly fine `LinearOrder` based on it, but typeclass
   resolution would fail in practice. We have to be painfully explicit about _many_ things to
   compensate. To be fair, Pi types with instance arguments are not the simplest usecase one could
   think of. -/
variable {F G : Type → Type} {U : Type} [LabelType U]

section LinearOrder
/- Lexicographic order: first on equivalence classes, then outer, finishing with inner:
   The `outer` and `inner` species do have linear orders, but these assume fixed label types. We
   can't rely on these alone to compare, e.g., `F {1, 2}` to `F {3}`.
   Instead, we start by ordering by equivalence classes:
   `[{3}, {1, 2}] < [{1}, {2, 3}] < [{1, 2, 3}]`
   Using the order on the equivalence classes is of course not enough, as, e.g., `F {1, 2}` can
   usually be built in several way. For instance, if `F` is `L`, then we have `1 < 2` and `2 < 1`.
   This is where the species' preexisting linear order becomes useful.
   Here, we have two nested species instead of the single `F` from the example. The same logic
   applies for both levels of nesting. We consider the linear order on the outer species first as
   this feels more natural. -/

abbrev Key :=
  Σₗ p : DecSetoid U,
  F (Quotient p.toSetoid) ×ₗ List (Σₗ b : Quotient p.toSetoid, G {x // ⟦x⟧ = b})

def toKey (c : Composition F G U) : @Key F G U :=
  let blocks := (Finset.univ.image (Quotient.mk c.partition.toSetoid)).sort (· ≤ ·)
  toLex ⟨c.partition, toLex (c.outer, blocks.map fun b => toLex ⟨b, c.inner b⟩)⟩

lemma toKey_inj : Function.Injective (@toKey F G U _) := by
  rintro ⟨p₁, o₁, i₁⟩ ⟨p₂, o₂, i₂⟩ h
  simp [toKey] at h; obtain ⟨peq, oeq⟩ := h; subst peq
  simp [heq_eq_eq] at oeq; obtain ⟨oeq, ieq⟩ := oeq; subst oeq; simp
  ext ⟨x⟩; exact ieq x

instance instLinearOrderComposition
  [∀ s : DecSetoid U, LinearOrder (F (Quotient s.toSetoid))]
  [∀ (s : DecSetoid U) (c : Quotient s.toSetoid), LinearOrder (G {x // ⟦x⟧ = c})]
: LinearOrder ((Composition F G) U) :=
  LinearOrder.lift' toKey toKey_inj
end LinearOrder

section Repr
/- We label the outer structure (`F`) with a block dependently-paired with its inner structure
   (`G`). This type contains exactly the data we need to represent a block. -/
abbrev BlockLabel (s : DecSetoid U) (inner : ∀ q : Quotient s.toSetoid, F {x // ⟦x⟧ = q}) : Type :=
  {p : Σ q : Quotient s.toSetoid, F {x // ⟦x⟧ = q} // p.2 = inner p.1}

def Composition.quotientEquivBlockLabel (c : Composition F G U)
: Quotient c.partition.toSetoid ≃ BlockLabel c.partition c.inner where
  toFun q    := ⟨⟨q, c.inner q⟩, rfl⟩
  invFun p   := p.1.1
  left_inv _ := rfl
  right_inv  := by rintro ⟨⟨q, g⟩, h⟩; simp at h; subst h; rfl

instance instReprBlockLabel
  [Repr U] (s : DecSetoid U) (inner : ∀ q : Quotient s.toSetoid, F {x // ⟦x⟧ = q})
  [∀ q : Quotient s.toSetoid, Repr (F {x // ⟦x⟧ = q})]
: Repr (BlockLabel s inner) :=
  ⟨fun ⟨⟨q, g⟩, _⟩ _ => f!"<{repr ((s.blockFinset q).sort (· ≤ ·))} ↦ {repr g}>"⟩

instance instLinearOrderBlockLabel
  (s : DecSetoid U) (inner : ∀ q : Quotient s.toSetoid, F {x // ⟦x⟧ = q})
  [LinearOrder (Quotient s.toSetoid)]
: LinearOrder (BlockLabel s inner) :=
  LinearOrder.lift'
    (fun p => p.1.1)
    (by rintro ⟨⟨q, g⟩, h⟩ ⟨⟨q', g'⟩, h'⟩ q_eq; dsimp at h h'; subst_vars; rfl)

instance instReprComposition
  [Repr U] [Species F] [Species G]
  [∀ (s : DecSetoid U) (inner : ∀ q : Quotient s.toSetoid, G {x // ⟦x⟧ = q}),
    Repr (F (BlockLabel s inner))
  ]
  [∀ (s : DecSetoid U) (q : Quotient s.toSetoid), Repr (G {x // ⟦x⟧ = q})]
: Repr (Composition F G U) where
  reprPrec c p :=
    haveI : ∀ q : Quotient c.partition.toSetoid, Finite (G {x // ⟦x⟧ = q}) :=
      fun _ => Species.finite
    reprPrec (Species.transport c.quotientEquivBlockLabel c.outer) p
end Repr
end Species
