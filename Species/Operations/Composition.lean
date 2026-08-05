/- TODO rm unused imports -/
import Species.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Order.Partition.Basic

/- Previous definition of `Comp`, but lead to noncomputability -/
/- /1- The type of `B`s belonging to `P.parts` -1/ -/
/- abbrev Blocks {U : Type} (P : Partition (Set.univ (α := U))) : Type := -/
/-   {B // B ∈ P.parts} -/
/- def Comp (F G : Type → Type) (U : Type) : Type := -/
/-   Σ P : Partition (Set.univ (α := U)), -/
/-   /1- F-structure over blocks -1/ -/
/-   F (Blocks P) -/
/-   /1- A unique G-structure is defined over the contents of each block -1/ -/
/-   × (∀ B : Blocks P, G (↥B.val)) -/

-- A surjective mapping putting labels into (non-empty) block.
structure Coloring (U : Type) (n : ℕ) where
  color : U → Fin n                 -- each label belongs to a block
  surj  : Function.Surjective color -- blocks are non-empty

-- The `Comp` structure, but without quotienting: not enough as ({1}, {2}) and ({2}, {1}) should be
-- considered the same.
def CompRaw (F G : Type → Type) (U : Type) (n : ℕ) : Type :=
  Σ c : Coloring U n,
  F (Fin n) ×                           -- F-structure on the set of blocks (indexed by Fin n)
  (∀ i : Fin n, G {u // c.color u = i}) -- G-structure on each block

-- To get from `CompRaw` to `Comp`, we need a notion of relabelling.

-- Relabel `CompRaw` via `p`.
def relabel
  {F G : Type → Type} [Species F] {U : Type} {n : ℕ} (cr : CompRaw F G U n) (p : Equiv.Perm (Fin n))
: CompRaw F G U n :=
  /- "The set of elements whose color is the preimage of `i` by `p`"
     is the same as
     "The set of elements whose color is mapped to `i` by `p`" -/
  let blockEq {U n} (color : U → Fin n) (p : Equiv.Perm (Fin n)) (i : Fin n)
  : {u // color u = p.symm i} = {u // p (color u) = i} :=
    congrArg Subtype (funext fun u => propext
        ⟨fun h => by rw [h, p.apply_symm_apply], fun h => by rw [← h, p.symm_apply_apply]⟩)
  /- The relabeling operation itself -/
  ⟨
    ⟨
      fun u => p (cr.1.color u),
      by intro i; obtain ⟨u, hu⟩ := cr.1.surj (p.symm i); exact ⟨u, by simp [hu]⟩
    ⟩,
    Species.transport p cr.2.1,
    fun i => cast (congrArg G (blockEq cr.1.color p i)) (cr.2.2 (p.symm i))
  ⟩

-- Relabeling is a civilized operation that can be viewed as a multiplicative action. Indeed,
-- `Equiv.Perm (Fin n)` is a group (permutations under composition).
section RelabelProperties
variable {F G : Type → Type} [Species F] {U : Type} {n : ℕ}

theorem relabel_one (cr : CompRaw F G U n) : relabel cr (Equiv.refl (Fin n)) = cr := by
  obtain ⟨c, fstruct, gstruct_fam⟩ := cr
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine Prod.ext ?_ ?_
  · -- F-structure preserved: trivial, we are just relabeling blocks.
    exact Species.transport_id fstruct
  · -- G-structures: trivial since we are relabeling blocks using the identity function.
    funext i
    simp [relabel]

theorem relabel_mul (p q : Equiv.Perm (Fin n)) (cr : CompRaw F G U n)
: relabel cr (p * q) = relabel (relabel cr q) p := by
  obtain ⟨c, φ, γ⟩ := cr
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine Prod.ext ?_ ?_
  · -- F-part: transport (p*q) φ = transport p (transport q φ)
    exact Species.transport_trans q p φ
  · -- γ-part: casts compose; index (p*q).symm i = q.symm (p.symm i)
    funext i
    simp [relabel, cast_cast]
    rfl

instance instMulActionRelabel : MulAction (Equiv.Perm (Fin n)) (CompRaw F G U n) where
  smul p cr := relabel cr p
  one_smul  := relabel_one
  mul_smul  := relabel_mul

/- TODO: Defining a MulAction just for that: overkill? -/
def permSetoid (F G : Type → Type) [Species F] (U : Type) (n : ℕ) : Setoid (CompRaw F G U n) :=
  MulAction.orbitRel (Equiv.Perm (Fin n)) (CompRaw F G U n)
section RelabelProperties

/- The actual `Comp` structure. -/
def Comp (F G : Type → Type) [Species F] (U : Type) : Type :=
  Σ n : ℕ, Quotient (permSetoid F G U n)

section CompFintype
variable {F G : Type → Type} [Species F] [Species G] {U : Type} [LabelType U] {n : ℕ}

instance : DecidableEq (F (Fin n)) :=
  (Fintype.equivFin (F (Fin n))).injective.decidableEq

-- DecidableEq for fibres, from their Fintype (computable)
instance : DecidableEq (F (Fin n)) := Fintype.decidableEqOfFintype
instance (c : Coloring U n) (i : Fin n) : DecidableEq (G {u // c.color u = i}) :=
  Fintype.decidableEqOfFintype

-- hence DecidableEq on CompRaw (Σ/×/Π of decidable-eq, Coloring via funext over Fintype)
instance : DecidableEq (CompRaw F G U n) := by unfold CompRaw; infer_instance

-- the orbit relation is a decidable ∃ over the finite Perm (Fin n)
instance : DecidableRel (permSetoid F G U n).r := fun cr cr' =>
  decidable_of_iff (∃ p : Equiv.Perm (Fin n), relabel cr p = cr')
    (by rfl)   -- orbitRel unfolds to this ∃

-- Fintype of the quotient, then of Comp
instance : Fintype (Quotient (permSetoid F G U n)) := Quotient.fintype _
noncomputable instance : Fintype (Comp F G U) := Fintype.ofEquiv _ truncEquiv.symm
end CompFintype

/-- A surjection from a finite type bounds the target's cardinality. -/
theorem Coloring.card_le {U : Type} [Fintype U] {n : ℕ} (c : Coloring U n)
: n ≤ Fintype.card U := by
  have := Fintype.card_le_of_surjective c.color c.surj
  simpa using this

/-- No colouring exists with more blocks than labels. -/
theorem Coloring.isEmpty_of_gt {U : Type} [Fintype U] {n : ℕ} (h : Fintype.card U < n)
: IsEmpty (Coloring U n) :=
  ⟨fun c => absurd (c.card_le) (not_le.mpr h)⟩

/-- Hence the raw data is empty there too. -/
theorem CompRaw.isEmpty_of_gt
  {F G : Type → Type} {U : Type} [Fintype U] {n : ℕ} (h : Fintype.card U < n)
: IsEmpty (CompRaw F G U n) :=
  ⟨fun cr => (Coloring.isEmpty_of_gt h).elim cr.1⟩

theorem Comp.card_le
  {F G : Type → Type} [Species F] {U : Type} [LabelType U] {n : ℕ}
  (q : Quotient (permSetoid F G U n))
: n ≤ Fintype.card U :=
  Quotient.inductionOn q (fun cr => cr.1.card_le)

def truncEquiv {F G : Type → Type} [Species F] {U : Type} [LabelType U] :
  Comp F G U ≃ Σ n : Fin (Fintype.card U + 1), Quotient (permSetoid F G U n.val)
where
  toFun  := fun ⟨n, q⟩ => ⟨⟨n, Nat.lt_succ_of_le (Comp.card_le q)⟩, q⟩
  invFun := fun ⟨n, q⟩ => ⟨n.val, q⟩
  left_inv  := fun _ => rfl
  right_inv := fun _ => rfl

/-- `σ` restricted to block `i`. -/
def transportBlock {U V : Type} {n : ℕ} (σ : U ≃ V) (color : U → Fin n) (i : Fin n) :
    {u // color u = i} ≃ {v // (color ∘ σ.symm) v = i} :=
  σ.subtypeEquiv (fun u => by simp [Function.comp, σ.symm_apply_apply])

def CompRaw.transport {F G : Type → Type} [Species G] {U V : Type}
    [LabelType U] [LabelType V] {n : ℕ} (σ : U ≃ V) (cr : CompRaw F G U n) :
    CompRaw F G V n :=
  ⟨ ⟨cr.1.color ∘ σ.symm, by
      intro i; obtain ⟨u, hu⟩ := cr.1.surj i; exact ⟨σ u, by simp [Function.comp, hu]⟩⟩,
    cr.2.1,                                   -- F-part unchanged: blocks are still `Fin n`
    fun i => Species.transport (transportBlock σ cr.1.color i) (cr.2.2 i) ⟩

/- theorem transport_cast -/
/-   {G : Type → Type} [Species G] {α β : Type} [LabelType α] [LabelType β] (h : α = β) (x : G α) -/
/- : cast (congrArg G h) x = Species.transport (Equiv.cast h) x := by -/
/-   subst h -/
/-   simp [Equiv.cast_refl, Equiv.refl] -/
/-   exact (Species.transport_id x).symm -/

theorem transport_cast {G} [Species G] {α β : Type} [LTα : LabelType α] (h : α = β) (x : G α)
: haveI : LabelType β := h ▸ LTα
  cast (congrArg G h) x = Species.transport (Equiv.cast h) x
:= by
  subst h
  exact (Species.transport_id x).symm

section CompSpecies
variable {F G : Type → Type} [Species F] [Species G]

instance instSpeciesComp : Species (Comp F G) where
  fintype := fun {U} _ => by
    -- Fintype (Comp F G U) = Fintype (Σ n, Quotient (permSetoid …))
    -- via truncEquiv to Σ n : Fin (card U + 1), Quotient …, then Fintype.ofEquiv
    -- needs: Fintype (Quotient (permSetoid …)) per n
    --        ← DecidableRel orbit relation ← DecidableEq (CompRaw …) ← DecidableEq F/G structs
    sorry

  transport := fun {U V} _ _ σ x =>
    -- lift CompRaw.transport through the quotient using CompRaw.transport_relabel
    match x with
    | ⟨n, q⟩ =>
      ⟨n, Quotient.map (CompRaw.transport σ)
            (fun a b ⟨p, hp⟩ => ⟨p, by rw [← CompRaw.transport_relabel, hp]⟩) q⟩

  transport_id := by
    rintro U _ ⟨n, q⟩
    -- reduce to CompRaw via Quotient.ind, then CompRaw-level transport_id
    refine Sigma.ext rfl (heq_of_eq ?_)
    induction q using Quotient.ind with
    | _ cr => sorry   -- CompRaw.transport (Equiv.refl U) cr ≈ cr  (Quotient.sound)

  transport_trans := by
    rintro U V W _ _ _ σ τ ⟨n, q⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    induction q using Quotient.ind with
    | _ cr => sorry   -- CompRaw.transport (σ.trans τ) cr ≈ transport τ (transport σ cr)
end CompSpecies

theorem CompRaw.transport_relabel {F G} [Species F] [Species G] {U V} [LabelType U] [LabelType V]
    {n} (σ : U ≃ V) (cr : CompRaw F G U n) (p : Equiv.Perm (Fin n)) :
    CompRaw.transport σ (relabel cr p) = relabel (CompRaw.transport σ cr) p := by
  obtain ⟨c, φ, γ⟩ := cr
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine Prod.ext rfl ?_
  funext i
  -- goal: the two G-structures at block i agree
  simp only [CompRaw.transport, relabel]
  -- LHS: transport (transportBlock σ (p∘c.color) i) (cast … (γ (p.symm i)))
  -- RHS: cast … (transport (transportBlock σ c.color (p.symm i)) (γ (p.symm i)))
  rw [transport_cast]                       -- LHS's cast → transport
  rw [transport_cast]                       -- RHS's cast → transport (if RHS has the cast form)
  simp only [Function.comp_apply]

-- (transport_cast already applied — goal has Equiv.cast inside transport, no raw cast left)
  rw [transport_trans_apply, transport_trans_apply]
  congr 1
  apply Equiv.ext
  rintro ⟨u, hu⟩
  apply Subtype.ext
  rfl


  rw [transport_cast, transport_cast]
  rw [transport_trans_apply, transport_trans_apply]   -- collapse each nested pair
  -- now: transport (E_σ.trans E_τ) x = transport (E_σ'.trans E_τ') x  — single transports
  congr 1
  apply Equiv.ext
  rintro ⟨u, hu⟩
  apply Subtype.ext
  rfl



  apply congrArg (fun e => Species.transport e (γ (p.symm i)))
  apply Equiv.ext
  rintro ⟨u, hu⟩
  rfl

/- def Comp.transport {F G} [Species F] [Species G] {U V} [LabelType U] [LabelType V] -/
/-     (σ : U ≃ V) : Comp F G U → Comp F G V := fun ⟨n, q⟩ => -/
/-   ⟨n, Quotient.map (CompRaw.transport σ) (fun a b ⟨p, hp⟩ => -/
/-         ⟨p, by rw [← CompRaw.transport_relabel, hp]⟩) q⟩ -/


namespace Species

