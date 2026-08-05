/- TODO rm unused imports -/
import Species.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Partition.Basic

/- The type of `B`s belonging to `P.parts` -/
abbrev Blocks {U : Type} (P : Partition (Set.univ (α := U))) : Type :=
  {B // B ∈ P.parts}

def Comp (F G : Type → Type) (U : Type) : Type :=
  Σ P : Partition (Set.univ (α := U)),
  /- F-structure over blocks -/
  F (Blocks P)
  /- A unique G-structure is defined over the contents of each block -/
  × (∀ B : Blocks P, G (↥B.val))

namespace Species

variable {F G : Type → Type} [Species F] [Species G] {U V : Type} {n : ℕ}

def map_partition {U V : Type} (P : Partition (Set.univ (α := U))) (f : U ≃ V)
: Partition (Set.univ (α := V)) where
  parts := (fun y => f '' y) '' P.parts;
  sSupIndep' := by
    intro s hs
    obtain ⟨B, hB, rfl⟩ := hs          -- s = f '' B, B ∈ P.parts
    -- s ∈ (f '' ·) '' P.parts ; show Disjoint s (sSup (parts \ {s}))
    have hind := P.sSupIndep' hB       -- Disjoint B (sSup (P.parts \ {B}))
    simp; intro a a_in_P a_neq_B
    rw [Set.disjoint_image_iff f.injective]
    have haB : Disjoint B a := by
      apply hind.mono_right
      exact le_sSup ⟨a_in_P, a_neq_B⟩      -- a ∈ P.parts \ {B}, so a ≤ sSup (…)
    exact haB;
  bot_notMem' := by
    rintro ⟨B, hB, hfB⟩
    rw [Set.image_eq_empty.mp hfB] at hB    -- hB : (∅ : Set U) ∈ P.parts
    exact P.bot_notMem' hB
  sSup_eq' := by
    rw [
      Set.sSup_eq_sUnion, ← Set.image_sUnion, ← Set.sSup_eq_sUnion, P.sSup_eq', Set.image_univ,
      f.surjective.range_eq
    ]

def partsEquiv {U V} (P : Partition (Set.univ (α := U))) (f : U ≃ V) :
    Blocks P ≃ Blocks (map_partition P f) where
  toFun := fun ⟨B, hB⟩ => ⟨f '' B, Set.mem_image_of_mem _ hB⟩
  invFun := fun ⟨B', hB'⟩ =>
    ⟨f.symm '' B', by obtain ⟨C, hC, rfl⟩ := hB'; rwa [Equiv.symm_image_image]⟩
  left_inv := fun ⟨B, hB⟩ => by simp
  right_inv := fun ⟨B', hB'⟩ => by simp

def blockEquiv {U V} (f : U ≃ V) (B : Set U) : ↥B ≃ ↥(f '' B) :=
  f.subtypeEquiv (fun u => by simp)

instance instSpeciesComp : Species (Comp F G) where
  fintype := fun {U} _ => by
    -- Fintype (Comp F G U) = Fintype (Σ P, F (Blocks P) × ∀ B, G ↥B.val)
    -- Needs: Fintype (Partition univ) [via bridge to Finpartition under [Fintype U]],
    --        LabelType (Blocks P) so F (Blocks P) has Species.fintype,
    --        LabelType ↥B.val for each block.
    sorry
  transport := fun f x =>
    match x with
    | ⟨P, φ, γ⟩ =>
      ⟨ map_partition P f,
        Species.transport (partsEquiv P f) φ,
        fun B' => Species.transport (fiberEquiv P f B') (γ ((partsEquiv P f).symm B')) ⟩
  transport_id := by
    rintro U _ ⟨P, φ, γ⟩
    -- index: map_partition P (refl) = P   (map_partition_refl, via Partition.ext + Set.image_id)
    -- fibre F: partsEquiv P refl ≃ refl (mod index eq) → Species.transport_id φ
    -- fibre G: fiberEquiv P refl B ≃ refl → Species.transport_id (γ B), reindexed
    -- Sigma.ext (map_partition_refl) then HEq over the F × Π G fibre.
    sorry
  transport_trans := by
    rintro U V W _ _ _ f g ⟨P, φ, γ⟩
    -- index: map_partition P (f.trans g) = map_partition (map_partition P f) g
    -- fibres via partsEquiv_trans / fiberEquiv_trans + Species.transport_trans
    sorry

/- transport := fun f ⟨P, φ, γ⟩ => -/
/-   ⟨ map_partition P f, -/
/-     Species.transport (partsEquiv P f) φ, -/
/-     fun B' => -/
/-       Species.transport -/
/-         ((blockEquiv f ((partsEquiv P f).symm B').val).trans -/
/-           (Equiv.setCongr (partsEquiv_symm_image P f B'))) -/
/-         (γ ((partsEquiv P f).symm B')) ⟩ -/

/- /1- Relabelling a split: `v` falls in the same block as its `σ`-preimage. -1/ -/
/- abbrev transportSplit {U V : Type} (σ : U ≃ V) (Comp F G U) : Comp := -/
/-   split ∘ σ.symm -/

/- /1- /2- There is a bijection between blocks before and after transport. -2/ -1/ -/
/- /1- def blockEquiv {U V} (σ : U ≃ V) (split : U → Fin n) (x : Fin n) -1/ -/
/- /1- : {u // split u = x} ≃ {v // transportSplit σ split v = x} := -1/ -/
/- /1-   σ.subtypeEquiv (fun u => by simp [Equiv.symm_apply_apply]) -1/ -/

/- /1- Species instance -1/ -/
/- instance instSpeciesPart : Species (Part n F) where -/
/-   fintype := fun {U} _ => by unfold Part; infer_instance -/
/-   transport := fun σ ⟨split, f⟩ => ⟨ -/
/-     transportSplit σ split, -/
/-     fun i => Species.transport (blockEquiv σ split i) (f i) -/
/-   ⟩ -/
/-   transport_id := by -/
/-     rintro U _ ⟨split, f⟩ -/
/-     refine Sigma.ext rfl (heq_of_eq ?_) -/
/-     funext i                                  -- fibre is a Π, so funext, not Prod.ext -/
/-     have foo : blockEquiv (Equiv.refl U) split i = Equiv.refl _ := by -/
/-       apply Equiv.ext; rintro ⟨u, hu⟩; apply Subtype.ext; rfl -/
/-     simp [foo]; exact Species.transport_id (f i) -/
/-   transport_trans := by -/
/-     rintro U V W _ _ _ σ τ ⟨split, f⟩ -/
/-     refine Sigma.ext rfl (heq_of_eq ?_) -/
/-     funext i -/
/-     have foo : blockEquiv (σ.trans τ) split i -/
/-          = (blockEquiv σ split i).trans (blockEquiv τ (transportSplit σ split) i) := by -/
/-       apply Equiv.ext; rintro ⟨u, hu⟩; apply Subtype.ext; rfl -/
/-     simp [foo] -/
/-     exact Species.transport_trans (blockEquiv σ split i) (blockEquiv τ (transportSplit σ split) i) (f i) -/
