import Species.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Sum.Order
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma

namespace Species

variable {F G : Type → Type} [Species F] [Species G]
variable {U V : Type} [LabelType U] [LabelType V]

def IsSplit {U} (p : Finset U × Finset U) : Prop :=
  (∀ u, u ∈ p.1 → u ∉ p.2) ∧ (∀ u, u ∈ p.1 ∨ u ∈ p.2)

def mul (F G : Type → Type) (U : Type) : Type :=
  Σ p : {p : Finset U × Finset U // IsSplit p}, F {x // x ∈ p.val.1} × G {x // x ∈ p.val.2}

-- σ restricted to a block:  ↥A ≃ ↥(A.map σ.toEmbedding)
def blockEquiv {U V} (σ : U ≃ V) (A : Finset U) : {x // x ∈ A} ≃ {x // x ∈ A.map σ.toEmbedding} :=
  σ.subtypeEquiv (fun a => by simp)

-- the split predicate transports
theorem IsSplit.map {U V} (σ : U ≃ V) {p : Finset U × Finset U} (h : IsSplit p) :
    IsSplit (p.1.map σ.toEmbedding, p.2.map σ.toEmbedding) := by
  obtain ⟨hd, hc⟩ := h
  refine ⟨?_, ?_⟩
  · intro v hv1 hv2
    rw [Finset.mem_map] at hv1 hv2
    obtain ⟨a, ha, rfl⟩ := hv1
    obtain ⟨b, hb, hb⟩ := hv2
    rw [Equiv.coe_toEmbedding] at hb
    rw [σ.injective.eq_iff] at hb; subst hb; apply hd b ha hb
  · intro v
    obtain ⟨a, rfl⟩ := σ.surjective v
    rcases hc a with h | h
    · exact Or.inl (Finset.mem_map_of_mem _ h)
    · exact Or.inr (Finset.mem_map_of_mem _ h)

def mul.transport {U V} [LabelType U] [LabelType V] (σ : U ≃ V) :
    mul F G U → mul F G V := fun ⟨⟨p, hp⟩, f, g⟩ =>
  ⟨⟨(p.1.map σ.toEmbedding, p.2.map σ.toEmbedding), hp.map σ⟩,
   Species.transport (blockEquiv σ p.1) f,
   Species.transport (blockEquiv σ p.2) g⟩

instance {U} [LabelType U] : DecidablePred (IsSplit (U := U)) := fun p => by
  unfold IsSplit; infer_instance

-- index collapses
/- theorem map_refl_emb {U} (A : Finset U) : A.map (Equiv.refl U).toEmbedding = A := by -/
/-   simp [Equiv.refl_toEmbedding]   -- or Finset.map_refl after rewriting the embedding to Embedding.refl -/

/- -- blockEquiv at refl is the identity (as an Equiv, modulo the index eq) -/
/- theorem blockEquiv_refl {U} (A : Finset U) : -/
/-     HEq (blockEquiv (Equiv.refl U) A) (Equiv.refl {x // x ∈ A}) := by -/
/-   -- both sides are Equivs between ↥(A.map refl) and ↥A, equal once map_refl_emb closes the index -/
/-   sorry -/

theorem map_refl_emb {U} (A : Finset U) :
    A.map (Equiv.refl U).toEmbedding = A := by
  ext a; simp [Finset.mem_map, Equiv.coe_toEmbedding]

theorem blockEquiv_refl {U} (A : Finset U) :
    HEq (blockEquiv (Equiv.refl U) A) (Equiv.refl {x // x ∈ A}) := by
  have h : A.map (Equiv.refl U).toEmbedding = A := map_refl_emb A
  -- express blockEquiv at refl as `refl` transported along the index equality
  have key : blockEquiv (Equiv.refl U) A = h.symm ▸ Equiv.refl {x // x ∈ A} := by
    apply Equiv.ext
    rintro ⟨a, ha⟩
    apply Subtype.ext
    -- both sides have underlying value `a`: LHS via subtypeEquiv+refl, RHS since ▸ moves only the proof
    rcases h.symm with rfl          -- legal *inside* key: goal here is the same-typed Eq, not the HEq
    simp [blockEquiv, Equiv.subtypeEquiv_apply, Equiv.coe_toEmbedding]
  rw [key]
  exact eqRec_heq h.symm (Equiv.refl {x // x ∈ A})

instance instSpeciesMul : Species (mul F G) where
  fintype := fun {U} _ => by unfold mul; infer_instance
  transport := fun σ x => mul.transport σ x
  transport_id := by
    rintro U _ ⟨⟨p, hp⟩, f, g⟩
    -- turn the index p.i.map refl back into p.i everywhere
    simp only [mul.transport]
    -- now both fibers are Species.transport (blockEquiv refl p.i) _ with blockEquiv refl ≃ refl
    congr 1
    · -- subtype/index component: the IsSplit-subtype equality, closed by map_refl_emb + Subtype.ext
      apply Subtype.ext; simp
    · -- fibers: reduce blockEquiv refl to refl, then transport_id
      sorry
  transport_trans := by
    rintro U V W _ _ _ σ τ ⟨⟨p, hp⟩, f, g⟩
    -- index equality: p.i.map (σ.trans τ).emb = (p.i.map σ.emb).map τ.emb  (Finset.map_map)
    -- fiber: blockEquiv (σ.trans τ) A ≟ (blockEquiv σ A).trans (blockEquiv τ _), then Species.transport_trans
    sorry

end Species
