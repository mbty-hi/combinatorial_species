import Species.Basic
import Species.Isomorphism
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Finite.Prod

/-!
# A categorical view of species

This file provides a bridge between the combinatorial vision of species used in [BLL] and the
categorical point of view of [Joyal81].

## Important definitions
* `FinBij`        : Joyal's B category ([Joyal81])
* `PreSpeciesCat` : the category of all functors from `B` to `Type`
* `IsSpecies`     : a functor in `PreSpeciesCat` is a species when all of its values are finite
* `SpeciesCat`    : the category of species
* `toSpeciesCat`  : convert species from the [BLL]-style presentation to the categorical view
* `ofSpeciesCat`  : convert species from the categorical view to the [BLL]-style presentation
* `Hom`           : the hom-set of the category of species

## Main statements
* `toSpeciesCat_ofSpeciesCat_iso` : converting an object of `SpeciesCat` to a species and back
  yields an isomorphic object
* `ofSpeciesCat_toSpeciesCat_iso` : converting a species to an object of `SpeciesCat` and back
  yields an isomorphic species
* `Hom.equivSpeciesCat` : species morphisms are morphisms in `SpeciesCat`
* `Iso.equivSpeciesCat` : species isomorphisms are isomorphisms in `SpeciesCat`
* `Iso.equivSpeciesCat_hom` : the two correspondences agree

## References
* [F. Bergeron, G. Labelle, P. Leroux, *Combinatorial Species and Tree-like Structures*][BLL]
* [A. Joyal, *Une théorie combinatoire des séries formelles*][Joyal81]
-/

namespace Species

open CategoryTheory

/-- Joyal's `B` category: objects are `Finite` (label) types, morphisms are bijections between them
([Joyal81] uses finite sets, but the two representations are equivalent). `FinBij` is just a
structure bundling types with their proofs of finiteness, bijections only appear in
`instCategory`. -/
structure FinBij where
  /-- The underlying label type. -/
  Labels : Type
  /-- Finiteness of the labels, implicitly inferred when constructing a `FinBij`. -/
  [inst : Finite Labels]
attribute [instance] FinBij.inst -- Expose `Finite Labels`

namespace FinBij

instance instCategory : Category FinBij where
  Hom X Y     := X.Labels ≃ Y.Labels
  id  X       := Equiv.refl X.Labels
  comp f g    := f.trans g
  id_comp _   := rfl
  comp_id _   := rfl
  assoc _ _ _ := rfl

instance instGroupoid : Groupoid FinBij where
  inv        := Equiv.symm
  inv_comp f := Equiv.ext (fun x => f.apply_symm_apply x)
  comp_inv f := Equiv.ext (fun x => f.symm_apply_apply x)

end FinBij

/-- The category of functors from `B` to `Type`. It is more general than the category of species, as
it includes functors that send some label types to infinite types (see `SpeciesCat` below). -/
abbrev PreSpeciesCat := FinBij ⥤ Type

/-- A functor on `B` is a species when all its values are finite. In other words, a species is a
rule that takes any finite label type to a finite type (type family `P.obj` specialized with
`Labels`), compatibly with relabelling (as `P.map` respects functorial laws). -/
def IsSpecies : ObjectProperty PreSpeciesCat :=
  fun (P : PreSpeciesCat) => ∀ (Labels : FinBij), Finite (P.obj Labels)

/-- Joyal's category of species: the full subcategory of functors `B ⥤ Type` that are species, with
morphisms as natural transformations. -/
abbrev SpeciesCat := IsSpecies.FullSubcategory

namespace SpeciesCat

instance instFiniteObjObj (S : SpeciesCat) (X : FinBij) : Finite (S.obj.obj X) := S.property X

end SpeciesCat

/-- A function that takes a `Species` to a `PreSpeciesCat` (i.e., a functor which does not
statically guarantee finiteness; see `toSpeciesCat` for getting a proper `SpeciesCat`). -/
def toPreSpeciesCat (F : Type → Type) [Species F] : PreSpeciesCat where
  obj X        := F X.Labels
  map f        := ↾(transport f)
  map_id X     := by ext s; exact id_transport s
  map_comp f g := by ext s; exact comp_transport f g s

namespace toPreSpeciesCat

instance instFiniteObj (F : Type → Type) [Species F] (X : FinBij)
: Finite ((toPreSpeciesCat F).obj X) :=
  inferInstanceAs (Finite (F X.Labels))

end toPreSpeciesCat

/-- A species as an object of `SpeciesCat`. -/
def toSpeciesCat (F : Type → Type) [Species F] : SpeciesCat :=
  ⟨toPreSpeciesCat F, fun _ => inferInstance⟩

/-- The type family underlying functor `P` of type `PreSpeciesCat`. `P.obj` expects a `FinBij`,
hence the `Finite Labels` requirement. Note that the addition of the finiteness constraint might
change the behavior of the type family on infinite types: if `P = toPreSpeciesCat F`, the result is
not equal to `F` (though it is isomorphic to it). This is irrelevant for species, as they are only
concerned with finite label types. -/
def ofPreSpeciesCat (P : PreSpeciesCat) : Type → Type :=
  fun (Labels : Type) => ∀ (_ : Finite Labels), P.obj ⟨Labels⟩

namespace ofPreSpeciesCat

variable (P : PreSpeciesCat) [∀ Labels, Finite (P.obj Labels)]

instance instSpecies : Species (ofPreSpeciesCat P) where
  finite               := by unfold ofPreSpeciesCat; infer_instance
  transport σ s _      := P.map (X := ⟨_⟩) (Y := ⟨_⟩) σ (s inferInstance)
  id_transport s       := funext (fun _ => P.map_id_apply _ _)
  comp_transport σ τ s :=
    funext (fun _ => P.map_comp_apply (X := ⟨_⟩) (Y := ⟨_⟩) (Z := ⟨_⟩) σ τ _)

end ofPreSpeciesCat

/-- The type family underlying an object of `SpeciesCat`. -/
abbrev ofSpeciesCat (S : SpeciesCat) : Type → Type :=
  ofPreSpeciesCat S.obj

namespace ofSpeciesCat

instance instSpecies (S : SpeciesCat) : Species (ofSpeciesCat S) :=
  ofPreSpeciesCat.instSpecies S.obj

end ofSpeciesCat

section RoundTrips

variable (P : PreSpeciesCat) [∀ Labels, Finite (P.obj Labels)] (S : SpeciesCat)
variable (F : Type → Type) [Species F]

/-- `toPreSpeciesCat` undoes `ofPreSpeciesCat` (up to isomorphism). -/
def toPreSpeciesCat_ofPreSpeciesCat_iso : toPreSpeciesCat (ofPreSpeciesCat P) ≅ P :=
  NatIso.ofComponents
    (fun X =>
      Equiv.toIso {
        toFun   s   := s X.inst
        invFun  x _ := x
        left_inv  _ := funext (fun _ => rfl)
        right_inv _ := rfl
      }
    )
    (fun f => by ext s; rfl)

/-- `ofPreSpeciesCat` undoes `toPreSpeciesCat` (up to isomorphism). -/
def ofPreSpeciesCat_toPreSpeciesCat_iso : Iso (ofPreSpeciesCat (toPreSpeciesCat F)) F where
  equiv _ _ := {
    toFun   s   := s inferInstance,
    invFun  x _ := x,
    left_inv  _ := funext (fun _ => rfl),
    right_inv _ := rfl
  }
  naturality _ _ := rfl

/-- `toSpeciesCat` undoes `ofSpeciesCat` (up to isomorphism). -/
def toSpeciesCat_ofSpeciesCat_iso : toSpeciesCat (ofSpeciesCat S) ≅ S :=
  IsSpecies.isoMk (toPreSpeciesCat_ofPreSpeciesCat_iso S.obj)

/-- `ofSpeciesCat` undoes `toSpeciesCat` (up to isomorphism). -/
def ofSpeciesCat_toSpeciesCat_iso : Iso (ofSpeciesCat (toSpeciesCat F)) F :=
  ofPreSpeciesCat_toPreSpeciesCat_iso F

end RoundTrips

/-- Hom-set in the category of species (its elements correspond to natural transformations between
species). An element of `Hom F G` is therefore a morphism of species, i.e., for every label type
`U`, a map from `F`-structures on `U` to `G`-structures on `U`, compatible with relabelling. -/
@[ext] structure Hom (F G : Type → Type) [Species F] [Species G] where
  /-- The map on each label type. -/
  app : ∀ (U : Type) [Finite U], F U → G U
  /-- Mapping then relabelling is the same as relabelling then mapping. -/
  naturality :
    ∀ {U V : Type} [Finite U] [Finite V] (σ : U ≃ V) (s : F U),
    app V (transport σ s) = transport σ (app U s)

namespace Hom

variable {F G H K : Type → Type} [Species F] [Species G] [Species H] [Species K]

/-- The identity morphism of species. -/
def id (F : Type → Type) [Species F] : Hom F F where
  app _ _ s      := s
  naturality _ _ := rfl

/-- Composition of morphisms of species (diagrammatic order). -/
def comp (α : Hom F G) (β : Hom G H) : Hom F H where
  app      U _ s := β.app U (α.app U s)
  naturality σ s := by rw [α.naturality, β.naturality]

@[simp] lemma id_comp (α : Hom F G) : (Hom.id F).comp α = α := rfl
@[simp] lemma comp_id (α : Hom F G) : α.comp (Hom.id G) = α := rfl

lemma comp_assoc (α : Hom F G) (β : Hom G H) (γ : Hom H K)
: (α.comp β).comp γ = α.comp (β.comp γ) := rfl

end Hom

section Morphisms

variable {F G : Type → Type} [Species F] [Species G]

/-- The morphism underlying an isomorphism. -/
def Iso.toHom (iso : Iso F G) : Hom F G := ⟨fun U _ => iso.equiv U, iso.naturality⟩

/-- Species morphisms are natural transformations between the underlying functors on `B`. -/
def Hom.equivNatTrans : Hom F G ≃ (toPreSpeciesCat F ⟶ toPreSpeciesCat G) where
  toFun α := {
    app X := ↾(α.app X.Labels)
    naturality _ _ σ := by ext s; exact α.naturality σ s
  }
  invFun η := {
    app      U _ s := η.app ⟨U⟩ s
    naturality σ s := NatTrans.naturality_apply η (X := ⟨_⟩) (Y := ⟨_⟩) σ s
  }
  left_inv  _ := rfl
  right_inv _ := by ext X s; rfl

/-- Species morphisms are morphisms in `SpeciesCat`. -/
def Hom.equivSpeciesCat : Hom F G ≃ (toSpeciesCat F ⟶ toSpeciesCat G) :=
  Hom.equivNatTrans.trans
    ((ObjectProperty.fullyFaithfulι IsSpecies).homEquiv
      (X := toSpeciesCat F)
      (Y := toSpeciesCat G)
    ).symm

/-- Species isomorphisms are natural isomorphisms between the underlying functors on `B`. -/
def Iso.equivNatIso : Iso F G ≃ (toPreSpeciesCat F ≅ toPreSpeciesCat G) where
  toFun iso :=
    NatIso.ofComponents
      (fun X => (iso.equiv X.Labels).toIso) (fun σ => by ext s; exact iso.naturality σ s)
  invFun i := {
    equiv      U _ := (i.app ⟨U⟩).toEquiv
    naturality σ s := NatTrans.naturality_apply i.hom (X := ⟨_⟩) (Y := ⟨_⟩) σ s
  }
  left_inv  _ := rfl
  right_inv _ := by ext X s; rfl

/-- Species isomorphisms are isomorphisms in `SpeciesCat`. -/
def Iso.equivSpeciesCat : Iso F G ≃ (toSpeciesCat F ≅ toSpeciesCat G) :=
  Iso.equivNatIso.trans
    ((ObjectProperty.fullyFaithfulι IsSpecies).isoEquiv
      (X := toSpeciesCat F) (Y := toSpeciesCat G)).symm

/-- The two correspondences agree. -/
@[simp] lemma Iso.equivSpeciesCat_hom (iso : Iso F G)
: (Iso.equivSpeciesCat iso).hom = Hom.equivSpeciesCat iso.toHom := by
  ext X s; rfl

end Morphisms

end Species
