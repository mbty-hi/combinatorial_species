import Species.Basic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Finset.Functor

namespace Species

open CategoryTheory

/- `FinBij` which corresponds to Joyal's `B` category.
   Objects are `Finite`, morphisms are bijections. -/
structure FinBij where
  α : Type
  [inst : Finite α] -- deduced field

attribute [instance] FinBij.inst -- Expose `Finite α`

instance : Category FinBij where
  Hom X Y     := X.α ≃ Y.α
  id  X       := Equiv.refl X.α
  comp f g    := f.trans g
  id_comp _   := rfl
  comp_id _   := rfl
  assoc _ _ _ := rfl

instance : Groupoid FinBij where
  inv        := Equiv.symm
  inv_comp f := Equiv.ext (fun x => f.apply_symm_apply x)
  comp_inv f := Equiv.ext (fun x => f.symm_apply_apply x)

/-- A species, viewed as a functor on category `B`. -/
def toFunctor (F : Type → Type) [Species F] : FinBij ⥤ Type where
  obj X        := F X.α
  map f        := ↾(Species.transport (F := F) f)
  map_id X     := by ext s; exact Species.id_transport s
  map_comp f g := by ext s; exact Species.comp_transport f g s

variable (G : FinBij ⥤ Type) [∀ X, Finite (G.obj X)]

def ofFunctor (G : FinBij ⥤ Type) (U : Type) : Type :=
  ∀ _ : Finite U, G.obj ⟨U⟩

instance : Species (ofFunctor G) where
  finite               := by unfold ofFunctor; infer_instance
  transport σ s        := fun _ => G.map (X := ⟨_⟩) (Y := ⟨_⟩) σ (s inferInstance)
  id_transport s       := funext fun _ => G.map_id_apply _ _
  comp_transport σ τ s :=
    funext (fun _ => by exact G.map_comp_apply (X := ⟨_⟩) (Y := ⟨_⟩) (Z := ⟨_⟩) σ τ _)

def toFunctor_ofFunctor_iso : toFunctor (ofFunctor G) ≅ G :=
  NatIso.ofComponents
    (fun X =>
      Equiv.toIso {
        toFun     := fun s   => s X.inst
        invFun    := fun x _ => x
        left_inv  := fun _   => funext fun _ => rfl
        right_inv := fun _   => rfl
      }
    )
    (fun f => by ext s; rfl)

def ofFunctor_toFunctor_equiv (F : Type → Type) [Species F] (U : Type) [Finite U]
: ofFunctor (Species.toFunctor F) U ≃ F U where
  toFun s := s inferInstance
  invFun x := fun _ => x
  left_inv _ := funext fun _ => rfl
  right_inv _ := rfl

instance (F : Type → Type) [Species F] (X : FinBij) : Finite ((Species.toFunctor F).obj X) :=
  inferInstanceAs (Finite (F X.α))

lemma ofFunctor_toFunctor_equiv_natural
  (F : Type → Type) [Species F] {U V : Type}
  [Finite U] [Finite V] (σ : U ≃ V) (s : ofFunctor (toFunctor F) U)
: ofFunctor_toFunctor_equiv F V (Species.transport σ s)
  = Species.transport σ (ofFunctor_toFunctor_equiv F U s)
:= by
  rfl

structure Hom (F G : Type → Type) [Species F] [Species G] where
  app : ∀ (U : Type) [Finite U], F U → G U
  naturality :
    ∀ {U V : Type} [Finite U] [Finite V] (σ : U ≃ V) (s : F U),
    app V (Species.transport σ s) = Species.transport σ (app U s)

end Species
