import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
import Mathlib.CategoryTheory.Category.KleisliCat

import Mathlib.Data.Part

universe u v w
variable {α β γ : Type u}

open CategoryTheory

class KSet (α : Type*) where
  Defined : α → Prop
  extensional : ∀ {a b}, (Defined a ↔ Defined b) → (Defined a → Defined b → a = b) → a = b

notation a:10 " ↓" => KSet.Defined a
notation a:10 " ↑" => ¬ KSet.Defined a


namespace KSet

/-- Undefined elements are unique in a K-Set. -/
def undefined_unique
  [KSet α]
  (x y : α)
  (h : x ↑) (h' : y ↑)
  : x = y := by
  apply extensional
  · constructor <;> intros <;> contradiction
  · intros; contradiction

end KSet


structure KSetHom (α : Type*) (β : Type*) [KSet α] [KSet β] where
  toFun : α → β
  strict : ∀ {a : α}, toFun a ↓ → a ↓

namespace KSetHom

instance instFunLike [KSet α] [KSet β] : FunLike (KSetHom α β) α β where
  coe f := f.toFun
  coe_injective' f g p := by
    cases f
    cases g
    congr

protected def id [KSet α] : KSetHom α α where
  toFun x := x
  strict dx := dx

protected def comp [KSet α] [KSet β] [KSet γ] (f : KSetHom β γ) (g : KSetHom α β) : KSetHom α γ where
  toFun x := f (g x)
  strict dz := g.strict (f.strict dz)

@[ext] theorem ext
  [KSet α] [KSet β]
  {f g : KSetHom α β}
  (h : ∀ x, f x = g x)
  : f = g := DFunLike.ext _ _ h

end KSetHom

def KSetCat : Type (u + 1) := Bundled KSet

namespace KSetCat

instance bundledHom : BundledHom KSetHom where
  toFun KA KB f := f.toFun
  id _ := KSetHom.id
  comp _ _ _ := KSetHom.comp
  hom_ext KA KB f g p := by
    cases f
    cases g
    congr

deriving instance LargeCategory for KSetCat

instance : CoeSort KSetCat (Type*) where
  coe X := X.α

instance (X : KSetCat) : KSet X := X.str

instance {X Y : KSetCat} : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe (f : KSetHom X Y) := f

instance instFunLike (X Y : KSetCat) : FunLike (X ⟶ Y) X Y :=
  show FunLike (KSetHom X Y) X Y from inferInstance

instance concreteCategory : ConcreteCategory KSetCat :=
  BundledHom.concreteCategory _

@[simp] lemma coe_id {X : KSetCat} : (𝟙 X : X → X) = id := rfl

@[simp] lemma coe_comp {X Y Z : KSetCat} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X ⟶ Z) = g ∘ f := rfl

@[simp] lemma comp_defined {X Y Z : KSetCat} {f : X ⟶ Y} {g : Y ⟶ Z} {x : X} : (g.comp f) x ↓ ↔ g (f x) ↓ := by rfl

def of (X : Type u) [KSet X] : KSetCat := Bundled.of X

def ofHom {X Y : Type u} [KSet X] [KSet Y] (f : KSetHom X Y) : of X ⟶ of Y :=
  f

/-!
# Discrete K-Sets
-/

def Disc (X : Type*) := X

instance {X : Type u} : KSet (Disc X) where
  Defined _ := True
  extensional p _ := And.right (p True.intro)

def discrete : Type u ⥤ KSetCat.{u} where
  obj X := of (Disc X)
  map f := ofHom ⟨ f , fun _ => True.intro ⟩

def DiscreteAdjunction : discrete ⊣ (forget KSetCat) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => {
      toFun := fun f => f.toFun
      invFun := fun f => ofHom ⟨ f , fun _ => True.intro ⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
  }



/-!
# Partial Elements
-/

structure Value (X : Type u) [KSet X] where
  val : X
  defined : val ↓

instance {X : Type u} [KSet X] : Coe (Value X) X where
  coe := Value.val

@[ext] theorem Value.ext
  {X : Type u}
  [KSet X]
  {v v' : Value X}
  (h : v.val = v'.val)
  : v = v' := by
  cases v
  cases v'
  congr

def Value.extend {X Y : Type u} [KSet Y] (f : X → Y) (x : X) : Part (Value Y) :=
  ⟨ f x ↓ , fun fxd => ⟨ f x , fxd ⟩ ⟩

@[simp] def Value.extend_id
    {X : Type u} [KSet X]
    (x : Value X)
    : Value.extend (𝟙 X) x = x := by sorry

def Values : KSetCat.{u} ⥤ KleisliCat Part where
  obj X := Value X
  map f x := Value.extend f x
  map_id X := funext fun x => by
    ext
    simp
    -- constructor
    -- · simp
    --   intro xd p
    --   rw [←p]
    -- · simp
    --   intro p
    --   exact ⟨ x.defined , by rw [←p] ⟩
  map_comp f g := funext fun x => by
    sorry
    -- ext
    -- simp [CategoryStruct.comp, (· >=> ·)] at *
    -- exact ⟨ fun x => ⟨ g.strict x.1, x ⟩, fun ⟨ _ , gfxd , p ⟩ => ⟨ gfxd, p ⟩ ⟩

-- -- theorem hell
-- --   :

instance : Functor.Faithful Values where
  map_injective := by
    intros X Y f g p
    ext x
    apply Y.str.extensional
    · sorry
    · intro fd gd
      have xd := f.strict fd
      have eq := congr_fun p ⟨ x , xd ⟩
      -- simp [Values] at eq
      -- have def_eq : f x ↓ = g x ↓ := propext eq.1
      -- have cool : HEq (α := f x ↓ → Y) (fun fxd ↦ f x) (β := g x ↓ → Y) (fun fxd ↦ g x) := by
      --   sorry
      -- have dank := congr_heq cool (heq_prop fd gd)
      -- exact dank
      -- apply congr_heq
      -- · exact cool
      -- · sorry
      -- apply eq_of_heq
      -- simp_rw [def_eq]
      -- have cool := eq_of_heq eq.2
      -- -- rw [def_eq] at eq
      -- -- apply eq_of_heq
      -- sorry
      -- apply Function.hfunext
      -- exact eq.2 ▸ sorry
      -- have cool := eq_of_heq eq.2
      -- subst eq.2

    -- · intro fxd
    --   have xd := f.strict fxd
    --   have eq := congr_fun p ⟨ x , xd ⟩
    --   simp [Values] at *
    --   refine ⟨ eq.1.1 fxd, ?_ ⟩
    --   have nice := congr_fun eq.2
    --   sorry
    -- · sorry
