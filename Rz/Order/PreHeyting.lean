import Mathlib.Init.Order.Defs
import Mathlib.Order.Notation

import Mathlib.Data.FunLike.Basic

universe u v w

variable {α β γ : Type*}

/-!
# Pre-Heyting algebras

Mathlib builds the entire order heirarchy atop posets, so we need to define preheyting algebras ourselves.
Unfortunately, this means that we need to re-build a lot of the `simp` machinery as well.

Moreover, `Mathlib.Order` is a *TERRIBLE* citizen, and pollutes the namespace with lemmas like `bot_le`
that require us to use a poset. Because Lean will transitively import modules and has no way of
hiding/qualifiying imports (?!?!), this means that `import Mathlib.CategoryTheory` will bring in
all of the globally scoped lemmas. Additionally, lean will not shadow top-level defs, and throws
and error instead.

If we put all of these mistakes together, it means that we cannot use reasonable names for pre-Heyting
algebra lemmas. Therefore, we place all names in a `Pre` namespace; this is very annoying, but as far
as I can tell there is no better solution.

HACK:
A more well-engineered solution would build pre-Heyting algebras as a tower of classes, but we do not
need this level of generality at the moment.
-/

/-- Heyting algebras generallized to preorders. -/
class PreHeyting (α : Type u) extends Bot α, Top α, Sup α, Inf α, HImp α, Preorder α where
  /-- `⊥` is the greatest element -/
  protected bot_le : ∀ a : α, ⊥ ≤ a
  /-- `⊤` is the greatest element -/
  protected le_top : ∀ a : α, a ≤ ⊤
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : ∀ a b : α, a ≤ a ⊔ b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : ∀ a b : α, b ≤ a ⊔ b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c
  /-- The infimum is a lower bound on the first argument -/
  protected inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  /-- The infimum is a lower bound on the second argument -/
  protected inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  /-- The infimum is the *greatest* lower bound -/
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c
  /-- `a ⇨` is right adjoint to `a ⊓` -/
  protected le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a ⊓ b ≤ c

namespace Pre

variable [PreHeyting α] {a b c d : α}

@[simp]
lemma bot_le : ⊥ ≤ a :=
  PreHeyting.bot_le _

@[simp]
lemma le_top : ⊥ ≤ a :=
  PreHeyting.bot_le _

@[simp]
lemma le_sup_left : a ≤ a ⊔ b :=
  PreHeyting.le_sup_left _ _

@[simp]
lemma le_sup_right : b ≤ a ⊔ b :=
  PreHeyting.le_sup_right _ _

lemma sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
  PreHeyting.sup_le _ _ _

@[simp]
lemma sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨ fun h => ⟨ le_trans le_sup_left h, le_trans le_sup_right h ⟩
  , fun ⟨ h1 , h2 ⟩ => sup_le h1 h2
  ⟩

@[simp]
lemma inf_le_left : a ⊓ b ≤ a :=
  PreHeyting.inf_le_left _ _

@[simp]
lemma inf_le_right : a ⊓ b ≤ b :=
  PreHeyting.inf_le_right _ _

lemma le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
  PreHeyting.le_inf _ _ _

@[simp]
lemma le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
  ⟨ fun h => ⟨ le_trans h inf_le_left, le_trans h inf_le_right ⟩
  , fun ⟨ h1 , h2 ⟩ => le_inf h1 h2
  ⟩

@[simp]
lemma le_himp_iff : a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  PreHeyting.le_himp_iff _ _ _

@[simp]
lemma himp_inf_le : (a ⇨ b) ⊓ a ≤ b :=
  le_himp_iff.1 le_rfl

end Pre


/-!
# Morphisms of pre-Heyting algebras.
-/

/-- Pre-heyting morphisms, organized as a typeclass. -/
class PreHeytingHomClass (F α β : Type*) [PreHeyting α] [PreHeyting β] [FunLike F α β] where
  monotone : ∀ (f : F) ⦃ a b : α ⦄, a ≤ b → f a ≤ f b
  map_le_bot : ∀ (f : F), f ⊥ ≤ ⊥
  top_le_map : ∀ (f : F), ⊤ ≤ f ⊤
  map_le_sup : ∀ (f : F) (a b : α), f (a ⊔ b) ≤ f a ⊔ f b
  inf_le_map : ∀ (f : F) (a b : α), f a ⊓ f b ≤ f (a ⊓ b)
  himp_le_map : ∀ (f : F) (a b : α), f a ⇨ f b ≤ f (a ⇨ b)


section Hom

variable {F : Type*} [FunLike F α β]

export PreHeytingHomClass (monotone map_le_bot top_le_map map_le_sup inf_le_map himp_le_map)

attribute [simp] map_le_bot top_le_map map_le_sup inf_le_map himp_le_map

variable [PreHeyting α] [PreHeyting β] [PreHeytingHomClass F α β]
variable (f : F)

@[simp]
lemma sup_le_map
    (a b : α)
    : f a ⊔ f b ≤ f (a ⊔ b) := by
  apply Pre.sup_le <;> apply monotone <;> simp

@[simp]
lemma map_le_inf
    (a b : α)
    : f (a ⊓ b) ≤ f a ⊓ f b := by
    apply Pre.le_inf <;> apply monotone <;> simp

@[simp]
lemma map_le_himp
    (a b : α)
    : f (a ⇨ b) ≤ f a ⇨ f b := by
  simp
  trans
  · apply inf_le_map
  · apply monotone
    rw [←Pre.le_himp_iff]

end Hom


/-- Morphisms of pre-Heyting algebras -/
structure PreHeytingHom (α β : Type*) [PreHeyting α] [PreHeyting β] where
  toFun : α → β
  monotone' : ∀ ⦃a b : α⦄, a ≤ b → toFun a ≤ toFun b
  map_le_bot' : toFun ⊥ ≤ ⊥
  top_le_map' : ⊤ ≤ toFun ⊤
  map_le_sup' : ∀ a b : α, toFun (a ⊔ b) ≤ toFun a ⊔ toFun b
  inf_le_map' : ∀ a b : α, toFun a ⊓ toFun b ≤ toFun (a ⊓ b)
  himp_le_map' : ∀ a b : α, toFun a ⇨ toFun b ≤ toFun (a ⇨ b)

namespace PreHeytingHom

open Function

variable [PreHeyting α] [PreHeyting β] [PreHeyting γ]

instance instFunLike : FunLike (PreHeytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨ _, _ , _, _, _, _, _ ⟩ := f
    obtain ⟨ _, _ , _, _, _, _, _ ⟩ := g
    congr

instance : PreHeytingHomClass (PreHeytingHom α β) α β where
  monotone f := f.monotone'
  map_le_bot f := f.map_le_bot'
  top_le_map f := f.top_le_map'
  map_le_sup f := f.map_le_sup'
  inf_le_map f := f.inf_le_map'
  himp_le_map f := f.himp_le_map'

@[ext]
theorem ext {f g : PreHeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

lemma toFun_eq_coe (f : PreHeytingHom α β) : f.toFun = f := rfl

variable (α)

protected def id : PreHeytingHom α α where
  toFun := id
  monotone' _ _ h := h
  map_le_bot' := by trivial
  top_le_map' := by trivial
  map_le_sup' := by simp
  inf_le_map' := by simp
  himp_le_map' := by simp

@[simp]
lemma coe_id : ⇑(PreHeytingHom.id α) = id := rfl

@[simp]
lemma id_apply (a : α) : PreHeytingHom.id α a = a := rfl

variable {α}

def comp (f : PreHeytingHom β γ) (g : PreHeytingHom α β) : PreHeytingHom α γ where
  toFun := f ∘ g
  monotone' _ _ h := by
    repeat (apply monotone)
    assumption
  map_le_bot' := calc
    f (g ⊥) ≤ f ⊥ := monotone f (map_le_bot g)
    f ⊥ ≤ ⊥       := map_le_bot f
  top_le_map' := calc
    ⊤ ≤ f ⊤       := top_le_map f
    f ⊤ ≤ f (g ⊤) := monotone f (top_le_map g)
  map_le_sup' a b := calc
    f (g (a ⊔ b)) ≤ f (g a ⊔ g b) := monotone f (map_le_sup g a b)
    f (g a ⊔ g b) ≤ f (g a) ⊔ f (g b) := map_le_sup f (g a) (g b)
  inf_le_map' a b := calc
    f (g a) ⊓ f (g b) ≤ f (g a ⊓ g b) := inf_le_map f (g a) (g b)
    f (g a ⊓ g b)     ≤ f (g (a ⊓ b)) := monotone f (inf_le_map g a b)
  himp_le_map' a b := calc
    f (g a) ⇨ f (g b) ≤ f (g a ⇨ g b) := himp_le_map f (g a) (g b)
    f (g a ⇨ g b) ≤ f (g (a ⇨ b))     := monotone f (himp_le_map g a b)

@[simp]
lemma coe_comp (f : PreHeytingHom β γ) (g : PreHeytingHom α β) : ⇑(f.comp g) = f ∘ g := rfl

@[simp]
lemma comp_apply (f : PreHeytingHom β γ) (g : PreHeytingHom α β) (a : α) : f.comp g a = f (g a) := rfl

end PreHeytingHom
