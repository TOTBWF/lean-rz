import Mathlib.Order.Basic
import Mathlib.Order.Hom.Basic

universe u v w

variable {α : Type u} {β : Type v}

/-!
# Pre-Heyting algebras

Mathlib builds the entire order heirarchy atop posets, so we need to define preheyting algebras ourselves.

HACK:
A more well-engineered solution would build heyting prealgebras as a tower of classes, but we do not
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

attribute [simp] PreHeyting.bot_le
attribute [simp] PreHeyting.le_top
attribute [simp] PreHeyting.le_sup_left
attribute [simp] PreHeyting.le_sup_right
attribute [simp] PreHeyting.inf_le_left
attribute [simp] PreHeyting.inf_le_right

/-!
# Morphisms of pre-Heyting algebras.
-/

/-- Morphisms of pre-Heyting algebras -/
structure PreHeytingHom (α β : Type*) [PreHeyting α] [PreHeyting β] extends OrderHom α β where
  map_le_bot : toFun ⊥ ≤ ⊥
  top_le_map : ⊤ ≤ toFun ⊤
  map_le_sup : ∀ a b : α, toFun (a ⊔ b) ≤ toFun a ⊔ toFun b
  inf_le_map : ∀ a b : α, toFun a ⊓ toFun b ≤ toFun (a ⊓ b)
  map_le_himp : ∀ a b : α, toFun a ⇨ toFun b ≤ toFun (a ⇨ b)

attribute [simp] PreHeytingHom.map_le_bot
attribute [simp] PreHeytingHom.top_le_map
attribute [simp] PreHeytingHom.map_le_sup
attribute [simp] PreHeytingHom.inf_le_map
attribute [simp] PreHeytingHom.map_le_himp

namespace PreHeytingHom

variable {α β : Type*} [PreHeyting α] [PreHeyting β]

instance instFunLike : FunLike (PreHeytingHom α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨ ⟨ _, _ ⟩, _, _, _, _, _ ⟩ := f
    obtain ⟨ ⟨ _, _ ⟩, _, _, _, _, _ ⟩ := g
    congr

@[ext]
theorem ext {f g : PreHeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[simp]
lemma sup_le_map
    [PreHeyting α] [PreHeyting β]
    (f : PreHeytingHom α β)
    (a b : α)
    : f a ⊔ f b ≤ f (a ⊔ b) := by
    apply PreHeyting.sup_le <;> apply f.monotone <;> simp

@[simp]
lemma map_le_inf
    [PreHeyting α] [PreHeyting β]
    (f : PreHeytingHom α β)
    (a b : α)
    : f (a ⊓ b) ≤ f a ⊓ f b := by
    apply PreHeyting.le_inf <;> apply f.monotone <;> simp

@[simp]
lemma himp_le_map
    [PreHeyting α] [PreHeyting β]
    (f : PreHeytingHom α β)
    (a b : α)
    : f (a ⇨ b) ≤ f a ⇨ f b := by
  simp [PreHeyting.le_himp_iff]
  trans
  · apply inf_le_map
  · apply f.monotone
    simp [←PreHeyting.le_himp_iff]

end PreHeytingHom
