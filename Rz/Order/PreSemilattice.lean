import Mathlib.Init.Order.Defs
import Mathlib.Order.Notation
import Mathlib.Order.Hom.Basic

import Mathlib.Data.FunLike.Basic


universe u v w
variable {α β γ : Type*}

class PreInfSemilattice (α : Type u) [Preorder α] extends Top α, Inf α where
  /-- `⊤` is the greatest element -/
  protected le_top : ∀ a : α, a ≤ ⊤
  /-- The infimum is a lower bound on the first argument -/
  protected inf_le_left : ∀ a b : α, a ⊓ b ≤ a
  /-- The infimum is a lower bound on the second argument -/
  protected inf_le_right : ∀ a b : α, a ⊓ b ≤ b
  /-- The infimum is the *greatest* lower bound -/
  protected le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c

namespace Pre

variable [Preorder α] [PreInfSemilattice α] {a b c d : α}

@[simp]
lemma le_top : a ≤ ⊤ :=
  PreInfSemilattice.le_top _

@[simp]
lemma inf_le_left : a ⊓ b ≤ a :=
  PreInfSemilattice.inf_le_left _ _

@[simp]
lemma inf_le_right : a ⊓ b ≤ b :=
  PreInfSemilattice.inf_le_right _ _

lemma le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
  PreInfSemilattice.le_inf _ _ _

@[simp]
lemma le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
  ⟨ fun h => ⟨ le_trans h inf_le_left , le_trans h inf_le_right ⟩
  , fun ⟨ h1 , h2 ⟩ => le_inf h1 h2
  ⟩

end Pre

class PreservesMeets
    {α β : Type*}
    [Preorder α] [PreInfSemilattice α] [Preorder β] [PreInfSemilattice β]
    (f : α → β)
    where
  top_le_map : ⊤ ≤ f ⊤
  inf_le_map : ∀ (a b : α), f a ⊓ f b ≤ f (a ⊓ b)
