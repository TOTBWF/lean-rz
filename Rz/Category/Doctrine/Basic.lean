import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Category.Preord

import Rz.Category.Cartesian

/-!
# Doctrines
-/

universe w v u

namespace CategoryTheory

/-- A `Doctrine` over a cartesian category `C` is a contravariant functor into the category of preorders.
    We opt to define doctrines as a bespoke typeclass to make it easier to extend to regular, coherent,
    first order, etc. This also has the additional benefit of not gunking up our goals with `op`. -/
class Doctrine {C : Type u} (P : C → Type w) [Category.{v} C] [Cartesian C] where
  /-- Every fibre of a doctrine carries the structure of a preorder. -/
  preorder : {Γ : C} → Preorder (P Γ)
  /-- A doctrine is equipped with an action of substitution. -/
  sub : {Γ Δ : C} → (Δ ⟶ Γ) → P Γ → P Δ
  /-- Substitution is monotone. -/
  sub_monotone : {Γ Δ : C} → (σ : Δ ⟶ Γ) → Monotone (sub σ)
  /-- Substitution along identity is identity. -/
  sub_id : {Γ : C} → (Φ : P Γ) → sub (𝟙 Γ) Φ = Φ
  /-- Substitution along composites is itself a composite. -/
  sub_comp : {Γ Δ Ψ : C} → (σ : Ψ ⟶ Δ) → (δ : Δ ⟶ Γ) → (Φ : P Γ) → sub σ (sub δ Φ) = sub (σ ≫ δ) Φ

notation Φ:max "^* " σ:max => Doctrine.sub σ Φ

variable {C : Type*} [Category C] [Cartesian C]
variable {P : C → Type w} [Doctrine P]

instance {Γ : C} : Preorder (P Γ) := Doctrine.preorder
export Doctrine (sub_monotone sub_id sub_comp)

attribute [simp] sub_comp sub_id


/-!
# Commuting substitutions
-/

section Substitutions

-- FIXME: Lean is trying to synthesize an instance for `outParam (P Γ)`
class SubCoe {Γ Δ : C} (Φ : P Δ) (σ : Γ ⟶ Δ) (Ψ : outParam (P Γ)) where
  sub_le : @LE.le (P Γ) _ (Φ^*σ) Ψ
  le_sub : @LE.le (P Γ) _ Ψ (Φ^*σ)

-- Perform simplification on substitutions once we've commuted them down as far as we can.
@[default_instance]
instance {Γ Δ : C} {σ δ : Δ ⟶ Γ} {Φ : P Γ} [S : Simp σ δ] : SubCoe Φ σ (Φ^* δ) where
  sub_le := by rw [S.simplify]
  le_sub := by rw [S.simplify]

instance instSubCoeSub
    {Γ Δ Ψ : C} {σ : Δ ⟶ Γ} {δ : Ψ ⟶ Δ} {Φ : P Γ} {ξ : P Ψ}
    [C : SubCoe Φ (δ ≫ σ) ξ]
    : SubCoe (Φ^* σ) δ ξ where
  sub_le := by
    rw [sub_comp]
    apply C.sub_le
  le_sub := by
    rw [sub_comp]
    apply C.le_sub

def hyp
    {Γ Δ : C} {Φ ψ : P Γ} {ξ : P Δ} {σ : Γ ⟶ Δ}
    (h : Φ ≤ ξ^*σ)
    [SubCoe ξ σ ψ]
    : Φ ≤ ψ := le_trans h SubCoe.sub_le

def begin
    {Γ Δ : C} {Φ ψ : P Γ} {ξ : P Δ} {σ : Γ ⟶ Δ}
    (h : Φ ≤ ψ)
    [SubCoe ξ σ ψ]
    : Φ ≤ ξ^* σ := le_trans h SubCoe.le_sub

end Substitutions
