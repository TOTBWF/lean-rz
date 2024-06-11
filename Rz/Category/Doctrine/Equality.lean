import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice

import Rz.Category.Cartesian
import Rz.Category.Doctrine.Cartesian

/-!
# Cartesian doctrines
-/

namespace CategoryTheory

universe w v u

class WithEquality {C : Type u} (P : C → Type w) [Category C] [Cartesian C] [CartesianDoctrine P] where
  Equal : {Γ : C} → (X : C) → P (Γ ⨯ X) → P ((Γ ⨯ X) ⨯ X)
  equal_monotone : {Γ X : C} → Monotone (Equal (Γ := Γ) X)
  equal_left_adj : {Γ X : C} → GaloisConnection (Equal (Γ := Γ) X) (Doctrine.sub (contr X))
  equal_beck_chevalley
    : {Γ Δ X : C} → (σ : Γ ⟶ Δ) → (Φ : P (Δ ⨯ X))
    → (Equal X Φ)^* (keep (keep σ)) ≤ Equal X (Φ^*(keep σ))
  equal_frobenius
    : {Γ X : C} → (Φ : P ((Γ ⨯ X) ⨯ X)) → (ξ : P (Γ ⨯ X))
    → Φ ⊓ Equal X ξ ≤ Equal X (Φ^*(contr X) ⊓ ξ)

variable {C : Type*} [Category C] [Cartesian C]
variable {P : C → Type w} [CartesianDoctrine P] [WithEquality P]

open WithEquality

@[simp]
lemma sub_equal
    {Γ Δ X : C} {σ : Γ ⟶ Δ} {Φ : P (Δ ⨯ X)}
    : (Equal X Φ)^* (keep (keep σ)) = Equal X (Φ^*(keep σ)) := by
  apply le_antisymm
  · apply equal_beck_chevalley
  · rw [equal_left_adj]
    rw [sub_comm (contr X)]
    apply sub_monotone
    rw [←equal_left_adj]

@[simp]
lemma inf_equal
    {Γ X : C} {Φ : P ((Γ ⨯ X) ⨯ X)} {ξ : P (Γ ⨯ X)}
    : Φ ⊓ Equal X ξ = Equal X (Φ^*(contr X) ⊓ ξ) := by
  apply le_antisymm
  · apply equal_frobenius
  · simp; constructor
    · rw [equal_left_adj]; simp
    · apply equal_monotone; simp

/-!
# Notation
-/

syntax:35 term:max " = " term:max : doctrine

macro_rules
| `(«doctrine» $x:term = $y:term) => `(«doctrine» $(Equal _ ⊤)($x, $y))

/-!
# Inference Rules
-/

lemma «Equal».sub_iff
    {Γ Δ X : C} {φ : P Γ} {σ : Γ ⟶ Δ} {x y : Δ ⟶ X}
    : (P ⊨ Γ | φ ⊢ (x = y) [σ]) ↔ (P ⊨ Γ | φ ⊢ (σ ≫ x) = (σ ≫ y)) := by
  simp [sub_comm σ]

lemma «Equal».refl
    {Γ X : C} {φ : P Γ} {x : Γ ⟶ X}
    : P ⊨ Γ | φ ⊢ x = x := calc
  φ ≤ ⊤                                                                              := by simp
  ⊤ = ⊤^* (inst x)                                                                   := symm sub_pres_top
  ⊤^* (inst x) ≤ ((Equal X ⊤)^* (contr X))^* (inst x)                                := sub_monotone _ (by rw [←equal_left_adj])
  ((Equal X ⊤)^* (contr X))^* (inst x) = ((Equal X ⊤)^*(inst (shift X x)))^*(inst x) := sub_comm (inst x)

lemma «Equal».subst
    {Γ X : C} {φ : P Γ} {x y : Γ ⟶ X}
    (ψ : P (Γ ⨯ X))
    (h : P ⊨ Γ | φ ⊢ x = y) (px : P ⊨ Γ | φ ⊢ ψ [inst x])
    : (P ⊨ Γ | φ ⊢ ψ [inst y]) := calc
  φ ≤ ψ^*(inst x) ⊓ ((Equal X ⊤)^*(inst (shift X y)))^*(inst x) := by
    apply «And».intro px; simpa using h
  _ = (((ψ^*(wk X) ⊓ Equal X ⊤))^*(inst (shift X y)))^*(inst x) := by
    rw [←sub_pres_inf]
    nth_rw 1 [sub_expand (ψ^*(wk X)) (inst (shift X y))]
    rw [←sub_pres_inf]
  _ = ((Equal X ψ)^*(inst (shift X y)))^*(inst x) := by
    simp [inf_equal, sub_comm (contr X)]
  _ ≤ ((ψ^*keep (wk X))^*(inst (shift X y)))^*(inst x) := by
    apply sub_monotone
    apply sub_monotone
    rw [equal_left_adj, sub_comm (contr X)]
  _ = ψ^*(inst y) := by
    rw[sub_comm (inst (shift X y)), sub_comm (inst x)]

lemma «Equal».symm
    {Γ X : C} {φ : P Γ} {x y : Γ ⟶ X}
    (h : P ⊨ Γ | φ ⊢ x = y)
    : P ⊨ Γ | φ ⊢ y = x :=
  «Equal».subst ((Equal X ⊤)^*(inst (shift X x))) h («Equal».refl)

lemma «Equal».trans
    {Γ X : C} {φ : P Γ} {x y z : Γ ⟶ X}
    (p : P ⊨ Γ | φ ⊢ x = y) (q : P ⊨ Γ | φ ⊢ y = z)
    : P ⊨ Γ | φ ⊢ x = z := by
  apply «Equal».subst _ («Equal».symm p) q
