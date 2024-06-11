import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice

import Rz.Category.Cartesian
import Rz.Category.Doctrine.Cartesian

namespace CategoryTheory

universe w v u

class WithExists {C : Type u} (P : C → Type w) [Category C] [Cartesian C] [CartesianDoctrine P] where
  Exists : {Γ : C} → (X : C) → P (Γ ⨯ X) → P Γ
  exists_monotone : {Γ X : C} → Monotone (Exists (Γ := Γ) X)
  exists_left_adj : {Γ X : C} → GaloisConnection (Exists (Γ := Γ) X) (Doctrine.sub (wk X))
  exists_beck_chevalley
    : {Γ Δ X : C} → (σ : Γ ⟶ Δ) → (Φ : P (Δ ⨯ X))
    → (Exists X Φ)^* σ ≤ Exists X (Φ^* (keep σ))
  exists_frobenius
    : {Γ X : C} → (Φ : P Γ) → (ξ : P (Γ ⨯ X))
    → Φ ⊓ Exists X ξ ≤ Exists X (Φ^* (wk X) ⊓ ξ)

variable {C : Type*} [Category C] [Cartesian C]
variable {P : C → Type w} [CartesianDoctrine P] [WithExists P]

open WithExists

@[simp]
lemma sub_exists
    {Γ Δ X : C} {σ : Γ ⟶ Δ} {Φ : P (Δ ⨯ X)}
    : (Exists X Φ)^* σ = Exists X (Φ^*(keep σ)) := by
  apply le_antisymm
  · apply exists_beck_chevalley
  · rw [exists_left_adj]
    rw [sub_comm (wk X)]
    apply sub_monotone
    rw [←exists_left_adj]

@[simp]
lemma inf_exists
    {Γ X : C} (Φ : P Γ) (ξ : P (Γ ⨯ X))
    : Φ ⊓ Exists X ξ = Exists X (Φ^* (wk X) ⊓ ξ) := by
  apply le_antisymm
  · apply exists_frobenius
  · simp; constructor
    · rw [exists_left_adj]; simp
    · apply exists_monotone; simp

instance
    {Γ Δ X : C} {φ : P (Δ ⨯ X)} {σ : Γ ⟶ Δ} {ψ : P (Γ ⨯ X)}
    [S : SubComm φ (keep σ) ψ]
    : SubComm (Exists X φ) σ (Exists X ψ) where
  sub_comm := by rw[←S.sub_comm, sub_exists]
/-!
# Notation
-/

syntax "∃" term ", " doctrine : doctrine

macro_rules
| `(«doctrine» ∃ $X, $φ) => `(WithExists.Exists $X («doctrine» $φ))

/-!
# Inference Rules
-/

lemma «Exists».intro
    {Γ X : C} {φ ξ : P Γ} {ψ : P (Γ ⨯ X)}
    (x : Γ ⟶ X)
    [SubComm ψ (inst x) ξ]
    (h : φ ≤ ξ)
    : P ⊨ Γ | φ ⊢ ∃ X, ψ :=
  le_trans h («Structural».subst (inst x) ((exists_left_adj ψ _).1 (le_refl _)))

lemma «Exists».elim
    {Γ X : C} {φ ξ : P Γ} {ψ τ : P (Γ ⨯ X)}
    (h : P ⊨ Γ | φ ⊢ ∃ X, ψ)
    [S : SubComm ξ (wk X) τ]
    (h' : {Ξ : P (Γ ⨯ X)} → Ξ ≤ φ^*(wk X) → Ξ ≤ ψ → Ξ ≤ τ)
    : P ⊨ Γ | φ ⊢ ξ :=
  «Structural».cut h <| calc
    φ ⊓ Exists X ψ ≤ Exists X (φ^*(wk X) ⊓ ψ) := by simp
    Exists X (φ^*(wk X) ⊓ ψ) ≤ ξ := by rw [exists_left_adj, S.sub_comm]; exact h' inf_le_left inf_le_right
