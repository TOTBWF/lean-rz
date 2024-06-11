import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice

import Rz.Category.Cartesian
import Rz.Category.Doctrine.Basic

/-!
# Cartesian doctrines
-/

namespace CategoryTheory

universe w v u

class CartesianDoctrine {C : Type u} (P : C → Type w) [Category C] [Cartesian C] extends Doctrine P where
  protected top : {Γ : C} → P Γ
  protected le_top : {Γ : C} → (φ : P Γ) → φ ≤ top
  protected inf : {Γ : C} → P Γ → P Γ → P Γ
  protected inf_le_left : {Γ : C} → (φ ψ : P Γ) → inf φ ψ ≤ φ
  protected inf_le_right : {Γ : C} → (φ ψ : P Γ) → inf φ ψ ≤ ψ
  protected le_inf : {Γ : C} → (φ ψ ξ : P Γ) → φ ≤ ψ → φ ≤ ξ → φ ≤ inf ψ ξ
  protected sub_pres_top : {Γ Δ : C} → (σ : Γ ⟶ Δ) → top^*σ = top
  protected sub_pres_inf : {Γ Δ : C} → (σ : Γ ⟶ Δ) → (φ ψ : P Δ) → (inf φ ψ)^*σ = inf (φ^*σ) (ψ^*σ)

variable {C : Type*} [Category C] [Cartesian C]
variable {P : C → Type w} [CartesianDoctrine P]

instance instOrderTopDoctrine {Γ : C} : OrderTop (P Γ) where
  top := CartesianDoctrine.top
  le_top := CartesianDoctrine.le_top

instance instSemilatticeInfDoctrine {Γ : C} : SemilatticeInf (P Γ) where
  inf := CartesianDoctrine.inf
  inf_le_left := CartesianDoctrine.inf_le_left
  inf_le_right := CartesianDoctrine.inf_le_right
  le_inf := CartesianDoctrine.le_inf

@[simp]
lemma sub_pres_top {Γ Δ : C} {σ : Γ ⟶ Δ} : (⊤ : P Δ)^*σ = ⊤ :=
  CartesianDoctrine.sub_pres_top σ

@[simp]
lemma sub_pres_inf {Γ Δ : C} {σ : Γ ⟶ Δ} {φ ψ : P Δ} : (φ ⊓ ψ)^*σ = φ^*σ ⊓ ψ^*σ :=
  CartesianDoctrine.sub_pres_inf σ φ ψ

instance
    {Γ Δ : C} {φ ψ : P Δ} {σ : Γ ⟶ Δ} {ξ τ : P Γ}
    [L : SubComm φ σ ξ] [R : SubComm ψ σ τ]
    : SubComm (φ ⊓ ψ) σ (ξ ⊓ τ) where
  sub_comm := by simp [L.sub_comm, R.sub_comm]

/-!
# Notation
-/

syntax:max "⊤" : doctrine
syntax:50 doctrine:51 " ∧ " doctrine:50 : doctrine

macro_rules
| `(«doctrine» ⊤) => `(⊤)
| `(«doctrine» $p ∧ $q) => `((«doctrine» $p) ⊓ («doctrine» $q))

/-!
# Inference Rules
-/


lemma «Top».intro
  {Γ : C} {φ : P Γ}
  : P ⊨ Γ | φ ⊢ ⊤ := by simp

lemma «And».intro
    {Γ : C} {φ ψ ξ : P Γ}
    (h1 : P ⊨ Γ | φ ⊢ ψ) (h2 : P ⊨ Γ | φ ⊢ ξ)
    : P ⊨ Γ | φ ⊢ ψ ∧ ξ := by
  simp; constructor <;> assumption

lemma «And».fst
    {Γ : C} {φ ψ ξ : P Γ}
    (h : P ⊨ Γ | φ ⊢ ψ ∧ ξ)
    : P ⊨ Γ | φ ⊢ ψ :=
  le_trans h inf_le_left

lemma «And».snd
    {Γ : C} {φ ψ ξ : P Γ}
    (h : P ⊨ Γ | φ ⊢ ψ ∧ ξ)
    : P ⊨ Γ | φ ⊢ ξ :=
  le_trans h inf_le_right

lemma «Structural».cut
    {Γ : C} {φ ψ ξ : P Γ}
    (h1 : P ⊨ Γ | φ ⊢ ψ) (h2 : P ⊨ Γ | φ ∧ ψ ⊢ ξ)
    : P ⊨ Γ | φ ⊢ ξ :=
  le_trans (le_inf (le_refl φ) h1) h2
