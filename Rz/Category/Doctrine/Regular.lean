import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.GaloisConnection

import Rz.Category.Cartesian
import Rz.Category.Doctrine.Basic
import Rz.Order.PreSemilattice

namespace CategoryTheory

universe w v u

class RegularDoctrine {C : Type u} (P : C → Type w) [Category C] [Cartesian C] extends Doctrine P where
  infSemilattice : {Γ : C} → PreInfSemilattice (P Γ)
  sub_inf_pres_meets : {Γ Δ : C} → (σ : Γ ⟶ Δ) → PreservesMeets (sub σ)
  Equal : {Γ : C} → (X : C) → P (Γ ⨯ X) → P ((Γ ⨯ X) ⨯ X)
  equal_monotone : {Γ X : C} → Monotone (Equal (Γ := Γ) X)
  equal_left_adj : {Γ X : C} → GaloisConnection (Equal (Γ := Γ) X) (sub (contr X))
  equal_beck_chevalley
    : {Γ Δ X : C} → (σ : Γ ⟶ Δ) → (Φ : P (Δ ⨯ X))
    → (Equal X Φ)^* (keep (keep σ)) ≤ Equal X (Φ^*(keep σ))
  equal_frobenius
    : {Γ X : C} → (Φ : P ((Γ ⨯ X) ⨯ X)) → (ξ : P (Γ ⨯ X))
    → Φ ⊓ Equal X ξ ≤ Equal X (Φ^*(contr X) ⊓ ξ)
  Exists : {Γ : C} → (X : C) → P (Γ ⨯ X) → P Γ
  exists_monotone : {Γ X : C} → Monotone (Exists (Γ := Γ) X)
  exists_left_adj : {Γ X : C} → GaloisConnection (Exists (Γ := Γ) X) (sub (wk X))
  exists_beck_chevalley
    : {Γ Δ X : C} → (σ : Γ ⟶ Δ) → (Φ : P (Δ ⨯ X))
    → (Exists X Φ)^* σ ≤ Exists X (Φ^* (keep σ))
  exists_frobenius
    : {Γ X : C} → (Φ : P Γ) → (ξ : P (Γ ⨯ X))
    → Φ ⊓ Exists X ξ ≤ Exists X (Φ^* (wk X) ⊓ ξ)

variable {C : Type*} [Category C] [Cartesian C]
variable {P : C → Type w} [RegularDoctrine P]

instance {Γ : C} : PreInfSemilattice (P Γ) := RegularDoctrine.infSemilattice
instance {Γ Δ : C} {σ : Γ ⟶ Δ} : PreservesMeets (Doctrine.sub (P := P) σ) := RegularDoctrine.sub_inf_pres_meets σ

notation "⨿ " X ", " Φ => RegularDoctrine.Exists X Φ

namespace RegularDoctrine

lemma equal_beck_chevalley_inv
    {Γ Δ X : C} (σ : Γ ⟶ Δ) (Φ : P (Δ ⨯ X))
    : Equal X (Φ^* (keep σ)) ≤ (Equal X Φ) ^* (keep (keep σ)):= by
  rw [equal_left_adj]
  simp
  rw [←sub_comp]
  apply sub_monotone
  rw [←equal_left_adj]


lemma equal_frobenius_inv
    {Γ X : C} (Φ : P ((Γ ⨯ X) ⨯ X)) (ξ : P (Γ ⨯ X))
    : Equal X (Φ^*(contr X) ⊓ ξ) ≤ Φ ⊓ Equal X ξ := by
  simp; constructor
  · rw [equal_left_adj]; simp
  · apply equal_monotone; simp

lemma exists_beck_chevalley_inv
    {Γ Δ X : C} (σ : Γ ⟶ Δ) (Φ : P (Δ ⨯ X))
    : Exists X (Φ^* (keep σ)) ≤ (Exists X Φ)^* σ := by
  rw [exists_left_adj]
  simp
  rw [←sub_comp]
  apply sub_monotone
  rw [←exists_left_adj]

lemma exists_frobenius_inv
    {Γ X : C} (Φ : P Γ) (ξ : P (Γ ⨯ X))
    : Exists X (Φ^* (wk X) ⊓ ξ) ≤ Φ ⊓ Exists X ξ := by
  simp; constructor
  · rw [exists_left_adj]; simp
  · apply exists_monotone; simp

instance
    {Γ Δ X : C} {Φ : P (Δ ⨯ X)} {σ : Γ ⟶ Δ} {ξ : P (Γ ⨯ X)}
    [SubCoe Φ (keep σ) ξ]
    : SubCoe (⨿ X, Φ) σ (⨿ X, ξ) where
  sub_le := le_trans (exists_beck_chevalley σ Φ) (exists_monotone SubCoe.sub_le)
  le_sub := le_trans (exists_monotone SubCoe.le_sub) (exists_beck_chevalley_inv σ Φ)

lemma cut
    {Γ : C} {Φ ψ ξ : P Γ}
    (h : Φ ≤ ψ) (h' : Φ ⊓ ψ ≤ ξ)
    : Φ ≤ ξ :=
  le_trans (Pre.le_inf (le_refl _) h) h'

lemma begin
    {Γ : C} {Φ ψ ξ : P Γ}
    (h : {Ξ : P Γ} → Ξ ≤ Φ ⊓ ξ → Ξ ≤ ψ)
    : Φ ⊓ ξ ≤ ψ :=
  h (le_refl _)

lemma iexists.intro
    {Γ X : C} {Φ ξ : P Γ} {ψ : P (Γ ⨯ X)}
    (x : Γ ⟶ X)
    [SubCoe ψ (inst x) ξ]
    (h : Φ ≤ ξ)
    : Φ ≤ ⨿ X, ψ := sorry

lemma iexists.elim
    {Γ X : C} {Φ Ξ ξ : P Γ} {ψ : P (Γ ⨯ X)}
    (h : Φ ≤ ⨿ X, ψ) (h' : (x : Γ ⟶ X) → [SubCoe ψ (inst x) Ξ] → Ξ ≤ ξ)
    : Φ ≤ ξ := sorry

end RegularDoctrine

/-!
# PERs with respect to a regular doctrine
-/

variable (P) in
class InternalPER (X : C) where
  Rel : P (X ⨯ X)
  isymm
    : {Γ : C} → {Φ : P Γ} → {x y : Γ ⟶ X}
    → Φ ≤ Rel^* ⟨x; y⟩ → Φ ≤ Rel^* ⟨y; x⟩
  itrans
    : {Γ : C} → {Φ : P Γ} → {x y z : Γ ⟶ X}
    → Φ ≤ Rel^* ⟨x; y⟩ → Φ ≤ Rel^* ⟨y; z⟩ → Φ ≤ Rel^* ⟨x; z⟩

namespace InternalPER

open RegularDoctrine

variable {Γ X : C} [InternalPER P X]
variable {Φ : P Γ}

notation x:max "∼" y:max => Rel^* ⟨x; y⟩

lemma left_rel
    {x y : Γ ⟶ X}
    (h : Φ ≤ x ∼ y)
    : Φ ≤ x ∼ x :=
  itrans h (isymm h)

lemma right_rel
    {x y : Γ ⟶ X}
    (h : Φ ≤ x ∼ y)
    : Φ ≤ y ∼ y :=
  itrans (isymm h) h

end InternalPER

variable (P) in
structure InternalFunRel (X Y : C) [InternalPER P X] [InternalPER P Y] where
  Fun : P (X ⨯ Y)
  ext
    : {Γ : C} → {Φ : P Γ} → {x₁ x₂ : Γ ⟶ X} → {y₁ y₂ : Γ ⟶ Y}
    → (x_eq : Φ ≤ x₁ ∼ x₂) → (y_eq : Φ ≤ y₁ ∼ y₂) → (f : Φ ≤ Fun^* ⟨x₁; y₁⟩)
    → Φ ≤ Fun^* ⟨x₂; y₂⟩
  strict_left
    : {Γ : C} → {Φ : P Γ} → {x : Γ ⟶ X} → {y : Γ ⟶ Y}
    → Φ ≤ Fun^* ⟨x; y⟩ → Φ ≤ x ∼ x
  strict_right
    : {Γ : C} → {Φ : P Γ} → {x : Γ ⟶ X} → {y : Γ ⟶ Y}
    → Φ ≤ Fun^* ⟨x; y⟩ → Φ ≤ y ∼ y
  functional
    : {Γ : C} → {Φ : P Γ} → {x : Γ ⟶ X} → {y₁ y₂ : Γ ⟶ Y}
    → Φ ≤ Fun^*⟨x; y₁⟩ → Φ ≤ Fun^*⟨x; y₂⟩ → Φ ≤ y₁ ∼ y₂
  total
    : {Γ : C} → {Φ : P Γ} → {x : Γ ⟶ X}
    → Φ ≤ x ∼ x
    → Φ ≤ ⨿ Y, (Fun^* ⟨shift Y x; var Y⟩)

namespace InternalFunRel

variable {Γ X Y Z : C} [InternalPER P X] [InternalPER P Y] [InternalPER P Z]
variable {Φ : P Γ}

open InternalPER
open RegularDoctrine

protected def id : InternalFunRel P X X where
  Fun := InternalPER.Rel
  ext p q f := itrans (itrans (isymm p) f) q
  strict_left := left_rel
  strict_right := right_rel
  functional p q := itrans (isymm p) q
  total {_} {_} {x} p := iexists.intro x p

protected def comp (F : InternalFunRel P X Y) (G : InternalFunRel P Y Z) : InternalFunRel P X Z where
  Fun := ⨿ Y, (F.Fun^* ⟨shift Y (wk Z); var Y⟩ ⊓ G.Fun^* ⟨var Y; shift Y (var Z)⟩)
  ext p q f := by
    have cool := hyp f
    sorry
    -- iexists.elim f ?_
  strict_left := sorry -- left_rel
  strict_right := sorry -- right_rel
  functional p q := sorry -- itrans (isymm p) q
  total {_} {_} {x} p := sorry -- exist x p

end  InternalFunRel
