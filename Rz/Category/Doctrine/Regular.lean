import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.GaloisConnection

import Rz.Category.Cartesian
import Rz.Category.Doctrine.Basic
import Rz.Order.PreSemilattice

namespace CategoryTheory

universe w v u

class RegularDoctrine {C : Type u} (P : C → Type w) [Category C] [Cartesian C] extends Doctrine P where
  infSemilattice : {Γ : C} → PreInfSemilattice (P Γ)
  sub_le_top : {Γ Δ : C} → (σ : Γ ⟶ Δ) → PreservesTop (sub σ)
  sub_le_inf : {Γ Δ : C} → (σ : Γ ⟶ Δ) → PreservesInf (sub σ)
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
  rw [wk_keep, ←sub_comp]
  apply sub_monotone
  rw [←exists_left_adj]

lemma exists_frobenius_inv
    {Γ X : C} (Φ : P Γ) (ξ : P (Γ ⨯ X))
    : Exists X (Φ^* (wk X) ⊓ ξ) ≤ Φ ⊓ Exists X ξ := by
  simp; constructor
  · rw [exists_left_adj]; simp
  · apply exists_monotone; simp

instance
    {Γ Δ : C} {Φ ψ : P Δ} {σ : Γ ⟶ Δ} {ξ Ξ : P Γ}
    [SubCoe Φ σ ξ] [SubCoe ψ σ Ξ]
    : SubCoe (Φ ⊓ ψ) σ (ξ ⊓ Ξ) where
  sub_le := calc
    (Φ ⊓ ψ)^*σ ≤ Φ^*σ ⊓ ψ^*σ := Pre.le_inf (sub_monotone σ Pre.inf_le_left) (sub_monotone σ Pre.inf_le_right)
    Φ^*σ ⊓ ψ^*σ ≤ ξ ⊓ Ξ      := Pre.inf_mono SubCoe.sub_le SubCoe.sub_le
  le_sub := calc
    ξ ⊓ Ξ ≤ Φ^*σ ⊓ ψ^*σ      := Pre.inf_mono SubCoe.le_sub SubCoe.le_sub
    Φ^*σ ⊓ ψ^*σ ≤ (Φ ⊓ ψ)^*σ := sub_le_inf σ
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

lemma and.intro
    {Γ : C} {Φ ψ ξ : P Γ}
    (h1 : Φ ≤ ψ) (h2 : Φ ≤ ξ)
    : Φ ≤ ψ ⊓ ξ := sorry

lemma and.fst
    {Γ : C} {Φ ψ ξ : P Γ}
    (h : Φ ≤ ψ ⊓ ξ)
    : Φ ≤ ψ := sorry

lemma and.unpack
    {Γ : C} {Φ ψ ξ : P Γ}
    (h : Φ ≤ ψ ⊓ ξ)
    : Φ ≤ ψ ∧ Φ ≤ ξ := sorry

lemma and.snd
    {Γ : C} {Φ ψ ξ : P Γ}
    (h : Φ ≤ ψ ⊓ ξ)
    : Φ ≤ ξ := sorry

lemma exists.intro
    {Γ X : C} {Φ ξ : P Γ} {ψ : P (Γ ⨯ X)}
    (x : Γ ⟶ X)
    [SubCoe ψ (inst x) ξ]
    (h : Φ ≤ ξ)
    : Φ ≤ ⨿ X, ψ := sorry

lemma exists.elim
    {Γ X : C} {Φ ξ : P Γ} {ψ : P (Γ ⨯ X)}
    (h : Φ ≤ ⨿ X, ψ) (h' : {Ξ : P (Γ ⨯ X)} → Ξ ≤ Φ^*(wk X) → Ξ ≤ ψ → Ξ ≤ ξ^*(wk X))
    : Φ ≤ ξ :=
  cut h <| by
    apply le_trans (exists_frobenius Φ ψ)
    rw [exists_left_adj]
    exact h' Pre.inf_le_left Pre.inf_le_right


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
  total {_} {_} {x} p := exists.intro x p

protected def comp (F : InternalFunRel P X Y) (G : InternalFunRel P Y Z) : InternalFunRel P X Z where
  Fun := ⨿ Y, (F.Fun^* ⟨shift Y (wk Z); var Y⟩ ⊓ G.Fun^* ⟨var Y; shift Y (var Z)⟩)
  ext p q f := begin $ by
    apply exists.elim (hyp f)
    intro Ξ φ fg
    apply begin $ exists.intro (var Y) ?_
    have y_def : Ξ ≤ (var Y) ∼ (var Y) := F.strict_right (and.fst fg)
    simp; constructor
    · apply F.ext (le_trans φ _) y_def (and.fst fg)
      unfold shift wk
      rw [←pair_comp, ←sub_comp]
      apply sub_monotone π₁ p
    · apply G.ext y_def (le_trans φ _) (and.snd fg)
      unfold shift wk
      rw [←pair_comp, ←sub_comp]
      apply sub_monotone π₁ q
  strict_left f := by
    apply exists.elim (hyp f)
    intro Ξ φ fg
    simp
    exact F.strict_left (and.fst fg)
  strict_right f := by
    apply exists.elim (hyp f)
    intro Ξ φ fg
    simp
    exact G.strict_right (and.snd fg)
  functional p q := by
    apply exists.elim (hyp p)
    intro ξ φ fg
    apply exists.elim (hyp $ le_trans φ (sub_monotone (wk Y) q))
    intro Ξ ζ fg'
    simp at *
    have f := hyp (le_trans ζ (sub_monotone (wk Y) fg.1))
    have f' := hyp fg'.1
    have g := hyp (le_trans ζ (sub_monotone (wk Y) fg.2))
    have g' := hyp fg'.2
    have eq_y_y' := F.functional f f'
    exact begin $ G.functional (G.ext eq_y_y' (G.strict_right g) g) g'
  total {_} {_} {x} p := by
    apply exists.elim (F.total p)
    intro ξ φ f_def
    apply exists.elim (G.total (F.strict_right f_def))
    intro Ξ ξ g_def
    apply begin $ exists.intro (var Z) (exists.intro (shift Z (var Y)) _)
    simp; constructor
    · apply le_trans ξ _
      simp [shift, ←pair_comp, ←sub_comp]
      exact sub_monotone (wk Z) f_def
    · exact g_def

end  InternalFunRel
