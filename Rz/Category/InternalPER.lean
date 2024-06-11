import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Lattice

import Rz.Category.Cartesian
import Rz.Category.Doctrine.Existential
import Rz.Category.Doctrine.Equality

/-!
# Internal PERs in a regular doctrine
-/

namespace CategoryTheory

universe w v u

variable {C : Type*} [Category C] [Cartesian C]
variable {P : C → Type w} [CartesianDoctrine P] [WithEquality P] [WithExists P]

open WithEquality
open WithExists

variable (P) in
class InternalPER (X : C) where
  Rel : {Γ : C} → (Γ ⟶ X) → (Γ ⟶ X) → P Γ
  isymm
    : {Γ : C} → {φ : P Γ} → {x y : Γ ⟶ X}
    → P ⊨ Γ | φ ⊢ $(Rel x y)
    → P ⊨ Γ | φ ⊢ $(Rel y x)
  itrans
    : {Γ : C} → {φ : P Γ} → {x y z : Γ ⟶ X}
    → P ⊨ Γ | φ ⊢ $(Rel x y) → P ⊨ Γ | φ ⊢ $(Rel y z)
    → P ⊨ Γ | φ ⊢ $(Rel x z)
  rel_sub
    : {Γ Δ : C} → {x y : Δ ⟶ X} → (σ : Γ ⟶ Δ)
    → (Rel x y)^*σ = Rel (σ ≫ x) (σ ≫ y)


/-!
# Notation
-/

syntax:35 term:max " ≈ " term:max : doctrine

macro_rules
| `(«doctrine» $x:term ≈ $y:term) => `(«doctrine» $(InternalPER.Rel $x $y))


namespace InternalPER

variable {Γ X : C} [InternalPER P X]
variable {φ : P Γ}


lemma left_rel
    {x y : Γ ⟶ X}
    (h : P ⊨ Γ | φ ⊢ x ≈ y)
    : P ⊨ Γ | φ ⊢ x ≈ x :=
  itrans h (isymm h)

lemma right_rel
    {x y : Γ ⟶ X}
    (h : P ⊨ Γ | φ ⊢ x ≈ y)
    : P ⊨ Γ | φ ⊢ y ≈ y :=
  itrans (isymm h) h

instance
    {Γ Δ : C} {x y : Δ ⟶ X} {σ : Γ ⟶ Δ} {x' y' : Γ ⟶ X}
    [L : VarComm (σ ≫ x) x'] [R : VarComm (σ ≫ y) y']
    : SubComm (P := P) (Rel x y) σ (Rel x' y') where
  sub_comm := by rw [←L.var_comm, ←R.var_comm, rel_sub σ]

end InternalPER

/-!
## Internal Functional Relations
-/

variable (P) in
@[ext]
structure InternalFunRel (X Y : C) [InternalPER P X] [InternalPER P Y] where
  Fun : {Γ : C} → (Γ ⟶ X) → (Γ ⟶ Y) → P Γ
  extensional
    : {Γ : C} → {φ : P Γ} → {x₁ x₂ : Γ ⟶ X} → {y₁ y₂ : Γ ⟶ Y}
    → (x_eq : P ⊨ Γ | φ ⊢ x₁ ≈ x₂) → (y_eq : P ⊨ Γ | φ ⊢ y₁ ≈ y₂)
    → (f : P ⊨ Γ | φ ⊢ $(Fun x₁ y₁))
    → P ⊨ Γ | φ ⊢ $(Fun x₂ y₂)
  strict_left
    : {Γ : C} → {φ: P Γ} → {x : Γ ⟶ X} → {y : Γ ⟶ Y}
    → P ⊨ Γ | φ ⊢ $(Fun x y)
    → P ⊨ Γ | φ ⊢ x ≈ x
  strict_right
    : {Γ : C} → {φ: P Γ} → {x : Γ ⟶ X} → {y : Γ ⟶ Y}
    → P ⊨ Γ | φ ⊢ $(Fun x y)
    → P ⊨ Γ | φ ⊢ y ≈ y
  functional
    : {Γ : C} → {φ : P Γ} → {x : Γ ⟶ X} → {y₁ y₂ : Γ ⟶ Y}
    → P ⊨ Γ | φ ⊢ $(Fun x y₁) → P ⊨ Γ | φ ⊢ $(Fun x y₂)
    → P ⊨ Γ | φ ⊢ y₁ ≈ y₂
  total
    : {Γ : C} → {φ : P Γ} → {x : Γ ⟶ X}
    → P ⊨ Γ | φ ⊢ x ≈ x
    → P ⊨ Γ | φ ⊢ ∃ Y, $(Fun (shift Y x) (var Y))
  fun_sub
    : {Γ Δ : C} → {x : Δ ⟶ X} → {y : Δ ⟶ Y} → (σ : Γ ⟶ Δ)
    → (Fun x y)^*σ = Fun (σ ≫ x) (σ ≫ y)


namespace InternalFunRel

variable {Γ X Y Z : C} [InternalPER P X] [InternalPER P Y] [InternalPER P Z]
variable {Φ : P Γ}
open InternalPER

instance
    {Γ Δ : C} {x : Δ ⟶ X} {y : Δ ⟶ Y} {σ : Γ ⟶ Δ} {x' : Γ ⟶ X} {y' : Γ ⟶ Y}
    [L : VarComm (σ ≫ x) x'] [R : VarComm (σ ≫ y) y'] {F : InternalFunRel P X Y}
    : SubComm (P := P) (F.Fun x y) σ (F.Fun x' y') where
  sub_comm := by rw [←L.var_comm, ←R.var_comm, F.fun_sub σ]


protected def id : InternalFunRel P X X where
  Fun := InternalPER.Rel
  extensional p q f := itrans (itrans (isymm p) f) q
  strict_left := left_rel
  strict_right := right_rel
  functional p q := itrans (isymm p) q
  total {_} {_} {x} p :=
    «Exists».intro x p
  fun_sub := rel_sub

protected def comp (F : InternalFunRel P X Y) (G : InternalFunRel P Y Z) : InternalFunRel P X Z where
  Fun x z := «doctrine» ∃ Y, $(F.Fun (shift Y x) (var Y)) ∧ $(G.Fun (var Y) (shift Y z))
  extensional p q fxy1 := by
    apply «Exists».elim fxy1
    intro Ξ σ fg
    apply «Exists».intro (var Y)
    have y_def : P ⊨ _ | Ξ ⊢ (var Y) ≈ (var Y) := F.strict_right («And».fst fg)
    apply «And».intro
    · apply F.extensional
      · exact (hyp (le_trans σ (sub_monotone _ p)))
      · exact y_def
      · exact («And».fst fg)
    · apply G.extensional
      · exact y_def
      · exact (hyp (le_trans σ (sub_monotone _ q)))
      · exact («And».snd fg)
  strict_left fxy := by
    apply «Exists».elim fxy
    intro Ξ σ fg
    apply F.strict_left («And».fst fg)
  strict_right fxy := by
    apply «Exists».elim fxy
    intro Ξ σ fg
    apply G.strict_right («And».snd fg)
  functional fxy1 fxy2 := by
    apply «Exists».elim fxy1
    intro ψ σ fg1
    apply «Exists».elim (hyp (le_trans σ (sub_monotone (wk Y) fxy2)))
    intro ξ δ fg2
    apply G.functional
    · apply G.extensional
      · apply F.functional
        · exact hyp (le_trans δ (sub_monotone (wk Y) («And».fst fg1)))
        · exact («And».fst fg2)
      · apply G.strict_right
        · exact hyp (le_trans δ (sub_monotone (wk Y) («And».snd fg1)))
      · exact hyp (le_trans δ (sub_monotone (wk Y) («And».snd fg1)))
    · exact («And».snd fg2)
  total {_} {_} {x} p := by
    apply «Exists».elim (F.total p)
    intro ψ σ f_def
    apply «Exists».elim (G.total (F.strict_right f_def))
    intro ξ δ g_def
    apply «Exists».intro (var Z)
    apply «Exists».intro (shift Z (var Y))
    apply «And».intro
    · exact hyp (le_trans δ (sub_monotone (wk Z) f_def))
    · exact g_def
  fun_sub σ := sub_comm σ
