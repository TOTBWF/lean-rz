import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Notation

import Rz.Tactic.Simp

universe v u

/-!
# Cartesian Categories

Mathlib builds the entire limit API atop of `HasLimit`, which asserts that the type of limit cones
is `NonEmpty`. This means that any consumers of the API are required to invoke choice to perform any
sort of construction, which is unacceptable for our purposes.

To work around this deficiency, we provide a separate API for categories with *chosen* products. Moreover,
we provide an API that privileges the elementary definition instead of cones; this makes goal display much nicer.
-/

namespace CategoryTheory

@[notation_class, ext]
class Product (C : Type*) where
  product : C → C → C

infixl:35 " ⨯ " => Product.product

/-- A category `C` equipped with a canonical choice of terminal object. -/
class WithTerminal (C : Type*) [Category C] extends Top C where
  protected unit : (X : C) → (X ⟶ ⊤)
  protected unit_unique : {X : C} → (f : X ⟶ ⊤) → f = unit X

/-- A category `C` is equipped with a product structure when there is a canonical choice of binary products. -/
class WithProducts (C : Type*) [Category C] extends Product C where
  protected proj1 : {X Y : C} → (X ⨯ Y) ⟶ X
  protected proj2 : {X Y : C} → (X ⨯ Y) ⟶ Y
  protected pair : {X Y Z : C} → (X ⟶ Y) → (X ⟶ Z) → (X ⟶ Y ⨯ Z)
  protected pair_proj1
    : {X Y Z : C} → {f : X ⟶ Y} → {g : X ⟶ Z}
    → pair f g ≫ proj1 = f
  protected pair_proj2
    : {X Y Z : C} → {f : X ⟶ Y} → {g : X ⟶ Z}
    → pair f g ≫ proj2 = g
  protected pair_unique
    : {X Y Z : C} → {p : X ⟶ Y ⨯ Z} → {f : X ⟶ Y} → {g : X ⟶ Z}
    → p ≫ proj1 = f → p ≫ proj2 = g
    → p = pair f g

/-!
## Notation for terminal objects
-/

scoped notation "!" => WithTerminal.unit

/-!
## Notation for products
-/

scoped notation "π₁" => WithProducts.proj1
scoped notation "π₂" => WithProducts.proj2
scoped notation:max "⟨" f:min "; " g:min "⟩" => WithProducts.pair f g

/-!
## Terminal object lemmas
-/

section WithTerminal

variable {C : Type*} [Category C] [WithTerminal C]

end WithTerminal

/-!
## Product lemmas
-/

section WithProducts

variable {C : Type*} [Cat : Category C] [Prod : WithProducts C]
variable {Γ Δ Ψ X Y Z W : C}
variable {f : X ⟶ Y} {g : X ⟶ Z}

def pair_eta
    (f : X ⟶ Y ⨯ Z)
    : f = ⟨f ≫ π₁; f ≫ π₂⟩ :=
  WithProducts.pair_unique rfl rfl

@[simp]
def pair_eta_id
    : ⟨π₁; π₂⟩ = 𝟙 (X ⨯ Y) := by
  apply symm (WithProducts.pair_unique _ _) <;> simp

@[ext 1000]
def pair_ext {f g : X ⟶ Y ⨯ Z}
    (h1 : f ≫ π₁ = g ≫ π₁) (h2 : f ≫ π₂ = g ≫ π₂)
    : f = g := by
  rw [WithProducts.pair_unique h1 h2]
  rw [←pair_eta]

@[simp]
def pair_proj1 : ⟨f;g⟩ ≫ π₁ = f := WithProducts.pair_proj1

@[simp]
def pair_proj2 : ⟨f;g⟩ ≫ π₂ = g := WithProducts.pair_proj2

@[simp]
def pair_proj1_assoc {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} : ⟨f;g⟩ ≫ (π₁ ≫ h) = f ≫ h := by
  rw [←Category.assoc, pair_proj1]

@[simp]
def pair_proj2_assoc {f : W ⟶ X} {g : W ⟶ Y} {h : Y ⟶ Z} : ⟨f;g⟩ ≫ (π₂ ≫ h) = g ≫ h := by
  rw [←Category.assoc, pair_proj2]

@[simp]
lemma pair_comp {h : Γ ⟶ X} : h ≫ ⟨f;g⟩ = ⟨h ≫ f;h ≫ g⟩ := by
  ext <;> simp

/-!
### De Bruijn operations
-/

def wk (X : C) : (Γ ⨯ X) ⟶ Γ := π₁

def var (X : C) : (Γ ⨯ X) ⟶ X := π₂

/-- Shift a de Bruijn variable up by one. -/
def shift (Y : C) (f : Γ ⟶ X) : (Γ ⨯ Y) ⟶ X := π₁ ≫ f

/-- Substitute for a variable. -/
def inst (x : Γ ⟶ X) : Γ ⟶ (Γ ⨯ X) := ⟨𝟙 Γ; x⟩

/-- Extend a substitution with a variable. -/
def keep (f : Γ ⟶ Δ) : (Γ ⨯ X) ⟶ (Δ ⨯ X) := ⟨π₁ ≫ f; π₂⟩

/-- Contraction. -/
def contr (X : C) : Γ ⨯ X ⟶ Γ ⨯ X ⨯ X := ⟨⟨π₁; π₂⟩; π₂⟩

/-- Exchange. -/
def exchg (X Y : C) : Γ ⨯ X ⨯ Y ⟶ Γ ⨯ Y ⨯ X := ⟨⟨π₁ ≫ π₁; π₂⟩; π₁ ≫ π₂⟩

end WithProducts

/-- A category `C` is cartesian when it has canonical choices of binary products and a canonical terminal object. -/
class Cartesian (C : Type*) [Category C] extends WithTerminal C, WithProducts C

variable {C : Type*} [Category C] [WithProducts C]
variable {Γ Δ X Y Z W : C}
variable {f : X ⟶ Y} {g : X ⟶ Z}
