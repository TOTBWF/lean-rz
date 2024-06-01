import Mathlib.Init.Order.Defs
import Mathlib.Order.Notation
import Mathlib.Tactic.Use

import Rz.Algebra.PCA
import Rz.Syntax.Subst
import Rz.Syntax.HOL

universe u v w
variable {α X Y : Type u}

/-!
# P(A) valued predicates.
-/
namespace PCA

open PAS

def Predicate (α : Type u) [PCA α] (X : Type v) := X → Val α → Prop

variable [A : PCA α]

instance : Preorder (Predicate α X) where
  le P Q := ∃ (f : Val α), ∀ (x : X), ∀ (a : Val α), P x a → ∃ (h : (A.ap f a) ↓), Q x ⟨ A.ap f a , h ⟩
  le_refl P := ⟨ A.id ⇓, by aesop ⟩
  le_trans P Q R := by
    intro ⟨ f , f_rz ⟩ ⟨ g , g_rz ⟩
    use ap (ap (A.comp) f) g ⇓
    intro x a px
    have ⟨ fa_def, qx ⟩ := f_rz x a px
    have ⟨ gfa_def, qx ⟩ := g_rz x (A.ap f a ⇓) qx
    aesop

/-!
## Meets
-/

instance : Inf (Predicate α X) where
  inf P Q x a := ∃ (l : Val α), ∃ (r : Val α), (a = ap (ap A.pair l) r) ∧ P x l ∧ Q x r

lemma inf_le_left
    {P Q : Predicate α X}
    : P ⊓ Q ≤ P := by
  use A.fst ⇓
  rintro x ⟨ a , a_def ⟩ ⟨ l , r , rfl , px, _ ⟩
  aesop

lemma inf_le_right
    {P Q : Predicate α X}
    : P ⊓ Q ≤ Q := by
  use A.snd ⇓
  rintro x ⟨ a , a_def ⟩ ⟨ l , r , rfl , _, qx ⟩
  aesop

lemma inf_universal
    {P Q R : Predicate α X}
    : P ≤ Q → P ≤ R → P ≤ Q ⊓ R := by
  intro ⟨ l , l_rz ⟩ ⟨ r , r_rz ⟩
  use («pca» fun x => ⟨ l x , r x ⟩) ⇓
  intro x a px
  have ⟨ la_def, qx ⟩ := l_rz x a px
  have ⟨ ra_def, rx ⟩ := r_rz x a px
  refine ⟨ ?_, ⟨ A.ap l a ⇓, A.ap r a ⇓, ?_, ?_, ?_ ⟩ ⟩ <;> aesop

/-!
## Joins
-/

instance : Sup (Predicate α X) where
  sup P Q x a := (∃ (l : Val α), (a = ap A.inl l) ∧ P x l) ∨ (∃ (r : Val α), (a = ap A.inr r) ∧ Q x r)

lemma left_le_sup
    {P Q : Predicate α X}
    : P ≤ P ⊔ Q := by
  use A.inl ⇓
  intro x a px
  refine ⟨ by simp, Or.inl ⟨ a, rfl, px ⟩ ⟩

lemma right_le_sup
    {P Q : Predicate α X}
    : Q ≤ P ⊔ Q := by
  use A.inr ⇓
  intro x a qx
  refine ⟨ by simp, Or.inr ⟨ a, rfl, qx ⟩ ⟩

lemma sup_universal
    {P Q R : Predicate α X}
    : P ≤ R → Q ≤ R → P ⊔ Q ≤ R := by
  intro ⟨ l , l_rz ⟩ ⟨ r , r_rz ⟩
  use («pca» A.elim l r) ⇓
  intro x a pqx
  match pqx with
  | Or.inl ⟨ la, eq, px ⟩ =>
    have ⟨ la_def , rx ⟩ := l_rz x la px
    aesop
  | Or.inr ⟨ ra, eq, qx ⟩ =>
    rw [eq]
    have ⟨ ra_def , rx ⟩ := r_rz x ra qx
    aesop

/-!
## Implications
-/
instance : HImp (Predicate α X) where
  himp P Q x f := ∀ (a : Val α), P x a → ∃ (h : A.ap f a ↓), Q x ⟨ A.ap f a , h ⟩

lemma himp_curry
    {P Q R : Predicate α X}
    : (P ⊓ Q ≤ R) → P ≤ (Q ⇨ R) := by
  intro ⟨ f , f_rz ⟩
  use (ap A.curry f) ⇓
  intro x a px
  use (by aesop)
  intro b qx
  have ⟨ d , rx ⟩ := f_rz x (_ ⇓) ⟨ a, b , rfl, px, qx ⟩
  refine ⟨ ?_, ?_ ⟩
  · simpa using d
  · simpa using rx

lemma himp_uncurry
    {P Q R : Predicate α X}
    : P ≤ (Q ⇨ R) → (P ⊓ Q ≤ R) := by
  intro ⟨ f , f_rz ⟩
  use (ap A.uncurry f) ⇓
  intro x ax ⟨ l , r , eq , px , qx ⟩
  have ⟨ d , qrx ⟩ := f_rz x l px
  have ⟨ d' , rx ⟩ := qrx r qx
  aesop

/-!
Existentials
-/

def Existential (f : X → Y) (P : Predicate α X) : Predicate α Y :=
  fun y a => ∃ (x : X), f x = y ∧ P x a

def Universal (f : X → Y) (P : Predicate α X) : Predicate α Y :=
  fun y a => ∀ (x : X) (b : Val α), (f x = y) ∧ ∃ (h : A.ap a b ↓), P x ⟨ A.ap a b , h ⟩
