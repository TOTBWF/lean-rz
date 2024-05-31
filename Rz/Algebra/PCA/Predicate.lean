import Mathlib.Init.Order.Defs
import Mathlib.Order.Notation
import Mathlib.Tactic.Use

import Rz.Algebra.PCA.Alternative
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
  use ⟨ term (abs («magma» (A.pair (l `(0)) (r `(0))))), abs_def ⟩
  intro x a px
  have ⟨ la_def, qx ⟩ := l_rz x a px
  have ⟨ ra_def, rx ⟩ := r_rz x a px
  refine ⟨ ?_, ⟨ A.ap l a ⇓, A.ap r a ⇓, ?_, ?_, ?_ ⟩ ⟩ <;> aesop
