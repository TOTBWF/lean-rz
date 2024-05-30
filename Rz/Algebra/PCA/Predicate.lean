import Mathlib.Init.Order.Defs


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

def Predicate (α : Type u) [PCA α] (X : Type v) := X → α → Prop

instance [PCA α] : Preorder (Predicate α X) where
  le P Q := ∃ (f : α), f ↓ ∧ ∀ (x : X), ∀ (a : α), P x a → Q x (ap f a)
  le_refl P := ⟨ eval [] PCA.id, by simp, fun x a px => by simpa ⟩
  le_trans P Q R := fun ⟨ f , f_rz ⟩ ⟨ g , g_rz ⟩ =>
    ⟨ ap (ap (eval [] PCA.comp) f) g, by simp [f_rz, g_rz], fun x a px => by aesop ⟩
