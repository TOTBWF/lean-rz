import Mathlib.Init.Order.Defs


import Rz.Algebra.PCA
import Rz.Syntax.Subst
import Rz.Syntax.HOL

universe u v w
variable {α X Y : Type u}

/-!
# P(A) valued predicates.
-/

def PCA.Pred (α : Type u) [PCA α] (X : Type v) := X → α → Prop

instance [PCA α] : Preorder (PCA.Pred α X) where
  le P Q := ∃ (f : FreeMagma α), ∀ (x : X), ∀ (a : α), P x a → ∃ (v : α), .nil ⊢ f a ⇓ v ∧ Q x v
  le_refl P := ⟨ PCA.id , fun x a px => ⟨ a , by simp , px ⟩ ⟩
  le_trans P Q R := fun ⟨ f , f_rz ⟩ ⟨ g , g_rz ⟩ =>
    ⟨ «magma» PCA.comp f g ,fun x a px =>
      have ⟨ fa, f_eval , qx ⟩ := f_rz x a px
      have ⟨ gfa , g_eval , rx ⟩ := g_rz x fa qx
      have comp_gf_eval : .nil ⊢ PCA.comp f g a ⇓ gfa := by
        simp
        rw [PAS.ap_congr]
        exists fa
      ⟨ gfa , comp_gf_eval , rx ⟩ ⟩
