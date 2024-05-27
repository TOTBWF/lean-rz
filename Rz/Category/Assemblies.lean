import Rz.Syntax.Magma
import Rz.Algebra.PCA

universe u v w

variable {α β γ δ : Type u}

class Assembly (α : outParam (Type u)) [PCA α] (β : Type v) where
  Realizes : α → β → Prop
  realizer : ∀ x : β, ∃ a : α, Realizes a x

infix:25 " ⊩ " => Assembly.Realizes

structure AssemblyHom (β : Type u) (γ : Type v) [PCA α] [Assembly α β] [Assembly α γ] where
  protected toFun : β → γ
  code : FreeMagma α
  code_defined : .nil ⊢ code ↓
  tracks : {ax afx : α} → {x : β} → ax ⊩ x → .nil ⊢ code ax ⇓ afx → afx ⊩ (toFun x)

infixr:25 " →ₐ " => AssemblyHom

namespace AssemblyHom

variable [PCA α] [Assembly α β] [Assembly α γ] [Assembly α δ]

def id : AssemblyHom β β := {
  toFun := fun x => x
  code := PCA.i
  code_defined := PCA.abs_defined _ _
  tracks := by
    intros ax afx x rz afx_eval
    have : ax = afx := PCA.i_eval_eq afx_eval
    rwa [←this]
}

def comp (f : AssemblyHom β γ) (g : AssemblyHom γ δ) : AssemblyHom β δ := {
  toFun := fun x => g.toFun (f.toFun x)
  code := PCA.c f.code g.code
  code_defined := PCA.abs_defined _ _
  tracks := by
    intros ax afx x rz afx_eval
    simp [PCA.c] at *
    have cool : (.snoc .nil ax) ⊢ g.code (f.code `(0)) ⇓ afx := by
      apply PCA.abs_eval_le
      exact afx_eval
    have gf_eval' : (.nil :# ax) ⊢ g.code (f.code ax) ⇓ afx := by
      apply PAS.ap_congr_inv
      · sorry
      · sorry
    have gf_eval : .nil ⊢ g.code (f.code ax) ⇓ afx := by sorry
    have ⟨ vf , f_eval ⟩ := PAS.ap_right_defined ⟨ _ , gf_eval ⟩
    have f_rz : vf ⊩ f.toFun x := f.tracks rz f_eval
    exact g.tracks (afx := afx) f_rz (PAS.ap_congr gf_eval f_eval)
}

end AssemblyHom
