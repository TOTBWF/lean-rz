import Mathlib.Init.Order.Defs
import Rz.Syntax.Magma
import Aesop

universe u v w
variable {α β : Type u}

class PAS (α : Type u) where
  ap : α → α → α
  Defined : α → Prop
  ap_def_left : {a b : α} → Defined (ap a b) → Defined a
  ap_def_right : {a b : α} → Defined (ap a b) → Defined b
  extensional : ∀ {a b}, (Defined a ↔ Defined b) → (Defined a → Defined b → a = b) → a = b

attribute [aesop unsafe 33%] PAS.ap_def_right
attribute [aesop unsafe 66%] PAS.ap_def_left

notation a:10 " ↓" => PAS.Defined a
notation a:10 " ↑" => ¬ PAS.Defined a

namespace PAS

variable [PAS α]

@[simp] def eval (ρ : List α) (e : FreeMagma α ρ.length) : α :=
match e with
| .var n => ρ.getIdx n
| .const a => a
| .ap e₁ e₂ => ap (eval ρ e₁) (eval ρ e₂)

instance Refine [PAS α] : Preorder α where
  le x y := Defined x → Defined y ∧ x = y
  le_refl x xd := ⟨ xd , rfl ⟩
  le_trans x y z r s xd :=
    have ⟨ yd , p ⟩ := r xd
    have ⟨ zd , q ⟩ := s yd
    ⟨ zd , Trans.trans p q ⟩

lemma ext
  {a b : α} {P : Prop} (l : a ↓ → P) (r : b ↓ → P) (h : P → a = b) : a = b := by
  apply extensional
  · exact ⟨ fun ad => by rwa [←h (l ad)], fun bd => by rwa [h (r bd)] ⟩
  · intro ad _bd
    exact (h (l ad))

end PAS

class PCA (α : Type u) extends PAS α where
  abs : {n : Nat} → FreeMagma α (n + 1) → FreeMagma α n
  abs_def : {ρ : List α} → {e : FreeMagma α ρ.length} → Defined (PAS.eval ρ e)
  abs_eval : {ρ : List α} → {e : FreeMagma α (ρ.length + 1)} → {v : α} → v ↓ → ap (PAS.eval ρ (abs e)) v = PAS.eval (v :: ρ) e

attribute [simp] PCA.abs_def
attribute [simp] PCA.abs_eval

namespace PCA

open PAS
variable [PCA α]

protected def id {n : Nat} : FreeMagma α n :=
  abs (.var 0)

@[simp] lemma id_def {ρ : List α} : eval ρ PCA.id ↓ := abs_def

@[simp] lemma id_eval {ρ : List α} {v : α} : ap (eval ρ PCA.id) v = v := by
  apply ext ?_ id abs_eval
  apply ap_def_right

protected def comp {n : Nat} : FreeMagma α n :=
  abs (abs (abs («magma» `(.succ .zero) (`(.succ (.succ .zero)) `(.zero)))))

@[simp] lemma comp_def {ρ : List α} : eval ρ PCA.comp ↓ := abs_def

@[simp] lemma comp_def_1 {ρ : List α} {v₁ : α} : ap (eval ρ PCA.comp) v₁ ↓ ↔ v₁ ↓ := by
  aesop (add norm PCA.comp)

@[simp] lemma comp_def_2 {ρ : List α} {v₁ v₂ : α} : ap (ap (eval ρ PCA.comp) v₁) v₂ ↓ ↔ v₁ ↓ ∧ v₂ ↓ := by
  aesop (add norm PCA.comp)

@[simp] lemma comp_eval {ρ : List α} {v₁ v₂ v₃ : α} : ap (ap (ap (eval ρ PCA.comp) v₁) v₂) v₃ = ap v₂ (ap v₁ v₃) := by
  apply ext (P := v₁ ↓ ∧ v₂ ↓ ∧ v₃ ↓) <;> aesop (add norm PCA.comp)

protected def const {n : Nat} : FreeMagma α n :=
  abs (abs (.var (.succ .zero)))

@[simp] lemma const_def {ρ : List α} : eval ρ PCA.const ↓ := abs_def

@[simp] lemma const_eval {ρ : List α} {v₁ v₂ : α} (v₂_def : v₂ ↓) : ap (ap (eval ρ PCA.const) v₁) v₂ = v₁ := by
  apply ext (P := v₁ ↓) ?_ id <;> aesop (add norm PCA.const)

end PCA
