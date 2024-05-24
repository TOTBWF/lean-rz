/-
# Partial Combinatory Algebras
-/
import Mathlib.Data.List.Indexes

import Rz.Data.Bwd
import Rz.Syntax.Magma
import Rz.Syntax.Subst


universe u v w
variable {α β : Type u}

/-!
# Partial Combinatory Algebras
-/

/-- Notation typeclass for Eval. -/
class HasEval (α : Type u) where
  /-- Big-step evaluation relation. -/
  Eval : (ρ : Bwd α) → FreeMagma α → α → Prop

def HasEval.Undefined [HasEval α] (ρ : Bwd α) (e : FreeMagma α) : Prop := (a : α) → ¬ (HasEval.Eval ρ e a)
def HasEval.Defined [HasEval α] (ρ : Bwd α) (e : FreeMagma α) : Prop := ∃ (a : α), HasEval.Eval ρ e a
def HasEval.Refines [HasEval α] (ρ₁ ρ₂ : Bwd α) (e₁ e₂ : FreeMagma α) : Prop := (a : α) → HasEval.Eval ρ₂ e₂ a → HasEval.Eval ρ₁ e₁ a
def HasEval.Equiv [HasEval α] (ρ₁ ρ₂ : Bwd α) (e₁ e₂ : FreeMagma α) : Prop := HasEval.Refines ρ₂ ρ₁ e₂ e₁ ∧ HasEval.Refines ρ₁ ρ₂ e₁ e₂

syntax term " ⊢ " magma " ↑" : term
syntax term " ⊢ " magma " ↓" : term
syntax term " ⊢ " magma " ⇓ " term:40 : term
syntax term " ⊢ " magma " ≤ " term:max " ⊢ " withPosition(magma) : term
syntax term " ⊢ " magma " ≃ " term:max " ⊢ " withPosition(magma) : term

-- ρ₁ ⊢ e₁ ≤ ρ₂ ⊢ e₂

macro_rules
| `($ρ:term ⊢ $e:magma ↑) => `(HasEval.Undefined $ρ («magma» $e))
| `($ρ:term ⊢ $e:magma ↓) => `(HasEval.Defined $ρ («magma» $e))
| `($ρ:term ⊢ $e:magma ⇓ $a:term) => `(HasEval.Eval $ρ («magma» $e) $a)
| `($ρ₁:term ⊢ $e₁:magma ≤ $ρ₂:term ⊢ $e₂:magma) => `(HasEval.Refines $ρ₂ $ρ₁ («magma» $e₂) («magma» $e₁))
| `($ρ₁:term ⊢ $e₁:magma ≃ $ρ₂:term ⊢ $e₂:magma) => `(HasEval.Equiv $ρ₁ $ρ₂ («magma» $e₁) («magma» $e₂))

/-- Partial Applicative Structures. -/
class PAS (α : Type u) extends HasEval α where
  /-- The evaluation relation is functional. -/
  eval_functional : (ρ : Bwd α) → (e : FreeMagma α) → (a a' : α) → ρ ⊢ e ⇓ a → ρ ⊢ e ⇓ a' → a = a'
  var_eval : (ρ : Bwd α) → (x : Fin ρ.length) → ρ ⊢ $(FreeMagma.var x) ⇓ ρ.get x
  var_oob : (ρ : Bwd α) → (x : Nat) → ρ.length ≤ x → ρ ⊢ $(FreeMagma.var x) ↑
  const_eval : (ρ : Bwd α) → (a : α) → ρ ⊢ a ⇓ a
  ap_eval : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → {a₁ a₂ : α} → ρ ⊢ e₁ ⇓ a₁ → ρ ⊢ e₂ ⇓ a₂ → ρ ⊢ e₁ e₂ ≃ ρ ⊢ a₁ a₂
  ap_left_defined : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ e₂ ↓ → ρ ⊢ e₁ ↓
  ap_right_defined : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ e₂ ↓ → ρ ⊢ e₂ ↓

theorem PAS.const_eval_eq
  [PAS α]
  (ρ : Bwd α)
  (a a' : α) (a_eval : ρ ⊢ a ⇓ a')
  : a = a' :=
    eval_functional ρ (.const a) a a' (const_eval ρ a) a_eval

theorem PAS.const_defined [PAS α] (ρ : Bwd α) (a : α) : ρ ⊢ a ↓ :=
  ⟨ a , PAS.const_eval ρ a ⟩

theorem PAS.ap_defined
  [PAS α]
  {ρ : Bwd α} {e₁ e₂ : FreeMagma α} {a₁ a₂ : α}
  (e₁_def : ρ ⊢ e₁ ⇓ a₁) (e₂_def : ρ ⊢ e₂ ⇓ a₂)
  (v_def : ρ ⊢ a₁ a₂ ↓)
  : ρ ⊢ e₁ e₂ ↓ :=
    let ⟨ w , h ⟩ := v_def
    ⟨ w , (ap_eval e₁_def e₂_def).2 w h ⟩

/-- Partial Combinatory Algebras. -/
class PCA (α : Type u) extends PAS α where
  /-- PCAs are equipped with a bracket abstraction operator. -/
  abs : FreeMagma α → FreeMagma α
  /-- Bracket abstraction yields a value. -/
  abs_defined : (ρ : Bwd α) → (e : FreeMagma α) → ρ ⊢ $(abs e) ↓
  /-- Bracket abstraction has a β-law. -/
  abs_eval : (ρ : Bwd α) → (a : α) → (e : FreeMagma α) → ρ ⊢ $(abs e) a ≃ (ρ :# a) ⊢ e

/-!
# SKI forms a basis for PCAs (and v.v.)
-/

class SKI (α : Type u) extends PAS α where
  s : α
  k : α
  i : α
  s_defined_2 : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ ↓ → ρ ⊢ e₂ ↓ → ρ ⊢ s e₁ e₂ ↓
  k_defined : {ρ : Bwd α} → {e : FreeMagma α} → ρ ⊢ e ↓ → ρ ⊢ k e ↓
  s_eval : (ρ : Bwd α) → (e₁ e₂ e₃ : FreeMagma α) → ρ ⊢ s e₁ e₂ e₃ ≃ ρ ⊢ (e₁ e₂) (e₁ e₃)
  k_eval : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → {a : α} → ρ ⊢ e₁ ⇓ a → ρ ⊢ e₂ ↓ → ρ ⊢ k e₁ e₂ ⇓ a
  i_eval : {ρ : Bwd α} → {e : FreeMagma α} → {a : α} → ρ ⊢ e ⇓ a → ρ ⊢ i e ⇓ a

namespace SKI

open SKI

theorem s_defined_1
  [A : SKI α]
  {ρ : Bwd α} {e : FreeMagma α}
  (e_defined : ρ ⊢ e ↓)
  : ρ ⊢ A.s e ↓ :=
  PAS.ap_left_defined (s_defined_2 e_defined (PAS.const_defined ρ k))

theorem i_eval_inv
  [A : SKI α]
  {ρ : Bwd α} {e : FreeMagma α} {a : α}
  (h : ρ ⊢ A.i e ⇓ a)
  : ρ ⊢ e ⇓ a := by sorry

@[simp] def abs [SKI α] : FreeMagma α → FreeMagma α
| .var 0 => .const i
| .var (n+1) => .ap (.const k) (.var n)
| .const a => .ap (.const k) (.const a)
| .ap e₁ e₂ => .ap (.ap (.const s) (abs e₁)) (abs e₂)

def abs_defined [SKI α] (ρ : Bwd α) (e : FreeMagma α) (h : e.fv ≤ ρ.length + 1) : ρ ⊢ $(SKI.abs e) ↓ := by
  match e with
  | .var 0 => simp; apply PAS.const_defined
  | .var (n+1) =>
    simp
    apply PAS.ap_defined
    · apply PAS.const_eval
    · apply PAS.var_eval ρ ⟨ n , Nat.le_of_succ_le_succ h ⟩
    · apply SKI.k_defined
      apply PAS.const_defined
  | .const a =>
    simp
    apply PAS.ap_defined
    · apply PAS.const_eval
    · apply PAS.const_eval
    · apply SKI.k_defined
      apply PAS.const_defined
  | .ap e₁ e₂ =>
    simp
    apply s_defined_2
    · have : e₁.fv ≤ ρ.length + 1 := Trans.trans (FreeMagma.fv_left_le_fv_ap e₁ e₂) h
      exact SKI.abs_defined ρ e₁ this
    · have : e₂.fv ≤ ρ.length + 1 := Trans.trans (FreeMagma.fv_right_le_fv_ap e₁ e₂) h
      exact SKI.abs_defined ρ e₂ this

def abs_refines_le [SKI α] (ρ : Bwd α) (a : α) (e : FreeMagma α) : ρ ⊢ $(abs e) a ≤ (ρ :# a) ⊢ e := by
  intros v v_eval
  match e with
  | .var 0 =>
    simp at v_eval
    have cool : (ρ :# a) ⊢ $(FreeMagma.var 0) ⇓ a := PAS.var_eval (ρ :# a) ⟨ 0 , by simp ⟩
    have cooler : ρ ⊢ a ⇓ v := by
      apply i_eval_inv
      exact v_eval
    rwa [←PAS.const_eval_eq ρ a v cooler]
  | .var (n+1) => sorry
  | .const a => sorry
  | .ap e₁ e₂ => sorry

end SKI
    -- exists _
    -- sorry
    -- exact ⟨ _ , _ ⟩
    -- -- have ⟨  ⟩
    -- sorry
    -- -- apply PAS.ap_defined
    -- -- · sorry
    -- -- · exact a₂_defined
    -- -- · sorry
    -- -- -- · apply PAS.ap_defined
    -- -- --   · apply PAS.const_eval
    -- -- --   · apply PAS.const_eval
    -- -- --   · apply PAS.ap_defined
    -- -- --     · sorry
    -- -- --     · sorry
    -- -- --     · sorry
