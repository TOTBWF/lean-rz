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
def HasEval.Refines [HasEval α] (ρ : Bwd α) (e₁ e₂ : FreeMagma α) : Prop := (a : α) → HasEval.Eval ρ e₁ a → HasEval.Eval ρ e₂ a
def HasEval.Equiv [HasEval α] (ρ : Bwd α) (e₁ e₂ : FreeMagma α) : Prop := HasEval.Refines ρ e₁ e₂ ∧ HasEval.Refines ρ e₂ e₁

syntax term " ⊢ " magma " ↑" : term
syntax term " ⊢ " magma " ↓" : term
syntax term " ⊢ " magma " ⇓ " term:40 : term
syntax term " ⊢ " magma " ≤ " withPosition(magma) : term
syntax term " ⊢ " magma " ≃ " withPosition(magma) : term

macro_rules
| `($ρ:term ⊢ $e:magma ↑) => `(HasEval.Undefined $ρ («magma» $e))
| `($ρ:term ⊢ $e:magma ↓) => `(HasEval.Defined $ρ («magma» $e))
| `($ρ:term ⊢ $e:magma ⇓ $a:term) => `(HasEval.Eval $ρ («magma» $e) $a)
| `($ρ:term ⊢ $e₁:magma ≤ $e₂:magma) => `(HasEval.Refines $ρ («magma» $e₁) («magma» $e₂))
| `($ρ:term ⊢ $e₁:magma ≃ $e₂:magma) => `(HasEval.Equiv $ρ («magma» $e₁) («magma» $e₂))

/-- Partial Applicative Structures. -/
class PAS (α : Type u) extends HasEval α where
  /-- The evaluation relation is functional. -/
  eval_functional : (ρ : Bwd α) → (e : FreeMagma α) → (a a' : α) → ρ ⊢ e ⇓ a → (ρ ⊢ e ⇓ a') → a = a'
  var_eval : (ρ : Bwd α) → (x : Fin ρ.length) → ρ ⊢ $(FreeMagma.var x) ⇓ ρ.get x
  var_oob : (ρ : Bwd α) → (x : Nat) → ρ.length ≤ x → ρ ⊢ $(FreeMagma.var x) ↑
  const_eval : (ρ : Bwd α) → (a : α) → ρ ⊢ a ⇓ a
  ap_eval : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → {a₁ a₂ : α} → ρ ⊢ e₁ ⇓ a₁ → ρ ⊢ e₂ ⇓ a₂ → ρ ⊢ e₁ e₂ ≃ a₁ a₂
  ap_left_defined : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ e₂ ↓ → ρ ⊢ e₁ ↓
  ap_right_defined : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ e₂ ↓ → ρ ⊢ e₂ ↓

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
  abs_eval : (ρ : Bwd α) → (a : α) → (e : FreeMagma α) → ρ ⊢ $(abs e) a ≃ $(e [ a ])

/-!
# SKI forms a basis for PCAs (and v.v.)
-/

class SKI (α : Type u) extends PAS α where
  s : α
  k : α
  i : α
  s_defined_2 : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ ↓ → ρ ⊢ e₂ ↓ → ρ ⊢ s e₁ e₂ ↓
  k_defined_const : (ρ : Bwd α) → (a : α) → ρ ⊢ k a ↓
  s_eval_const : (ρ : Bwd α) → (a b c : α) → ρ ⊢ s a b c ≃ (a b) (a c)
  k_eval_const : (ρ : Bwd α) → (a b : α) → ρ ⊢ k a b ⇓ a
  i_eval_const : (ρ : Bwd α) → (a : α) → ρ ⊢ i a ⇓ a

namespace SKI

open SKI


theorem s_defined_1
  [A : SKI α]
  {ρ : Bwd α} {e : FreeMagma α}
  (e_defined : ρ ⊢ e ↓)
  : ρ ⊢ A.s e ↓ :=
  PAS.ap_left_defined (s_defined_2 e_defined (PAS.const_defined ρ k))
  -- have ⟨ a , a_eval ⟩ := e_defined
  -- apply PAS.ap_defined
  -- · apply PAS.const_eval
  -- · exact a_eval
  -- · apply s_defined_1_const

-- theorem s_defined_2
--   [A : SKI α]
--   {ρ : Bwd α} {e₁ e₂ : FreeMagma α}
--   (e₁_defined : ρ ⊢ e₁ ↓) (e₂_defined : ρ ⊢ e₂ ↓)
--   : ρ ⊢ A.s e₁ e₂ ↓ :=
--   have ⟨ a₁ , a₁_eval ⟩ := e₁_defined
--   have ⟨ a₂ , a₂_eval ⟩ := e₂_defined
--   have ⟨ a₃ , a₃_eval ⟩ := s_defined_2_const ρ a₁ a₂
--   have cool := (PAS.ap_eval _ _)
--   -- ⟨ a₃ , (PAS.ap_eval ((PAS.ap_eval (PAS.const_eval ρ A.s) a₁_eval).2 _ _) a₂_eval).2 a₃ _ ⟩
--   -- have ⟨ a₁ , a₁_eval ⟩ := e₁_defined
--   -- have ⟨ a₂ , a₂_eval ⟩ := e₂_defined
--   -- apply PAS.ap_defined
--   -- · sorry
--   -- · sorry
--   -- · sorry
--   -- PAS.ap_defined a₁_eval a₂_eval _
--   -- apply PAS.ap_defined
--   -- · exact a₁_eval
--   -- · sorry
--   -- · sorry


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
    · apply SKI.k_defined_const
  | .const a =>
    simp
    apply PAS.ap_defined
    · apply PAS.const_eval
    · apply PAS.const_eval
    · apply SKI.k_defined_const
  | .ap e₁ e₂ =>
    simp
    apply s_defined_2
    · have : e₁.fv ≤ ρ.length + 1 := Trans.trans (FreeMagma.fv_left_le_fv_ap e₁ e₂) h
      exact SKI.abs_defined ρ e₁ this
    · have : e₂.fv ≤ ρ.length + 1 := Trans.trans (FreeMagma.fv_right_le_fv_ap e₁ e₂) h
      exact SKI.abs_defined ρ e₂ this

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
