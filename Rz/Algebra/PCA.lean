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
  eval_var : (ρ : Bwd α) → (x : Fin ρ.length) → ρ ⊢ $(FreeMagma.var x) ⇓ ρ.get x
  eval_oob : (ρ : Bwd α) → (x : Nat) → ρ.length ≤ x → ρ ⊢ $(FreeMagma.var x) ↑
  eval_const : (ρ : Bwd α) → (a : α) → ρ ⊢ a ⇓ a
  eval_ap : (ρ : Bwd α) → (e₁ e₂ : FreeMagma α) → (a₁ a₂ : α) → ρ ⊢ e₁ ⇓ a₁ → ρ ⊢ e₂ ⇓ a₂ → ρ ⊢ e₁ e₂ ≃ a₁ a₂



/-- Partial Combinatory Algebras. -/
class PCA (α : Type u) extends PAS α where
  /-- PCAs are equipped with a bracket abstraction operator. -/
  abs : FreeMagma α → FreeMagma α
  /-- Bracket abstraction yields a value. -/
  abs_defined : (ρ : Bwd α) → (e : FreeMagma α) → ρ ⊢ $(abs e) ↓
  /-- Bracket abstraction has a β-law. -/
  abs_eval : (ρ : Bwd α) → (a : α) → (e : FreeMagma α) → ρ ⊢ $(abs e) a ≃ $(e [ a ])


class SKI (α : Type u) extends PAS α where
  s : α
  k : α
  i : α
  s_defined : (a b : α) → .nil ⊢ s a b ↓
  k_defined : (a : α) → .nil ⊢ k a ↓
  s_eval : (a b c : α) → .nil ⊢ s a b c ≃ ((a b) (a c))
  k_eval : (a b : α) → .nil ⊢ k a b ⇓ a
  i_eval : (a : α) → .nil ⊢ i a ⇓ a
