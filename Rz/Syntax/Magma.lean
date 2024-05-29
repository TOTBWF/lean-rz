/-
# Free Magmas
-/
import Lean

-- import Rz.Data.Bwd
import Rz.Data.Nat
import Rz.Syntax.Subst

open Lean Syntax Meta Elab
open Tactic.Simp

universe u v w
variable {α β γ : Type u}

inductive FreeMagma (α : Type u) : Type u where
| var : Nat → FreeMagma α
| const : α → FreeMagma α
| ap : FreeMagma α → FreeMagma α → FreeMagma α

namespace FreeMagma

@[simp] def fv : FreeMagma α → Nat
| .var x => x + 1
| .const _ => 0
| .ap e₁ e₂ => Nat.max (fv e₁) (fv e₂)

def revAps (e : FreeMagma α) (es : List (FreeMagma α)) : FreeMagma α :=
  es.foldr (fun a b => .ap b a) e

@[simp] theorem revAps_nil (e : FreeMagma α) : revAps e [] = e := rfl
@[simp] theorem revAps_cons (e : FreeMagma α) (a as) : revAps e (a :: as) = (revAps e as).ap a := rfl

theorem fv_const_le (a : α) (n : Nat) : (const a).fv ≤ n := Nat.zero_le _

theorem fv_left_le_fv_ap (e₁ e₂ : FreeMagma α) : e₁.fv ≤ (ap e₁ e₂).fv := Nat.le_max_left _ _

theorem fv_right_le_fv_ap (e₁ e₂ : FreeMagma α) : e₂.fv ≤ (ap e₁ e₂).fv := Nat.le_max_right _ _

theorem ap_closed_closed {e₁ e₂ : FreeMagma α} (h : (ap e₁ e₂).fv = 0) : e₁.fv = 0 ∧ e₂.fv = 0 :=
  Nat.eq_zero_of_max_eq_zero h

def rename (e : FreeMagma α) (ρ : Rn) : FreeMagma α :=
match e with
| .var x => .var (ρ x)
| .const a => .const a
| .ap e₁ e₂ => .ap (rename e₁ ρ) (rename e₂ ρ)

def subst (e : FreeMagma α) (σ : Sb (FreeMagma α)) : FreeMagma α :=
match e with
| .var x => σ x
| .const a => .const a
| .ap e₁ e₂ => .ap (subst e₁ σ) (subst e₂ σ)

instance : Rename (FreeMagma α) where
  rename := rename

instance : Var (FreeMagma α) where
  var := .var

instance : Subst (FreeMagma α) where
  subst := subst

instance : HAct α (FreeMagma α) (FreeMagma α) where
  hAct a e := subst e (Sb.id ;; (FreeMagma.const a))

/-!
# Syntax for magmas
-/

/-- Coerce into `MagmaSyntax`. -/
class MagmaSyntax (α : Type u) (β : outParam (Type v)) where
  quote : α → FreeMagma β

instance : MagmaSyntax (FreeMagma α) α where
  quote e := e

instance : MagmaSyntax α α where
  quote := .const

syntax (name := term_whnfI) "whnfI% " ident term:max* : term

@[term_elab term_whnfI] def elabWhnfI : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(whnfI% $f $[$args]*) =>
    -- Note: this doesn't seem to add terminfo to `f`
    let some f ← Term.resolveId? f (withInfo := true) | throwUnknownConstant f.getId
    let e ← Term.elabAppArgs f #[] (args.map .stx) expectedType?
      (explicit := false) (ellipsis := false)
    let e ← instantiateMVars e
    whnfI <| (← Term.tryPostponeIfHasMVars? e).getD e
  | _ => throwUnsupportedSyntax

declare_syntax_cat magma
syntax ident : magma
syntax "$(" term:min ")" : magma
syntax "`(" term:min ")" : magma
syntax magma "$[" term:min "]*" : magma
syntax:10 magma:10 (colGt magma:11)+ : magma
syntax "(" magma:min ")" : magma
syntax "«magma»" magma : term

macro_rules
| `(«magma» $x:ident ) => `(whnfI% MagmaSyntax.quote $x)
| `(«magma» $($x:term) ) => `(whnfI% MagmaSyntax.quote $x)
| `(«magma» `($x:term) ) => `(FreeMagma.var $x)
| `(«magma» $a:magma $[$x:term]* ) => `(FreeMagma.revAps («magma» $a) $x)
| `(«magma» $a:magma $args:magma*) => do
    Array.foldlM (β := Term) (fun acc arg => `(FreeMagma.ap $acc («magma» $arg))) (← `(«magma» $a)) args
| `(«magma» ( $a:magma )) => `(«magma» $a)
