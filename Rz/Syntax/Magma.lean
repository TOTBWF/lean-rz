/-
# Free Magmas
-/
import Lean

import Rz.Data.Bwd
import Rz.Syntax.Subst

open Lean.Syntax

universe u v w
variable {α β γ : Type u}

inductive FreeMagma (α : Type u) : Type u where
| var : Nat → FreeMagma α
| const : α → FreeMagma α
| ap : FreeMagma α → FreeMagma α → FreeMagma α

namespace FreeMagma

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
  hAct a e := subst e (Sb.id ; (FreeMagma.const a))

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

declare_syntax_cat magma
syntax ident : magma
syntax "$(" term:min ")" : magma
syntax:10 magma:10 (colGt magma:11)+ : magma
syntax "(" magma:min ")" : magma
syntax "«magma»" magma : term

macro_rules
| `(«magma» $x:ident ) => `(MagmaSyntax.quote $x)
| `(«magma» $($x:term) ) => `(MagmaSyntax.quote $x)
| `(«magma» $a:magma $args:magma*) => do
    Array.foldlM (β := Term) (fun acc arg => `(FreeMagma.ap $acc («magma» $arg))) (← `(«magma» $a)) args
| `(«magma» ( $a:magma )) => `(«magma» $a)
