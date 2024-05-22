/-
# Free Magmas
-/
import Lean

import Rz.Data.Bwd

open Lean Elab Meta Term

universe u v w

-- Not /really/ the free magma anymore...
inductive FreeMagma (α : Type u) (n : Nat) : Type u where
| var : Fin n → FreeMagma α n
| const : α → FreeMagma α n
| op : FreeMagma α n → FreeMagma α n → FreeMagma α n

namespace FreeMagma

def foldM [Monad m] (v : Fin n → m β) (c : α → m β) (o : β → β → m β) : FreeMagma α n → m β
| .var i => v i
| .const a => c a
| .op l r => do
  let a ← foldM v c o l
  let b ← foldM v c o r
  o a b


/-!
# Elaboration
-/

/-- Extensible elaboration of magma expressions. -/
class MagmaExpr (α : Type u) (β : outParam (Type v)) where
  expr : {n : Nat} → α → FreeMagma β n

@[default_instance]
instance : MagmaExpr α α where
  expr := .const

declare_syntax_cat magma
syntax ident : magma
syntax:10 magma:10 magma:11+ : magma
syntax "(" magma:min ")" : magma

unsafe def mkMagmaVar (u : Level) (tp : Expr) (vars : TSyntaxArray `ident) (x : Ident) : TermElabM Expr := do
  let size ← mkNumeral (mkConst ``Nat) vars.size
  -- Check to see if the variable is bound by the `magma` binding form.
  match Array.indexOf? vars x with
  | some ix =>
    -- If it is, construct a `var` with the correct de Bruijn index.
    let x ← mkNumeral (mkApp (mkConst ``Fin) size) (vars.size - ix - 1)
    pure (mkAppN (mkConst ``FreeMagma.var [u]) #[tp, size, x])
  | none =>
    -- Otherwise, elaborate `x` as an identifier, and pass it off to instance resolution.
    let v ← mkFreshLevelMVar
    let mvar ← mkFreshExprMVar none
    let e ← elabIdent x mvar
    let inst ← synthInstance (mkAppN (mkConst ``MagmaExpr [v, u]) #[mvar, tp])
    pure (mkAppN (mkConst ``MagmaExpr.expr [v, u]) #[mvar, tp, inst, size, e])


def mkMagmaOp (u : Level) (tp : Expr) (vars : TSyntaxArray `ident) (a : Expr) (args : Array Expr) : TermElabM Expr := do
  let size ← mkNumeral (mkConst ``Nat) vars.size
  pure (Array.foldl (fun acc arg => mkAppN (mkConst ``FreeMagma.op [u]) #[tp, size, acc, arg]) a args)

unsafe def mkMagmaExpr (u : Level) (tp : Expr) (vars : TSyntaxArray `ident) : Syntax → TermElabM Expr
| `(magma| $x:ident) =>
  mkMagmaVar u tp vars x
| `(magma| $a:magma $args:magma*) => do
  let ea ← mkMagmaExpr u tp vars a
  let eas ← Array.mapM (fun arg => mkMagmaExpr u tp vars arg) args
  mkMagmaOp u tp vars ea eas
| `(magma| ( $a )) => mkMagmaExpr u tp vars a
| _ => throwUnsupportedSyntax


syntax (name := magma_expr) "[magma|" ident* "|" magma "|]" : term

#check BinderInfo

@[term_elab magma_expr] unsafe def elabMagmaExpr : TermElab := fun stx _ =>
  match stx with
  | `([magma| $vars:ident* | $tm:magma |]) => do
    let u ← mkFreshLevelMVar
    let tp ← mkFreshExprMVar none
    mkMagmaExpr u tp vars tm
  | _ => throwUnsupportedSyntax



/-!
# Common Terms
-/

-- a ρ ~~~~> .op (.op a ρ₀)

def test (a : α) : FreeMagma α 3 := [magma| x y z | (x a) (x z) |]

#print test
