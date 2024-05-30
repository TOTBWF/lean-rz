/-
# Free Magmas
-/
import Lean

import Rz.Data.Nat
import Rz.Data.Idx
import Rz.Syntax.Subst

open Lean Syntax Meta Elab
open Tactic.Simp

universe u v w
variable {α β γ : Type u}

inductive FreeMagma (α : Type u) (n : Nat) : Type u where
| var : Idx n → FreeMagma α n
| const : α → FreeMagma α n
| ap : FreeMagma α n → FreeMagma α n → FreeMagma α n

namespace FreeMagma


@[simp] def aps {n} (e : FreeMagma α n) (es : List (FreeMagma α n)) : FreeMagma α n :=
  es.foldr (fun arg acc => FreeMagma.ap acc arg) e

/-!
# Syntax for magmas
-/

/-- Coerce into `MagmaSyntax`. -/
class MagmaSyntax (α : Type u) (n : Nat) (β : outParam (Type v)) where
  quote : α → FreeMagma β n

instance {n : Nat} : MagmaSyntax (FreeMagma α n) n α where
  quote e := e

instance {n : Nat} : MagmaSyntax α n α where
  quote := .const

syntax (name := term_whnfI) "whnfI% " ident term:max* : term

@[term_elab term_whnfI] def elabReduce : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(whnfI% $f $[$args]*) =>
    -- Note: this doesn't seem to add terminfo to `f`
    let some f ← Term.resolveId? f (withInfo := true) | throwUnknownConstant f.getId
    let e ← Term.elabAppArgs f #[] (args.map .stx) expectedType?
      (explicit := false) (ellipsis := false)
    whnfI e
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
| `(«magma» $a:magma $[$x:term]* ) => `(FreeMagma.aps («magma» $a) $x)
| `(«magma» $a:magma $args:magma*) => do
    Array.foldlM (β := Term) (fun acc arg => `(FreeMagma.ap $acc («magma» $arg))) (← `(«magma» $a)) args
| `(«magma» ( $a:magma )) => `(«magma» $a)
