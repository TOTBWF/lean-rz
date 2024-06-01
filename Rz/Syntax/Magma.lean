/-
# Free Magmas
-/
import Lean

import Rz.Data.Nat
import Rz.Data.Idx
import Rz.Syntax.Subst

open Lean Syntax Meta Elab

universe u v w
variable {α β γ : Type u}

inductive FreeMagma (α : Type u) (n : Nat) : Type u where
| var : Idx n → FreeMagma α n
| const : α → FreeMagma α n
| ap : FreeMagma α n → FreeMagma α n → FreeMagma α n
deriving Repr

namespace FreeMagma

def aps {n} (e : FreeMagma α n) (es : List (FreeMagma α n)) : FreeMagma α n :=
  es.foldr (fun arg acc => FreeMagma.ap acc arg) e

@[simp] def shift {n : Nat} : FreeMagma α n → FreeMagma α (n + 1)
| .var i => .var (.succ i)
| .const a => .const a
| .ap e₁ e₂ => .ap (shift e₁) (shift e₂)
