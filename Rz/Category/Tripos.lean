import Lean

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Order.GaloisConnection

import Rz.Category.PreHeyt
import Rz.Category.Pullback

/-!
# Set-indexed triposes
-/

universe u v

namespace CategoricalLogic

open CategoryTheory Opposite

class ExistentialDoctrine (F : Type u ᵒᵖ ⥤ PreHeyt) where
  Exists : {X Y : Type u} → (f : X → Y) → F.obj (op X) → F.obj (op Y)
  exists_monotone : {X Y : Type u} → {f : X → Y} → Monotone (Exists f)
  exists_left_adj : {X Y : Type u} → {f : X → Y} → GaloisConnection (Exists f) (F.map (op f))
  exists_beck_chevalley :
    {W X Y Z : Type u} → {v : W → X} → {r : W → Y} → {s : X → Z} → {u : Y → Z} → {P : F.obj (op Y)} →
    IsPullbackSquare v r s u →
    F.map (op s) (Exists u P) ≤ Exists v (F.map (op r) P)

class UniversalDoctrine (F : Type u ᵒᵖ ⥤ PreHeyt) where
  Forall : {X Y : Type u} → (f : X → Y) → F.obj (op X) → F.obj (op Y)
  forall_monotone : {X Y : Type u} → {f : X → Y} → Monotone (Forall f)
  forall_right_adj : {X Y : Type u} → {f : X → Y} → GaloisConnection (F.map (op f)) (Forall f)
  forall_beck_chevalley :
    {W X Y Z : Type u} → {v : W → X} → {r : W → Y} → {s : X → Z} → {u : Y → Z} → {P : F.obj (op Y)} →
    IsPullbackSquare v r s u →
    Forall v (F.map (op r) P) ≤ F.map (op s) (Forall u P)

class Tripos (F : Type u ᵒᵖ ⥤ PreHeyt) extends ExistentialDoctrine F, UniversalDoctrine F where
  Generic : Type u
  Proof : F.obj (op Generic)
  classify : {X : Type u} → F.obj (op X) → (X → Generic)
  le_proof : {X : Type u} → (P : F.obj (op X)) → P ≤ F.map (op (classify P)) Proof
  proof_le : {X : Type u} → (P : F.obj (op X)) → F.map (op (classify P)) Proof ≤ P

open Lean Syntax Meta Elab Parser

declare_syntax_cat tripos
syntax "⊤" : tripos
syntax "⊥" : tripos
syntax tripos " ∧ " tripos : tripos
syntax tripos " ∨ " tripos : tripos
syntax tripos " → " tripos : tripos
syntax "∃" "(" binderIdent " : " term ")" "," tripos : tripos
syntax "∀" "(" binderIdent " : " term ")" "," tripos : tripos
syntax:10 term:max "(" term,* ")" : tripos
syntax  "(" tripos:min ")" : tripos

declare_syntax_cat ctxCell
syntax binderIdent " : " term:max : ctxCell

/-- Get the type of a context cell `x : tp`. -/
def CtxCell.getTp : TSyntax `ctxCell → MacroM (TSyntax `term)
| `(ctxCell| $x:binderIdent : $tp) => pure tp
| _ => Macro.throwUnsupported

/-- Get the identifier of a context cell `x : tp` -/
def CtxCell.getIdent : TSyntax `ctxCell → MacroM (TSyntax `term)
| `(ctxCell| $x:ident : $tp) => pure x
| `(ctxCell| _ : $tp) => `(_)
| _ => Macro.throwUnsupported


/-- Transform a context into a left-associated product type.
    This will only introduce `Unit` if the provided context is empty. -/
syntax "ctx_tp%" ctxCell,* : term

macro_rules
| `(ctx_tp%) => `(Unit)
| `(ctx_tp% $x:binderIdent : $tp:term, $ctx,*) =>
  Array.foldlM (β := Term)
    (fun acc cell => do `($acc × $(← CtxCell.getTp cell)))
    tp
    ctx.getElems

/-- Construct a pattern from a context. -/
syntax "ctx_pat% " ctxCell,* : term

macro_rules
| `(ctx_pat%) => `(())
| `(ctx_pat% $cell:ctxCell, $ctx:ctxCell,*) => do
  Array.foldlM (β := Term)
    (fun pat cell => do `(($pat, $(← CtxCell.getIdent cell))))
    (← CtxCell.getIdent cell)
    ctx.getElems


/-- Construct a substitution from a list of terms. -/
syntax "subst% "term,* : term

macro_rules
| `(subst%) => `(PUnit.unit)
| `(subst% $tm:term) => `($tm)
| `(subst% $tm:term, $tms:term,*) => `(Prod.mk $tm (subst% $tms,*))

/-- Construct an element of the preheyting algebra from a formula. -/
syntax "formula%" term:max " ⊨ " ctxCell,* " ⊢ " tripos : term

macro_rules
| `(formula% $P:term ⊨ $_:ctxCell,* ⊢ ⊤) => `(Top.top)
| `(formula% $P:term ⊨ $_:ctxCell,* ⊢ ⊥) => `(Bot.bot)
| `(formula% $P:term ⊨ $ctx:ctxCell,* ⊢ $p ∧ $q) =>
    `(Inf.inf (formula% $P:term ⊨ $ctx,* ⊢ $p) (formula% $P:term ⊨ $ctx,* ⊢ $q))
| `(formula% $P:term ⊨ $ctx:ctxCell,* ⊢ $p ∨ $q) =>
    `(Sup.sup (formula% $P:term ⊨ $ctx,* ⊢ $p) (formula% $P:term ⊨ $ctx,* ⊢ $q))
| `(formula% $P:term ⊨ $ctx:ctxCell,* ⊢ $p → $q) =>
    `(HImp.himp (formula% $P:term ⊨ $ctx,* ⊢ $p) (formula% $P:term ⊨ $ctx,* ⊢ $q))
| `(formula% $P:term ⊨ $ctx:ctxCell,* ⊢ ∃($x:binderIdent : $a:term), $p) => do
    let ctx' := ctx.push (← `(ctxCell| $x:binderIdent : $a:term))
    `(ExistentialDoctrine.Exists (@Prod.fst _ $a) (formula% $P:term ⊨ $ctx',* ⊢ $p))
| `(formula% $P:term ⊨ $ctx:ctxCell,* ⊢ ∀ ($x:binderIdent : $a:term), $p) => do
    let ctx' := ctx.push (← `(ctxCell| $x:binderIdent : $a:term))
    `(UniversalDoctrine.Forall (@Prod.fst _ $a) (formula% $P:term ⊨ $ctx',* ⊢ $p))
| `(formula% $P:term ⊨ $ctx:ctxCell,* ⊢ $t:term ($args:term,*)) =>
    `(($P).map (op (fun (ctx_pat% $ctx,*) => (subst% $args,*))) $t)
| `(formula% $P:term ⊨ $ctx:ctxCell,* ⊢ ($p)) =>
    `(formula% $P:term ⊨ $ctx,* ⊢ $p)

/-- Construct an element of the preheyting algebra from a list of formulas via conjunction. -/
syntax "hypotheses%" term:max " ⊨ " ctxCell,* " ⊢ " tripos,* : term

macro_rules
| `(hypotheses% $P ⊨ $ctx,* ⊢ ) => `(@Top.top (($P).obj (op (ctx_tp% $ctx,*))) _)
| `(hypotheses% $P ⊨ $ctx,* ⊢ $p:tripos) => `(formula% $P ⊨ $ctx,* ⊢ $p)
| `(hypotheses% $P ⊨ $ctx,* ⊢ $p:tripos, $ps:tripos,*) => `(Inf.inf (formula% $P ⊨ $ctx,* ⊢ $p) (hypotheses% $P ⊨ $ctx,* ⊢ $ps,*))

/-- Construct an implication in the preheyting algebra. -/
syntax term " ⊨ " ctxCell,* " | " tripos,* " ⊢ " tripos : term

/-- Shorthand for globally true propositions in a tripos. -/
syntax term " ⊨ " tripos : term

macro_rules
| `($P:term ⊨ $ctx,* | $ps,* ⊢ $p) => `(@LE.le (($P).obj (op (ctx_tp% $ctx,*))) _ (hypotheses% $P ⊨ $ctx,* ⊢ $ps,*) (formula% $P ⊨ $ctx,* ⊢ $p))
| `($P:term ⊨ $p:tripos) => `(@LE.le (($P).obj PUnit) _ Top.top (formula% $P ⊨ ⊢ $p))

end CategoricalLogic
