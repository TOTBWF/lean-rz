import Lean

import Mathlib.Init.Order.Defs

import Rz.Tactic.WHNFI
import Rz.Syntax.Magma
import Rz.Data.Vec

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

structure Val (α : Type u) [PAS α] where
  val : α
  defined : val ↓ := by aesop

instance [PAS α] : Coe (Val α) α where
  coe := Val.val

notation v " ⇓" => ⟨ v , by aesop ⟩

attribute [simp] Val.val
attribute [simp] Val.defined

namespace PAS

variable [PAS α]

lemma ext
  {a b : α} (P : Prop) (l : a ↓ → P) (r : b ↓ → P) (h : P → a = b) : a = b := by
  apply extensional
  · exact ⟨ fun ad => by rwa [←h (l ad)], fun bd => by rwa [h (r bd)] ⟩
  · intro ad _bd
    exact (h (l ad))

def aps (a : α) (as : List α) : α :=
  List.foldl ap a as

@[simp] lemma aps_nil (a : α) : aps a [] = a := rfl

@[simp] lemma aps_cons (a arg : α) (args : List α) : aps a (arg :: args) = aps (ap a arg) args := rfl

lemma aps_def_left {a : α} {args : List α} (aps_def : aps a args ↓) : a ↓ := by
  induction args generalizing a with
  | nil => simpa using aps_def
  | cons arg args IH =>
    apply ap_def_left
    apply (IH (a := ap a arg))
    simpa using aps_def

lemma aps_def_right {a : α} {args : List α} (aps_def : aps a args ↓) (arg : α) (mem : arg ∈ args) : arg ↓ := by
  induction mem generalizing a with
  | head => exact (ap_def_right (aps_def_left aps_def))
  | @tail arg args _ IH =>
    apply (IH (a := ap a arg))
    simpa using aps_def

@[simp] def eval {n : Nat} (e : FreeMagma α n) (ρ : Vec (Val α) n) : α :=
match e with
| .var n => ρ.get n
| .const a => a
| .ap e₁ e₂ => ap (eval e₁ ρ) (eval e₂ ρ)

def term (e : FreeMagma α 0) : α :=
  eval e .nil

@[simp] lemma const_term {a : α} : term (.const a) = a := rfl
@[simp] lemma ap_term {e₁ e₂ : FreeMagma α 0} : term (.ap e₁ e₂) = ap (term e₁) (term e₂) := rfl

instance Refine [PAS α] : Preorder α where
  le x y := Defined x → Defined y ∧ x = y
  le_refl x xd := ⟨ xd , rfl ⟩
  le_trans x y z r s xd :=
    have ⟨ yd , p ⟩ := r xd
    have ⟨ zd , q ⟩ := s yd
    ⟨ zd , Trans.trans p q ⟩

end PAS

class PCA (α : Type u) extends PAS α where
  abs : {n : Nat} → FreeMagma α (n + 1) → FreeMagma α n
  abs_def : {n : Nat} → {e : FreeMagma α (n + 1)} → {ρ : Vec (Val α) n} → PAS.eval (abs e) ρ ↓
  abs_eval : {n : Nat} → {e : FreeMagma α (n + 1)} → {a : α} → {ρ : Vec (Val α) n} → (a_def : a ↓) → ap (PAS.eval (abs e) ρ) a = PAS.eval e (.cons ⟨ a , a_def ⟩ ρ)

attribute [simp] PCA.abs_def
attribute [simp] PCA.abs_eval

namespace PCA

open Lean Syntax Meta Elab

/-!
# Notation
-/
class Splice (α : Type u) (v : Nat) (β : outParam (Nat → Type v)) where
  splice : α → β v


instance {v k : Nat} [S : Splice (FreeMagma α v) k (FreeMagma α)] : Splice (FreeMagma α v) (k + 1) (FreeMagma α) where
  splice e := FreeMagma.shift (S.splice e)

instance {v : Nat} : Splice (FreeMagma α v) v (FreeMagma α) where
  splice e := e

instance {v : Nat} : Splice α v (FreeMagma α) where
  splice a := .const a

instance {v : Nat} [PAS α] : Splice (Val α) v (FreeMagma α) where
  splice a := .const a


@[simp] def FreeMagma.abs [PCA α] {v : Nat} (k : FreeMagma α (v + 1) → FreeMagma α (v + 1)) : FreeMagma α v :=
  PCA.abs (k (.var 0))

declare_syntax_cat pca
syntax ident : pca
syntax "$(" term:min ")" : pca
syntax "fun " ident+ " => " pca : pca
syntax:10 pca:10 (colGt pca:11)+ : pca
syntax "(" pca:min ")" : pca
syntax "pca%" pca : term
syntax "«pca»" pca : term

macro_rules
| `(pca% $x:ident) => `(whnfI% Splice.splice $x)
| `(pca% $($x:term) ) => `(whnfI% Splice.splice $x)
| `(pca% fun $xs:ident* => $a:pca ) => do
   Array.foldrM (β := Term) (fun x acc => `(FreeMagma.abs (fun $x => $acc))) (← `(pca% $a)) xs
| `(pca% $a:pca $args:pca*) => do
    Array.foldlM (β := Term) (fun acc arg => `(FreeMagma.ap $acc (pca% $arg))) (← `(pca% $a)) args
| `(pca% ( $a:pca )) => `(pca% $a)
| `(«pca» $a:pca) => `(whnfR% PAS.term (pca% $a))

open PAS
variable [A : PCA α]

@[simp] lemma abs_term {e : FreeMagma α 1} : term (abs e) = eval (abs e) .nil := rfl


/-!
## Function Composition
-/

@[aesop norm]
protected def id : α :=
  «pca» fun x => x

@[aesop norm]
protected def comp : α :=
  «pca» fun f g x => g (f x)

@[simp] lemma id_def : A.id ↓ := abs_def

@[simp] lemma id_eval {a : α} : ap A.id a = a := by
  apply ext (a ↓) <;> aesop (add norm PCA.id)

@[simp] lemma comp_def : A.comp ↓ := abs_def

@[simp] lemma comp_def_1 {v₁ : α} : ap PCA.comp v₁ ↓ ↔ v₁ ↓ := by aesop

@[simp] lemma comp_def_2 {v₁ v₂ : α} : ap (ap A.comp v₁) v₂ ↓ ↔ v₁ ↓ ∧ v₂ ↓ := by aesop
  -- aesop (add norm PCA.comp)

@[simp] lemma comp_eval {v₁ v₂ v₃ : α} : ap (ap (ap A.comp v₁) v₂) v₃ = ap v₂ (ap v₁ v₃) := by
  apply ext (v₁ ↓ ∧ v₂ ↓ ∧ v₃ ↓) <;> aesop

/-!
# Constant functions
-/

@[aesop norm]
protected def const : α :=
  «pca» fun x y => x

@[aesop norm]
protected def ignore : α :=
  «pca» fun x y => y

@[simp] lemma const_def : A.const ↓ := abs_def

@[simp] lemma ignore_def : A.ignore ↓ := abs_def

/-!
# Pairs
-/

@[aesop norm]
protected def pair : α :=
  «pca» fun x y p => p x y

@[aesop norm]
protected def fst : α :=
  «pca» fun p => p A.const

@[aesop norm]
protected def snd : α :=
  «pca» fun p => p A.ignore

/-- Notation for pairing in a PCA. -/
syntax "⟨ " pca,+ " ⟩ " : pca

macro_rules
| `(pca% ⟨ $a:pca, $args:pca,* ⟩) => do
   Array.foldlM (β := Term) (fun acc arg => `(FreeMagma.ap (FreeMagma.ap (.const PCA.pair) $acc) (pca% $arg))) (← `(pca% $a)) args.getElems

@[simp] lemma fst_def : A.fst ↓ := abs_def

@[simp] lemma snd_def : A.snd ↓ := abs_def

@[simp] lemma pair_def : A.pair ↓ := abs_def

@[simp] lemma pair_def_1 {v₁ : α} : ap A.pair v₁ ↓ ↔ v₁ ↓ := by
  aesop (add norm PCA.pair)

@[simp] lemma pair_def_2 {v₁ v₂ : α} : («pca» ⟨ v₁ , v₂ ⟩) ↓ ↔ v₁ ↓ ∧ v₂ ↓ := by
  aesop

@[simp] lemma fst_pair_eval {v₁ v₂ : α} (v₂_def : v₂ ↓) : («pca» A.fst ⟨ v₁ , v₂ ⟩) = v₁ := by
  apply ext (v₁ ↓ ∧ v₂ ↓) <;> aesop

@[simp] lemma snd_pair_eval {v₁ v₂ : α} (v₁_def : v₁ ↓) : («pca» A.snd ⟨ v₁ , v₂ ⟩) = v₂ := by
  apply ext (v₁ ↓ ∧ v₂ ↓) <;> aesop

@[aesop norm]
protected def curry : α :=
  «pca» fun f x y => f ⟨ x , y ⟩

@[aesop norm]
protected def uncurry : α :=
  «pca» fun f xy => f (A.fst xy) (A.snd xy)

@[simp] lemma curry_def : A.curry ↓ := abs_def

@[simp] lemma curry_def_1 {f : α} : ap A.curry f ↓ ↔ f ↓ := by
  aesop

@[simp] lemma curry_def_2 {f x : α} : («pca» A.curry f x) ↓ ↔ f ↓ ∧ x ↓ := by
  aesop

@[simp] lemma curry_eval {f x y : α} : ap (ap (ap A.curry f) x) y = ap f (ap (ap A.pair x) y) := by
  apply ext (f ↓ ∧ x ↓ ∧ y ↓) <;> aesop

@[simp] lemma uncurry_def : A.uncurry ↓ := abs_def

@[simp] lemma uncurry_def_1 {f : α} : ap A.uncurry f ↓ ↔ f ↓ := by
  aesop

@[simp] lemma uncurry_eval {f x y : α} : ap (ap A.uncurry f) (ap (ap A.pair x) y) = ap (ap f x) y := by
  apply ext (f ↓ ∧ x ↓ ∧ y ↓) <;> aesop


/-!
# Booleans
-/

@[aesop norm]
protected def true : α := A.const

@[aesop norm]
protected def false : α := A.ignore

@[simp] lemma true_def : A.true ↓ := const_def

@[simp] lemma false_def : A.false ↓ := ignore_def

/-!
# Sums
-/

@[aesop norm]
protected def inl : α :=
  «pca» fun x => ⟨ A.true, x ⟩

@[aesop norm]
protected def inr : α :=
  «pca» fun x => ⟨ A.false, x ⟩

@[aesop norm] protected def elim : α :=
  «pca» fun l r x => (A.fst x) l r (A.snd x)

@[simp] lemma inl_def : A.inl ↓ := abs_def

@[simp] lemma inl_def_1 (v : α) : ap A.inl v ↓ ↔ v ↓ := by
  aesop (add norm PCA.inl, norm PCA.pair, norm PCA.true)

@[simp] lemma inr_def : A.inr ↓ := abs_def

@[simp] lemma inr_def_1 (v : α) : ap A.inr v ↓ ↔ v ↓ := by
  aesop (add norm PCA.inr, norm PCA.pair, norm PCA.false)

@[simp] lemma elim_def : A.elim ↓ := abs_def

@[simp] lemma elim_def_1 {l : α} : («pca» A.elim l) ↓ ↔ l ↓ := by
  aesop

@[simp] lemma elim_def_2 {l r : α} : («pca» A.elim l r) ↓ ↔ l ↓ ∧ r ↓ := by
  aesop

@[simp] lemma elim_inl_eval {l r v : α} (r_def : r ↓) : («pca» A.elim l r (A.inl v)) = («pca» l v) := by
  apply ext (l ↓ ∧ r ↓ ∧ v ↓) <;> aesop

@[simp] lemma elim_inr_eval {l r v : α} (l_def : l ↓) : («pca» A.elim l r (A.inr v)) = («pca» r v) := by
  apply ext (l ↓ ∧ r ↓ ∧ v ↓) <;> aesop

end PCA
