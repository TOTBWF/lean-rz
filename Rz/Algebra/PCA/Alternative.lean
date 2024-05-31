import Mathlib.Init.Order.Defs
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

instance {n : Nat} [PAS α] : FreeMagma.MagmaSyntax (Val α) n α where
  quote v := .const v

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

syntax "⟦" magma:min "⟧" term : term

macro_rules
| `(⟦ $e:magma ⟧ $ρ:term) => `(PAS.eval («magma» $e) $ρ)

class PCA (α : Type u) extends PAS α where
  abs : {n : Nat} → FreeMagma α (n + 1) → FreeMagma α n
  abs_def : {n : Nat} → {e : FreeMagma α (n + 1)} → {ρ : Vec (Val α) n} → PAS.eval (abs e) ρ ↓
  abs_eval : {n : Nat} → {e : FreeMagma α (n + 1)} → {a : α} → {ρ : Vec (Val α) n} → (a_def : a ↓) → ap (PAS.eval (abs e) ρ) a = PAS.eval e (.cons ⟨ a , a_def ⟩ ρ)

attribute [simp] PCA.abs_def
attribute [simp] PCA.abs_eval

namespace PCA

open PAS
variable [A : PCA α]

@[simp] lemma abs_term {e : FreeMagma α 1} : term (abs e) = eval (abs e) .nil := rfl


/-!
## Function Composition
-/

protected def id : α :=
  term (abs (.var 0))

protected def comp : α :=
  term (abs (abs (abs («magma» `(1) (`(2) `(0))))))

@[simp] lemma id_def : A.id ↓ := abs_def

@[simp] lemma id_eval {a : α} : ap A.id a = a := by
  apply ext (a ↓) <;> aesop (add norm PCA.id)

@[simp] lemma comp_def : A.comp ↓ := abs_def

@[simp] lemma comp_def_1 {v₁ : α} : ap PCA.comp v₁ ↓ ↔ v₁ ↓ := by
  aesop (add norm PCA.comp)

@[simp] lemma comp_def_2 {v₁ v₂ : α} : ap (ap A.comp v₁) v₂ ↓ ↔ v₁ ↓ ∧ v₂ ↓ := by
  aesop (add norm PCA.comp)

@[simp] lemma comp_eval {v₁ v₂ v₃ : α} : ap (ap (ap A.comp v₁) v₂) v₃ = ap v₂ (ap v₁ v₃) := by
  apply ext (v₁ ↓ ∧ v₂ ↓ ∧ v₃ ↓) <;> aesop (add norm PCA.comp)

/-!
# Constant functions
-/

protected def const : α :=
  term (abs (abs (.var 1)))

protected def ignore : α :=
  term (abs (abs (.var 0)))

/-!
# Pairs
-/

protected def pair : α :=
  term (abs (abs (abs («magma» `(0) `(2) `(1)))))

protected def fst : α :=
  term (abs («magma» `(0) A.const))

protected def snd : α :=
  term (abs («magma» `(0) A.ignore))

@[simp] lemma fst_def : A.fst ↓ := abs_def

@[simp] lemma snd_def : A.snd ↓ := abs_def

@[simp] lemma pair_def : A.pair ↓ := abs_def

@[simp] lemma pair_def_1 {v₁ : α} : ap A.pair v₁ ↓ ↔ v₁ ↓ := by
  aesop (add norm PCA.pair)

@[simp] lemma pair_def_2 {v₁ v₂ : α} : ap (ap A.pair v₁) v₂ ↓ ↔ v₁ ↓ ∧ v₂ ↓ := by
  aesop (add norm PCA.pair)

@[simp] lemma fst_pair_eval {v₁ v₂ : α} (v₂_def : v₂ ↓) : ap A.fst (ap (ap A.pair v₁) v₂) = v₁ := by
  apply ext (v₁ ↓ ∧ v₂ ↓) <;> aesop (add norm PCA.pair, norm PCA.fst, norm PCA.const)

@[simp] lemma snd_pair_eval {v₁ v₂ : α} (v₁_def : v₁ ↓) : ap A.snd (ap (ap A.pair v₁) v₂) = v₂ := by
  apply ext (v₁ ↓ ∧ v₂ ↓) <;> aesop (add norm PCA.pair, norm PCA.snd, norm PCA.ignore)
end PCA
