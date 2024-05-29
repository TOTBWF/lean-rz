import Mathlib.Init.Order.Defs
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Use

import Rz.Syntax.Magma
-- import Rz.Data.Bwd

universe u v w
variable {α β : Type u}

/-!
## Partial Applicative Systems
-/

class PAS (α : Type u) where
  /-- `a₁ · a₂ ↝ a₃` denotes that applying a₁ to a₂ reduces to a₃. -/
  Ap : α → α → α → Prop
    /-- The application relation is functional. -/
  ap_functional : {a₁ a₂ v₁ v₂ : α} → Ap a₁ a₂ v₁ → Ap a₁ a₂ v₂ → v₁ = v₂

/-- Extend the small-step relation to a big-step relation on `FreeMagma α`. -/
def PAS.Eval [PAS α] : (ρ : List α) → FreeMagma α → α → Prop
  | ρ, .var i, v => ∃ h, ρ.get ⟨i, h⟩ = v
  | _, .const a, v => a = v
  | ρ, .ap e₁ e₂, v => ∃ v₁ v₂, Eval ρ e₁ v₁ ∧ Eval ρ e₂ v₂ ∧ PAS.Ap v₁ v₂ v

syntax term " ⊢ " magma " ⇓ " term:40 : term
macro_rules
| `($ρ:term ⊢ $e:magma ⇓ $a:term) => `(PAS.Eval $ρ («magma» $e) $a)

namespace PAS
/-- `Undefined ρ e` denotes that an expression `e` diverges when evaluated in environment `ρ`. -/
def Undefined [PAS α] (ρ : List α) (e : FreeMagma α) : Prop := (a : α) → ¬ (ρ ⊢ e ⇓ a)
/-- `Defined ρ e` denotes that an expression `e` diverges when evaluated in environment `ρ`. -/
def Defined [PAS α] (ρ : List α) (e : FreeMagma α) : Prop := ∃ (a : α), ρ ⊢ e ⇓ a
/-- `Refines ρ e₁ e₂` denotes that an expression `e₂` is least as defined as `e₁`. -/
def Refines [PAS α] (ρ₁ : List α) (e₁ : FreeMagma α) (ρ₂ : List α) (e₂ : FreeMagma α) : Prop := {a : α} → ρ₁ ⊢ e₁ ⇓ a → ρ₂ ⊢ e₂ ⇓ a

open Classical in

noncomputable def ap [PAS α] : Option α → Option α → Option α
  | some a, some b =>
    if h : ∃ c, PAS.Ap a b c then some (Classical.choose h) else none
  | _, _ => none

/-- Extend the small-step relation to a big-step function on `FreeMagma α`. -/
@[simp] noncomputable def eval [PAS α] : (ρ : List α) → FreeMagma α → Option α
  | ρ, .var i => ρ.get? i
  | _, .const a => some a
  | ρ, .ap e₁ e₂ => ap (eval ρ e₁) (eval ρ e₂)

end PAS

@[inherit_doc PAS.Undefined]
macro ρ:term " ⊢ " e:magma " ↑" : term => `(PAS.Undefined $ρ («magma» $e))
@[inherit_doc PAS.Defined]
macro ρ:term " ⊢ " e:magma " ↓" : term => `(PAS.Defined $ρ («magma» $e))
@[inherit_doc PAS.Refines]
macro ρ₁:term " ⊢ " e₁:magma " ≤ " ρ₂:term:max " ⊢ " e₂:withPosition(magma) : term =>
  `(PAS.Refines $ρ₁ («magma» $e₁) $ρ₂ («magma» $e₂))

@[inherit_doc PAS.eval]
macro "eval(" ρ:term:max " ⊢ " e:magma ")" : term => `(PAS.eval $ρ («magma» $e))

namespace PAS

theorem ap_eq_some [PAS α] {oa ob : Option α} {c : α} :
    ap oa ob = some c ↔ ∃ a b, oa = some a ∧ ob = some b ∧ Ap a b c := by
  cases oa <;> cases ob <;> simp [ap]
  split
  · next h =>
    constructor <;> intro h2
    · cases h2; exact Classical.choose_spec h
    · rw [ap_functional (Classical.choose_spec h) h2]
  · simp; exact mt (Exists.intro _) ‹_›

@[simp] theorem ap_none_left [PAS α] (a : Option α) : ap none a = none := rfl
@[simp] theorem ap_none_right [PAS α] (a : Option α) : ap a none = none := by cases a <;> rfl

theorem eval_eq_some [PAS α] {ρ : List α} {e : FreeMagma α} {v : α} :
    eval(ρ ⊢ e) = some v ↔ ρ ⊢ e ⇓ v := by
  induction e generalizing v with simp [Eval]
  | var i => simp [List.get?_eq_some]
  | ap e₁ e₂ ih₁ ih₂ => simp [ap_eq_some, ih₁, ih₂]

theorem eval_isSome [PAS α] {ρ : List α} {e : FreeMagma α} : (eval ρ e).isSome ↔ ρ ⊢ e ↓ := by
  simp [Option.isSome_iff_exists, eval_eq_some, Defined]

/-!
### Order-Theoretic Properties of Refinement
-/

/-- The refinement relation extends to a preorder on expressions. -/
instance Refine [PAS α] {ρ : List α} : Preorder (FreeMagma α) where
  le e₁ e₂ := PAS.Refines ρ e₁ ρ e₂
  le_refl e v v_eval := v_eval
  le_trans e₁ e₂ e₃ p q v v_eval := q (p v_eval)
variable [PAS α]

@[simp] theorem const_eval
  {ρ : List α}
  {a v : α}
  : ρ ⊢ a ⇓ v ↔ a = v := by
  simp [PAS.Eval]

/-- Application is monotonic with respect to refinement. -/
theorem ap_le_ap
  {ρ : List α}
  {e₁ e₂ e₁' e₂' : FreeMagma α}
  (le_left : ρ ⊢ e₁ ≤ ρ ⊢ e₁') (le_right : ρ ⊢ e₂ ≤ ρ ⊢ e₂')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁' e₂' := by
    intros v v_eval
    simp [Eval] at *
    have ⟨ v₁ , v₁_eval , v₂ , v₂_eval, v_ap ⟩ := v_eval
    exact ⟨ v₁ , le_left v₁_eval, v₂ , le_right v₂_eval, v_ap ⟩

@[inherit_doc ap_le_ap]
theorem ap_le_ap_right
  {ρ : List α}
  {e₁ e₂ e₂' : FreeMagma α}
  (le_right : ρ ⊢ e₂ ≤ ρ ⊢ e₂')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁ e₂' := ap_le_ap (Refine.le_refl e₁) le_right

@[inherit_doc ap_le_ap]
theorem ap_le_ap_left
  {ρ : List α}
  {e₁ e₂ e₁' : FreeMagma α}
  (le_left : ρ ⊢ e₁ ≤ ρ ⊢ e₁')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁' e₂ := ap_le_ap le_left (Refine.le_refl e₂)

theorem ap_eval
  {ρ : List α}
  {e₁ e₂ : FreeMagma α} {v : α}
  : ρ ⊢ e₁ e₂ ⇓ v ↔ ∃ v₁ v₂ : α, ρ ⊢ e₁ ⇓ v₁ ∧  ρ ⊢ e₂ ⇓ v₂ ∧ PAS.Ap v₁ v₂ v := by simp [PAS.Eval]

theorem ap_eval_const_left
    {ρ : List α} {v₁ v : α} {e₂ : FreeMagma α}
    : ρ ⊢ v₁ e₂ ⇓ v ↔ ∃ v₂ : α, ρ ⊢ e₂ ⇓ v₂ ∧ PAS.Ap v₁ v₂ v := by
  simp [PAS.Eval]

theorem ap_congl
  {ρ : List α}
  {e₁ e₂ : FreeMagma α} {v : α}
  : ρ ⊢ e₁ e₂ ⇓ v ↔ ∃ v₁ : α, ρ ⊢ e₁ ⇓ v₁ ∧ ρ ⊢ v₁ e₂ ⇓ v := by
  simp [PAS.Eval]

theorem ap_congr
  {ρ : List α}
  {e₁ e₂ : FreeMagma α} {v : α}
  : ρ ⊢ e₁ e₂ ⇓ v ↔ ∃ v₂ : α, ρ ⊢ e₂ ⇓ v₂ ∧ ρ ⊢ e₁ v₂ ⇓ v := by
  simp [PAS.Eval]
  apply Iff.intro
  · rintro ⟨ v₁ , v₁_eval , v₂ , v₂_eval , v_ap ⟩
    exact ⟨ v₂ , v₂_eval , v₁ , v₁_eval , v_ap ⟩
  · rintro ⟨ v₂ , v₂_eval , v₁ , v₁_eval , v_ap ⟩
    exact ⟨ v₁ , v₁_eval , v₂ , v₂_eval , v_ap ⟩

/-!
### Evaluation Lemmas
-/

/-- Evaluation is a functional relation. -/
theorem eval_functional
    {ρ : List α}
    {e : FreeMagma α} {a a' : α}
    (h1 : ρ ⊢ e ⇓ a) (h2 : ρ ⊢ e ⇓ a')
    : a = a' := by
  induction e generalizing a a' with simp [Eval] at h1 h2
  | var => obtain ⟨_, rfl⟩ := h1; obtain ⟨_, rfl⟩ := h2; rfl
  | const => exact h1 ▸ h2
  | ap _ _ ih1 ih2 =>
    obtain ⟨_, ev11, _, ev12, h1⟩ := h1
    obtain ⟨_, ev21, _, ev22, h2⟩ := h2
    cases ih1 ev11 ev21
    cases ih2 ev12 ev22
    exact ap_functional h1 h2


end PAS

/-!
# Partial Combinatory Algebras
-/

/-- Partial Combinatory Algebras. -/
class PCA (α : Type u) extends PAS α where
  /-- PCAs are equipped with a bracket abstraction operator. -/
  abs : FreeMagma α → FreeMagma α
  /-- Bracket abstraction yields a value. -/
  abs_defined : (ρ : List α) → (e : FreeMagma α) → ρ ⊢ $(abs e) ↓
  /-- Bracket abstraction has a β-law. -/
  abs_eval : {ρ : List α} → {e₁ e₂ : FreeMagma α} → {v₁ : α} →
    ρ ⊢ $(abs e₁) e₂ ⇓ v₁ ↔ (∃ v₂, ρ ⊢ e₂ ⇓ v₂ ∧ (v₂ :: ρ) ⊢ e₁ ⇓ v₁)

namespace PCA

variable [PCA α]
open PAS

@[simp] theorem abs_eval' {ρ : List α} {e : FreeMagma α} {v : α} :
    ap (eval ρ (abs e)) v = eval (v :: ρ) e := by
  ext v'; simp [eval_eq_some]
  rw [← eval.eq_2, ← eval.eq_3, eval_eq_some, abs_eval]
  simp

@[simp] def absn (e : FreeMagma α) : Nat → FreeMagma α
  | 0 => e
  | n+1 => (absn (abs e) n)

-- theorem absn_le
--   {ρ : List α} {e : FreeMagma α} {as : List (FreeMagma α)} {v : α} {vargs : List α}
--   (e_eval : ρ ⊢ $(absn e as.length) $[as]* ⇓ v)
--   (as_eval : as.Forall₂ (fun a v => ρ ⊢ a ⇓ v) vargs)
--   : (vargs ++ ρ) ⊢ e ⇓ v := by
--     induction as_eval generalizing e v with
--     | nil =>
--       simp [absn] at *
--       exact e_eval
--     | @cons a varg as vargs a_eval _ IH =>
--       simp [absn] at *
--       have ⟨ vbody , vbody_eval , v_ap ⟩ := PAS.ap_congl.1 e_eval
--       have' ih_eval := IH vbody_eval
--       have outer_eval : (vargs ++ ρ) ⊢ $(abs e) varg ⇓ v := by
--         rw [PAS.ap_congl]
--         use vbody, ih_eval
--         have ⟨v', h1, h2⟩ := PAS.ap_congr.1 v_ap
--         rwa [← PAS.eval_functional a_eval h1] at h2
--       simpa [abs_eval] using outer_eval

theorem absn_eval
    {ρ : List α} {f : FreeMagma α} {es : List (FreeMagma α)} {v : α}
    : ρ ⊢ $(absn f es.length) $[es]* ⇓ v ↔
      ∃ vargs, es.Forall₂ (fun a v => ρ ⊢ a ⇓ v) vargs ∧ (vargs ++ ρ) ⊢ f ⇓ v := by
  constructor
  · intro e_eval
    induction es generalizing f v with simp at *
    | nil => exact ⟨[], .nil, e_eval⟩
    | cons e es IH =>
      have ⟨vf, ve, vf_eval, ve_eval, vf_ap⟩ := PAS.ap_eval.1 e_eval
      have ⟨vargs, as_eval, vbody_eval⟩ := IH vf_eval
      refine ⟨ve::vargs, .cons ve_eval as_eval, ?_⟩
      simpa using abs_eval.1 <|
        (PAS.ap_eval (e₂ := .const ve)).2 ⟨_, ve, vbody_eval, by simp, vf_ap⟩
  · intro ⟨vargs, es_eval, f_eval⟩
    induction es_eval generalizing f v with
    | nil => simpa using f_eval
    | @cons e varg es vargs e_eval _ IH =>
      have ⟨fv, varg', absf_eval, h2, ap_eval⟩ :=
        (abs_eval (e₂ := .const varg)).2 ⟨_, by simp, f_eval⟩
      simp at h2; subst h2
      have := IH absf_eval
      exact ⟨_, _, this, e_eval, ap_eval⟩

protected def id : FreeMagma α :=
  abs (.var 0)

protected theorem id_le (ρ : List α) (e : FreeMagma α) : ρ ⊢ PCA.id e ≤ ρ ⊢ e := by
  intro v v_eval
  rewrite [PCA.id, PCA.abs_eval] at v_eval
  simp [PAS.Eval] at v_eval
  exact v_eval

protected theorem le_id (ρ : List α) (e : FreeMagma α) : ρ ⊢ e ≤ ρ ⊢ PCA.id e := by
  intro v v_eval
  simp [PCA.id, PCA.abs_eval]
  simp [PAS.Eval]
  exact v_eval

-- @[simp] protected theorem i_eval {ρ : List α} {e : FreeMagma α} {v : α} : ρ ⊢ PCA.id e ⇓ v ↔ ρ ⊢ e ⇓ v :=
--   ⟨ PCA.id_le _ _ , PCA.le_id _ _ ⟩

@[simp] protected theorem i_eval' {ρ : List α} {e : Option α} :
    ap eval(ρ ⊢ PCA.id) e = e := by
  simp [PCA.id]; cases e <;> simp

@[simp] protected theorem i_eval {ρ : List α} {e : FreeMagma α} {v : α} :
    ρ ⊢ PCA.id e ⇓ v ↔ ρ ⊢ e ⇓ v := by
  simp [← eval_eq_some]

-- \f g x.
protected def comp : FreeMagma α :=
  abs (abs (abs («magma» `(1) (`(2) `(0)))))

@[simp] protected theorem comp_eval'
    {ρ : List α} {e₁ e₂ e₃ : Option α} :
    ap (ap (ap eval(ρ ⊢ PCA.comp) e₁) e₂) e₃ = ap e₂ (ap e₁ e₃) := by
  cases e₁ <;> [simp; skip]
  cases e₂ <;> [simp; skip]
  cases e₃ <;> [simp; skip]
  simp [PCA.comp]

@[simp] protected theorem comp_eval
    {ρ : List α} {e₁ e₂ e₃ : FreeMagma α} {v : α} :
    ρ ⊢ PCA.comp e₁ e₂ e₃ ⇓ v ↔ ρ ⊢ e₂ (e₁ e₃) ⇓ v := by
  simp [← eval_eq_some]

theorem forall₂_cons_left {R : α → β → Prop} {l₁ : List α} {l₂ : List β} {a : α} :
    List.Forall₂ R (a :: l₁)  l₂ ↔ ∃ b l₂', R a b ∧ l₂ = b :: l₂' ∧ l₁.Forall₂ R l₂' :=
  match l₂ with
  | .nil => by simp; nofun
  | .cons a b =>
    ⟨fun | .cons h1 h2 => ⟨_, _, h1, rfl, h2⟩, fun ⟨_, _, h1, rfl, h2⟩ => .cons h1 h2⟩

theorem forall₂_nil_left {R : α → β → Prop} {l₂ : List β} :
    List.Forall₂ R [] l₂ ↔ l₂ = [] := by
  cases l₂ <;> simp; nofun

-- @[simp] protected theorem comp_eval
--     {ρ : List α} {e₁ e₂ e₃ : FreeMagma α} {v : α}
--     : ρ ⊢ PCA.comp e₁ e₂ e₃ ⇓ v ↔ ρ ⊢ e₂ (e₁ e₃) ⇓ v := by
--   simp [PCA.comp]
--   refine absn_eval (es := [_, _, _]) |>.trans ?_
--   simp [forall₂_cons_left, forall₂_nil_left]
--   constructor
--   · rintro ⟨vargs, ⟨v₃, v₃_eval, _, rfl, v₂, v₂_eval, _, rfl, v₁, v₁_eval, rfl⟩, v_eval⟩
--     simp [PAS.Eval, List.get] at v_eval
--     obtain ⟨_, ⟨-, rfl⟩, v13, ⟨_, ⟨-, rfl⟩, v13_eval⟩, v23_eval⟩ := v_eval
--     exact ⟨_, _, v₂_eval, ⟨_, _, v₁_eval, v₃_eval, v13_eval⟩, v23_eval⟩
--   · rintro ⟨v₂, v13, v₂_eval, ⟨v₁, v₃, v₁_eval, v₃_eval, v13_eval⟩, v23_eval⟩
--     refine ⟨[_,_,_], ⟨_, v₃_eval, _, rfl, _, v₂_eval, _, rfl, _, v₁_eval, rfl⟩, ?ax⟩
--     simp [PAS.Eval, List.get]
--     exact ⟨_, ⟨by omega, rfl⟩, _, ⟨_, ⟨by omega, rfl⟩, v13_eval⟩, v23_eval⟩

  -- ⟨ PCA.comp_le (v := v) , PCA.le_comp (v := v) ⟩
-- @[simp] protected def comp_eval {ρ : List α} {e₁ e₂ e₃ : FreeMagma α} {v : α} : ρ ⊢ PCA.comp e ⇓ v ↔ ρ ⊢ e ⇓ v := sorry

-- protected def le_comp (ρ : Bwd α) (e₁ e₂ e₃ : FreeMagma α) : ρ ⊢ e₂ (e₁ e₃) ≤ ρ ⊢ PCA.comp e₁ e₂ e₃ := by
--   apply PAS.ap_le_ap_var_right
--   sorry
  -- rintro v ⟨ v₂ , v₁₃ , v₂_eval , ⟨ v₁ , v₃ , v₁_eval , v₂_eval , v₁₃_ap ⟩ , v_ap ⟩
  -- suffices h : (ρ :# v₃ :# v₂ :# v₁) ⊢ PCA.comp `(0) `(1) `(2) ⇓ v
  -- · sorry
  -- · sorry
  -- have
  -- apply PAS.ap_le_ap_left
  -- · apply PAS.ap_le_ap_left
  --   · unfold PCA.comp
  --     sorry
  --   · sorry
  -- · sorry
  -- rw [PAS.ap_congl]
  -- exists sorry
  -- rw [PAS.ap_congl]
  -- exists sorry
  -- rintro v ⟨ v₂ , v₁ , v₂_eval , ⟨ v₁ , v₃ , p ⟩ , v_ap ⟩
  -- rw [PCA.comp, PAS.ap_eval]
  -- exists sorry
  -- exists v
  -- rw [PAS.ap_eval]
  -- split_ands
  -- · exists sorry
  --   exists sorry
  --   rw [PCA.abs_eval]
  --   sorry
  -- · sorry
  -- · sorry
  -- exists sorry
  -- rw [PCA.abs_eval]
  -- exact ⟨ sorry , sorry , sorry ⟩

-- protected def comp_le (ρ : Bwd α) (e₁ e₂ e₃ : FreeMagma α) : ρ ⊢ PCA.comp e₁ e₂ e₃ ≤ ρ ⊢ e₂ (e₁ e₃) := by
--   intros v v_eval
--   rewrite [PCA.comp] at v_eval
--   sorry
--   -- have ⟨ v_comp , v_comp_eval ⟩ := abs_defined ρ (.ap e₂ (.ap e₁ (.var 0)))
--   -- have ⟨ v₂ , v₂_eval , v' , ⟨ v₁ , v₁_eval , v₃ , v₃_eval , v'_ap ⟩ , v_ap ⟩ := v_eval
--   -- have ⟨ v₁ , v₂ , v₁_eval , v_v₂_eq, v_ap ⟩ : ρ ⊢ $(abs (.var 0)) v ⇓ v :=
--   --   abs_eval ρ v (FreeMagma.var 0)  (by simp [PAS.Eval])
--   -- exact ⟨ v_comp , v_comp_eval , v₃, v₃_eval, sorry ⟩

end PCA
