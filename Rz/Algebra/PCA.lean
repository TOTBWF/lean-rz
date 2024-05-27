/-
# Partial Combinatory Algebras
-/
import Rz.Data.Bwd
import Rz.Syntax.Magma
import Rz.Syntax.Subst


universe u v w
variable {α β : Type u}

/-!
# Partial Applicative Structures
-/

/-- Notation typeclass for Eval. -/
class HasEval (α : Type u) where
  /-- Big-step evaluation relation. -/
  Eval : (ρ : Bwd α) → FreeMagma α → α → Prop

def HasEval.Undefined [HasEval α] (ρ : Bwd α) (e : FreeMagma α) : Prop := (a : α) → ¬ (HasEval.Eval ρ e a)
def HasEval.Defined [HasEval α] (ρ : Bwd α) (e : FreeMagma α) : Prop := ∃ (a : α), HasEval.Eval ρ e a
def HasEval.Refines [HasEval α] (ρ₁ ρ₂ : Bwd α) (e₁ e₂ : FreeMagma α) : Prop := (a : α) → HasEval.Eval ρ₂ e₂ a → HasEval.Eval ρ₁ e₁ a
def HasEval.Equiv [HasEval α] (ρ₁ ρ₂ : Bwd α) (e₁ e₂ : FreeMagma α) : Prop := HasEval.Refines ρ₂ ρ₁ e₂ e₁ ∧ HasEval.Refines ρ₁ ρ₂ e₁ e₂

syntax term " ⊢ " magma " ↑" : term
syntax term " ⊢ " magma " ↓" : term
syntax term " ⊢ " magma " ⇓ " term:40 : term
syntax term " ⊢ " magma " ≤ " term:max " ⊢ " withPosition(magma) : term
syntax term " ⊢ " magma " ≃ " term:max " ⊢ " withPosition(magma) : term

macro_rules
| `($ρ:term ⊢ $e:magma ↑) => `(HasEval.Undefined $ρ («magma» $e))
| `($ρ:term ⊢ $e:magma ↓) => `(HasEval.Defined $ρ («magma» $e))
| `($ρ:term ⊢ $e:magma ⇓ $a:term) => `(HasEval.Eval $ρ («magma» $e) $a)
| `($ρ₁:term ⊢ $e₁:magma ≤ $ρ₂:term ⊢ $e₂:magma) => `(HasEval.Refines $ρ₂ $ρ₁ («magma» $e₂) («magma» $e₁))
| `($ρ₁:term ⊢ $e₁:magma ≃ $ρ₂:term ⊢ $e₂:magma) => `(HasEval.Equiv $ρ₁ $ρ₂ («magma» $e₁) («magma» $e₂))

/-- Partial Applicative Structures. -/
class PAS (α : Type u) extends HasEval α where
  /-- The evaluation relation is functional. -/
  eval_functional : {ρ : Bwd α} → {e : FreeMagma α} → {a a' : α} → ρ ⊢ e ⇓ a → ρ ⊢ e ⇓ a' → a = a'
  /-- Looking up the 0th variable resolves to the final element of the environment. -/
  var_zero_eval : (ρ : Bwd α) → (a : α) → (ρ :# a) ⊢ `(0) ⇓ a
  /-- Resolving a successor variable requires us to look up in the tail of the environment. -/
  var_succ_eval_le : (ρ : Bwd α) → (a : α) → (n : Nat) → (ρ :# a) ⊢ `(n+1) ≤ ρ ⊢ `(n)
  var_succ_eval_ge : (ρ : Bwd α) → (a : α) → (n : Nat) → ρ ⊢ `(n) ≤ (ρ :# a) ⊢ `(n+1)
  /-- Resolving an out-of-bounds variable diverges. -/
  var_zero_diverge : (n : Nat) → (Bwd.nil : Bwd α) ⊢ `(n) ↑
  /-- Constants reduce to themselves. -/
  const_eval : (ρ : Bwd α) → (a : α) → ρ ⊢ a ⇓ a
  /-- Applications are evaluated by evaluating both sides.
      Note the change of environment; this corresponds to the fact that substitutions do not act on values. -/
  ap_eval_le : {ρ₁ ρ₂ : Bwd α} → {e₁ e₂ : FreeMagma α} → {a₁ a₂ : α} → ρ₁ ⊢ e₁ ⇓ a₁ → ρ₁ ⊢ e₂ ⇓ a₂ → ρ₁ ⊢ e₁ e₂ ≤ ρ₂ ⊢ a₁ a₂
  ap_eval_ge : {ρ₁ ρ₂ : Bwd α} → {e₁ e₂ : FreeMagma α} → {a₁ a₂ : α} → ρ₁ ⊢ e₁ ⇓ a₁ → ρ₁ ⊢ e₂ ⇓ a₂ → ρ₂ ⊢ a₁ a₂ ≤ ρ₁ ⊢ e₁ e₂
  /-- If an application is defined, then so is the left argument. -/
  ap_left_defined : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ e₂ ↓ → ρ ⊢ e₁ ↓
  /-- If an application is defined, then so is the right argument. -/
  ap_right_defined : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ e₂ ↓ → ρ ⊢ e₂ ↓

namespace PAS

/-!
## Variable Lemmas
-/

/-- Variant of `var_succ_eval` that uses `Nat.pred`. -/
theorem var_pred_eval_ne_zero_le
  [PAS α]
  (ρ : Bwd α) (a : α)
  (n : Nat) (h : n ≠ 0)
  : (ρ :# a) ⊢ `(n) ≤ ρ ⊢ `(n.pred) := by
  match n with
  | 0 => contradiction
  | n+1 => apply var_succ_eval_le

theorem var_pred_eval_ne_zero_ge
  [PAS α]
  (ρ : Bwd α) (a : α)
  (n : Nat) (h : n ≠ 0)
  : ρ ⊢ `(n.pred) ≤ (ρ :# a) ⊢ `(n) := by
  match n with
  | 0 => contradiction
  | n+1 => apply var_succ_eval_ge


/-- Variable lookups evaluate to `Bwd.get` if they are in bounds. -/
theorem var_get_eval
  [PAS α]
  (ρ : Bwd α) (x : Fin ρ.length)
  : ρ ⊢ `(x) ⇓ ρ.get x := by
  match ρ with
  | .nil =>
    have : x.val < 0 := x.is_lt
    contradiction
  | .snoc ρ a =>
    if h : x = 0 then
      simp [h]
      apply PAS.var_zero_eval
    else
      apply (PAS.var_pred_eval_ne_zero_ge ρ a x (Fin.val_ne_of_ne h))
      rw [Bwd.get_snoc_pred_ne_zero ρ a x h]
      apply PAS.var_get_eval (x := x.pred h)

theorem var_of_converge [PAS α] (ρ : Bwd α) (x : Nat) : ρ ⊢ `(x) ↓ → x < ρ.length := by
  rintro ⟨v, H⟩
  induction ρ generalizing x with
  | nil => cases var_zero_diverge _ _ H
  | snoc ρ a IH =>
    match x with
    | 0 => simp
    | x + 1 => exact Nat.succ_lt_succ <| IH _ <| var_succ_eval_le _ _ _ _ H

/-!
## Evaluation Lemmas
-/

/-- If a value evaluates to another value, then the two values are equal. -/
theorem const_eval_eq
  [PAS α]
  (ρ : Bwd α)
  (a a' : α) (a_eval : ρ ⊢ a ⇓ a')
  : a = a' :=
    eval_functional (const_eval ρ a) a_eval


/-- Evaluation of constants is invariant under environments. -/
theorem const_eval_stable
  [PAS α]
  (ρ₁ ρ₂ : Bwd α)
  (a a' : α) (a_eval : ρ₁ ⊢ a ⇓ a')
  : ρ₂ ⊢ a ⇓ a' := by
    rw [const_eval_eq ρ₁ a a' a_eval]
    apply const_eval

/-- Evaluation of closed terms is invariant under environments. -/
theorem closed_eval_stable
  [PAS α]
  (ρ₁ ρ₂ : Bwd α)
  (e : FreeMagma α) (a : α)
  (closed : e.fv = 0)
  (a_eval : ρ₁ ⊢ e ⇓ a)
  : ρ₂ ⊢ e ⇓ a := by
    match e with
    | .var _ => contradiction
    | .const b =>
       apply const_eval_stable
       exact a_eval
    | .ap e₁ e₂ =>
      have ⟨ a₁ , a₁_eval_ρ₁ ⟩ := ap_left_defined ⟨ a , a_eval ⟩
      have ⟨ a₂ , a₂_eval_ρ₁ ⟩ := ap_right_defined ⟨ a , a_eval ⟩
      have ⟨ e₁_closed , e₂_closed ⟩ := FreeMagma.ap_closed_closed closed
      have a₁_eval_ρ₂ : ρ₂ ⊢ e₁ ⇓ a₁ := by
        apply closed_eval_stable
        · exact e₁_closed
        · exact a₁_eval_ρ₁
      have a₂_eval_ρ₂ : ρ₂ ⊢ e₂ ⇓ a₂ := by
        apply closed_eval_stable
        · exact e₂_closed
        · exact a₂_eval_ρ₁
      apply ap_eval_ge a₁_eval_ρ₂ a₂_eval_ρ₂
      apply ap_eval_le (ρ₂ := ρ₂) a₁_eval_ρ₁ a₂_eval_ρ₁
      · exact a_eval

/-!
## Definedness Lemmas
-/

/-- Constants are always defined. -/
theorem const_defined [PAS α] (ρ : Bwd α) (a : α) : ρ ⊢ a ↓ :=
  ⟨ a , const_eval ρ a ⟩

/-- An application is defined when both sides evalute to a value, and the application of those values is defined. -/
theorem ap_defined
  [PAS α]
  {ρ : Bwd α} {e₁ e₂ : FreeMagma α} {a₁ a₂ : α}
  (e₁_def : ρ ⊢ e₁ ⇓ a₁) (e₂_def : ρ ⊢ e₂ ⇓ a₂)
  (v_def : ρ ⊢ a₁ a₂ ↓)
  : ρ ⊢ e₁ e₂ ↓ :=
    let ⟨ w , h ⟩ := v_def
    ⟨ w , ap_eval_ge e₁_def e₂_def w h ⟩

def refine_refl
  [PAS α]
  {ρ : Bwd α} {e : FreeMagma α}
  : ρ ⊢ e ≤ ρ ⊢ e := by
  intros _ v_eval
  exact v_eval

def ap_refine
  [PAS α]
  {ρ : Bwd α} {e₁ e₂ e₁' e₂' : FreeMagma α}
  (rl : ρ ⊢ e₁ ≤ ρ ⊢ e₁')
  (rr : ρ ⊢ e₂ ≤ ρ ⊢ e₂')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁' e₂' := by
  intros v v_eval
  have ⟨ v₁ , v₁_eval ⟩ := ap_left_defined ⟨ v , v_eval ⟩
  have ⟨ v₂ , v₂_eval ⟩ := ap_right_defined ⟨ v , v_eval ⟩
  apply ap_eval_ge
  · exact rl v₁ v₁_eval
  · exact rr v₂ v₂_eval
  · apply ap_eval_le (ρ₂ := ρ)
    · exact v₁_eval
    · exact v₂_eval
    · exact v_eval

def ap_refine_left
  [PAS α]
  {ρ : Bwd α} {e₁ e₂ e₁' : FreeMagma α}
  (h : ρ ⊢ e₁ ≤ ρ ⊢ e₁')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁' e₂ :=
  ap_refine h refine_refl

def ap_refine_right
  [PAS α]
  {ρ : Bwd α} {e₁ e₂ e₂' : FreeMagma α}
  (h : ρ ⊢ e₂ ≤ ρ ⊢ e₂')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁ e₂' :=
  ap_refine refine_refl h

def ap_congl
  [PAS α]
  {ρ : Bwd α} {e₁ e₂ : FreeMagma α} {v₁ : α}
  (e₁_eval : ρ ⊢ e₁ ⇓ v₁)
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ v₁ e₂ := by
  apply ap_refine_left
  intros v v_eval
  have : v = v₁ := eval_functional v_eval e₁_eval
  rw [this]
  apply const_eval

def ap_congr
  [PAS α]
  {ρ : Bwd α} {e₁ e₂ : FreeMagma α} {v₂ : α}
  (e₂_eval : ρ ⊢ e₂ ⇓ v₂)
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁ v₂ := by
  apply ap_refine_right
  intros v v_eval
  have : v = v₂ := eval_functional v_eval e₂_eval
  rw [this]
  apply const_eval


end PAS

/-- Partial Combinatory Algebras. -/
class PCA (α : Type u) extends PAS α where
  /-- PCAs are equipped with a bracket abstraction operator. -/
  abs : FreeMagma α → FreeMagma α
  /-- Bracket abstraction yields a value. -/
  abs_defined : (ρ : Bwd α) → (e : FreeMagma α) → ρ ⊢ $(abs e) ↓
  /-- Bracket abstraction has a β-law. -/
  abs_eval_le : (ρ : Bwd α) → (a : α) → (e : FreeMagma α) → ρ ⊢ $(abs e) a ≤ (ρ :# a) ⊢ e
  abs_eval_ge : (ρ : Bwd α) → (a : α) → (e : FreeMagma α) → (ρ :# a) ⊢ e ≤ ρ ⊢ $(abs e) a

namespace PCA

protected def i [PCA α] : FreeMagma α :=
  abs (.var 0)

protected def i_eval_le [PCA α] (ρ : Bwd α) (e : FreeMagma α) : ρ ⊢ PCA.i e ≤ ρ ⊢ e := by
  intros v v_eval
  have ⟨ v' , v'_eval ⟩ := PAS.ap_right_defined ⟨ v , v_eval ⟩
  have : ρ ⊢ PCA.i v' ⇓ v := PAS.ap_congr v'_eval _ v_eval
  have l : (ρ :# v') ⊢ `(0) ⇓ v := abs_eval_le ρ v' (.var 0) v this
  have r : (ρ :# v') ⊢ `(0) ⇓ v' := by
   apply PAS.var_zero_eval
  have : v = v' := PAS.eval_functional l r
  rwa [this]

protected def i_eval_ge [PCA α] (ρ : Bwd α) (e : FreeMagma α) : ρ ⊢ e ≤ ρ ⊢ PCA.i e := by
  intros v v_eval
  have : ρ ⊢ PCA.i v ⇓ v := by
    apply abs_eval_ge ρ v (.var 0)
    apply PAS.var_zero_eval
  exact (PAS.ap_congr_inv this v_eval)

protected def i_eval_eq
  [PCA α] {ρ : Bwd α} {v v' : α}
  (v_eval : ρ ⊢ PCA.i v ⇓ v')
  : v = v' := by
    apply PAS.eval_functional (ρ := ρ)
    · apply PCA.i_eval_ge
      · apply PAS.const_eval
    · exact v_eval

protected def c [PCA α] (e₁ e₂ : FreeMagma α) : FreeMagma α :=
  abs («magma» e₂ (e₁ `(0)))

-- protected def c_eval_le
--   [PCA α]
--   {ρ : Bwd α}
--   {e₁ e₂ : FreeMagma α} {v₁ v₂ : α}
--   (e₁_eval : ρ ⊢ e₁ ⇓ v₁) (e₂)

protected def true [PCA α] : FreeMagma α :=
  (abs (abs (.var 1)))

protected def false [PCA α] : FreeMagma α :=
  (abs (abs (.var 0)))

protected def ite [PCA α] : FreeMagma α :=
  (abs (abs (abs («magma» `(2) `(1) `(0)))))

end PCA

/-!
# SKI forms a basis for PCAs (and v.v.)
-/

/-- Partial Applicative Structures with S, K, and I combinators. -/
class SKI (α : Type u) extends PAS α where
  s : α
  k : α
  i : α
  s_defined_2 : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → ρ ⊢ e₁ ↓ → ρ ⊢ e₂ ↓ → ρ ⊢ s e₁ e₂ ↓
  k_defined : {ρ : Bwd α} → {e : FreeMagma α} → ρ ⊢ e ↓ → ρ ⊢ k e ↓
  s_eval_le : (ρ : Bwd α) → (e₁ e₂ e₃ : FreeMagma α) → ρ ⊢ s e₁ e₂ e₃ ≤ ρ ⊢ (e₁ e₃) (e₂ e₃)
  s_eval_ge : (ρ : Bwd α) → (e₁ e₂ e₃ : FreeMagma α) → ρ ⊢ (e₁ e₃) (e₂ e₃) ≤ ρ ⊢ s e₁ e₂ e₃
  k_eval_le : (ρ : Bwd α) → (e₁ e₂ : FreeMagma α) → ρ ⊢ e₂ ↓ → ρ ⊢ k e₁ e₂ ≤ ρ ⊢ e₁
  k_eval_ge : (ρ : Bwd α) → (e₁ e₂ : FreeMagma α) → ρ ⊢ e₂ ↓ → ρ ⊢ e₁ ≤ ρ ⊢ k e₁ e₂
  i_eval_le : (ρ : Bwd α) → (e : FreeMagma α) → ρ ⊢ i e ≤ ρ ⊢ e
  i_eval_ge : (ρ : Bwd α) → (e : FreeMagma α) → ρ ⊢ e ≤ ρ ⊢ i e

namespace SKI

open SKI

theorem s_defined_1
  [A : SKI α]
  {ρ : Bwd α} {e : FreeMagma α}
  (e_defined : ρ ⊢ e ↓)
  : ρ ⊢ A.s e ↓ :=
  PAS.ap_left_defined (s_defined_2 e_defined (PAS.const_defined ρ k))

@[simp] def abs [SKI α] : FreeMagma α → FreeMagma α
| .var 0 => .const i
| .var (n+1) => .ap (.const k) (.var n)
| .const a => .ap (.const k) (.const a)
| .ap e₁ e₂ => .ap (.ap (.const s) (abs e₁)) (abs e₂)

def abs_defined [SKI α] (ρ : Bwd α) (e : FreeMagma α) (h : e.fv ≤ ρ.length + 1) : ρ ⊢ $(SKI.abs e) ↓ := by
  match e with
  | .var 0 => simp; apply PAS.const_defined
  | .var (n+1) =>
    simp
    apply PAS.ap_defined
    · apply PAS.const_eval
    · apply PAS.var_get_eval ρ ⟨ n , Nat.le_of_succ_le_succ h ⟩
    · apply SKI.k_defined
      apply PAS.const_defined
  | .const a =>
    simp
    apply PAS.ap_defined
    · apply PAS.const_eval
    · apply PAS.const_eval
    · apply SKI.k_defined
      apply PAS.const_defined
  | .ap e₁ e₂ =>
    simp
    apply s_defined_2
    · have : e₁.fv ≤ ρ.length + 1 := Trans.trans (FreeMagma.fv_left_le_fv_ap e₁ e₂) h
      exact SKI.abs_defined ρ e₁ this
    · have : e₂.fv ≤ ρ.length + 1 := Trans.trans (FreeMagma.fv_right_le_fv_ap e₁ e₂) h
      exact SKI.abs_defined ρ e₂ this

def abs_refines_le [SKI α] (ρ : Bwd α) (a : α) (e : FreeMagma α) : ρ ⊢ $(abs e) a ≤ (ρ :# a) ⊢ e := by
  intros v v_eval
  match e with
  | .var 0 =>
    simp at *
    have var_eval : (ρ :# a) ⊢ `(0) ⇓ a := PAS.var_zero_eval ρ a
    have a_eval : ρ ⊢ a ⇓ v := i_eval_le _ _ v v_eval
    rwa [←PAS.const_eval_eq ρ a v a_eval]
  | .var (n+1) =>
     simp at *
     apply PAS.var_succ_eval_ge ρ a n
     apply SKI.k_eval_le ρ (.var n) (.const a) _
     · exact v_eval
     · apply PAS.const_defined
  | .const b =>
    simp at *
    apply PAS.const_eval_stable
    apply SKI.k_eval_le ρ (.const b) (.const a) _
    · exact v_eval
    · apply PAS.const_defined ρ a
  | .ap e₁ e₂ =>
    simp at *
    have ap_abs_eval : ρ ⊢ ($(abs e₁) a) ($(abs e₂) a) ⇓ v := by
      apply SKI.s_eval_le ρ (abs e₁) (abs e₂) (.const a)
      exact v_eval
    have ⟨ v₁ , v₁_eval ⟩ := PAS.ap_left_defined ⟨ v , ap_abs_eval ⟩
    have ⟨ v₂ , v₂_eval ⟩ := PAS.ap_right_defined ⟨ v , ap_abs_eval ⟩
    apply PAS.ap_eval_ge (ρ₂ := ρ) (abs_refines_le ρ a e₁ v₁ v₁_eval) (abs_refines_le ρ a e₂ v₂ v₂_eval)
    apply PAS.ap_eval_le v₁_eval v₂_eval
    exact ap_abs_eval

def abs_refines_ge [SKI α] (ρ : Bwd α) (a : α) (e : FreeMagma α) : (ρ :# a) ⊢ e ≤ ρ ⊢ $(abs e) a := by
  intros v v_eval
  match e with
  | .var 0 =>
    simp at *
    have var_eval : (ρ :# a) ⊢ `(0) ⇓ a := PAS.var_zero_eval ρ a
    apply i_eval_ge _ _
    rw [PAS.eval_functional v_eval var_eval]
    apply PAS.const_eval
  | .var (n+1) =>
    simp at *
    apply k_eval_ge ρ (.var n) (.const a) _
    · apply PAS.var_succ_eval_le ρ a n
      exact v_eval
    · apply PAS.const_defined
  | .const b =>
    simp at *
    apply k_eval_ge ρ (.const b) (.const a) _
    · apply PAS.const_eval_stable
      exact v_eval
    · apply PAS.const_defined
  | .ap e₁ e₂ =>
    simp at *
    have ⟨ v₁ , v₁_eval ⟩ := PAS.ap_left_defined ⟨ v , v_eval ⟩
    have ⟨ v₂ , v₂_eval ⟩ := PAS.ap_right_defined ⟨ v , v_eval ⟩
    apply s_eval_ge ρ (abs e₁) (abs e₂) (.const a)
    apply PAS.ap_eval_ge (ρ₂ := ρ) (abs_refines_ge ρ a e₁ v₁ v₁_eval) (abs_refines_ge ρ a e₂ v₂ v₂_eval)
    apply PAS.ap_eval_le v₁_eval v₂_eval
    exact v_eval

end SKI
