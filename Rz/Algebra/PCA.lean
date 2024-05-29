import Mathlib.Init.Order.Defs
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Use

import Rz.Syntax.Magma
import Rz.Data.Bwd

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
def PAS.Eval [PAS α] : (ρ : Bwd α) → FreeMagma α → α → Prop
  | ρ, .var i, v => ∃ h, ρ.get ⟨i, h⟩ = v
  | _, .const a, v => a = v
  | ρ, .ap e₁ e₂, v => ∃ v₁ v₂, Eval ρ e₁ v₁ ∧ Eval ρ e₂ v₂ ∧ PAS.Ap v₁ v₂ v

syntax term " ⊢ " magma " ⇓ " term:40 : term
macro_rules
| `($ρ:term ⊢ $e:magma ⇓ $a:term) => `(PAS.Eval $ρ («magma» $e) $a)

namespace PAS
/-- `Undefined ρ e` denotes that an expression `e` diverges when evaluated in environment `ρ`. -/
def Undefined [PAS α] (ρ : Bwd α) (e : FreeMagma α) : Prop := (a : α) → ¬ (ρ ⊢ e ⇓ a)
/-- `Defined ρ e` denotes that an expression `e` diverges when evaluated in environment `ρ`. -/
def Defined [PAS α] (ρ : Bwd α) (e : FreeMagma α) : Prop := ∃ (a : α), ρ ⊢ e ⇓ a
/-- `Refines ρ e₁ e₂` denotes that an expression `e₂` is least as defined as `e₁`. -/
def Refines [PAS α] (ρ₁ : Bwd α) (e₁ : FreeMagma α) (ρ₂ : Bwd α) (e₂ : FreeMagma α) : Prop := {a : α} → ρ₁ ⊢ e₁ ⇓ a → ρ₂ ⊢ e₂ ⇓ a
end PAS

@[inherit_doc PAS.Undefined]
syntax term " ⊢ " magma " ↑" : term
@[inherit_doc PAS.Defined]
syntax term " ⊢ " magma " ↓" : term
@[inherit_doc PAS.Refines]
syntax term " ⊢ " magma " ≤ " term:max " ⊢ " withPosition(magma) : term

macro_rules
| `($ρ:term ⊢ $e:magma ↑) => `(PAS.Undefined $ρ («magma» $e))
| `($ρ:term ⊢ $e:magma ↓) => `(PAS.Defined $ρ («magma» $e))
| `($ρ₁:term ⊢ $e₁:magma ≤ $ρ₂:term ⊢ $e₂:magma) => `(PAS.Refines $ρ₁ («magma» $e₁) $ρ₂ («magma» $e₂))


namespace PAS

/-!
### Order-Theoretic Properties of Refinement
-/

/-- The refinement relation extends to a preorder on expressions. -/
instance Refine [PAS α] {ρ : Bwd α} : Preorder (FreeMagma α) where
  le e₁ e₂ := PAS.Refines ρ e₁ ρ e₂
  le_refl e v v_eval := v_eval
  le_trans e₁ e₂ e₃ p q v v_eval := q (p v_eval)
variable [PAS α]

/-- Application is monotonic with respect to refinement. -/
theorem ap_le_ap
  {ρ : Bwd α}
  {e₁ e₂ e₁' e₂' : FreeMagma α}
  (le_left : ρ ⊢ e₁ ≤ ρ ⊢ e₁') (le_right : ρ ⊢ e₂ ≤ ρ ⊢ e₂')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁' e₂' := by
    intros v v_eval
    simp [Eval] at *
    have ⟨ v₁ , v₁_eval , v₂ , v₂_eval, v_ap ⟩ := v_eval
    exact ⟨ v₁ , le_left v₁_eval, v₂ , le_right v₂_eval, v_ap ⟩

@[inherit_doc ap_le_ap]
theorem ap_le_ap_right
  {ρ : Bwd α}
  {e₁ e₂ e₂' : FreeMagma α}
  (le_right : ρ ⊢ e₂ ≤ ρ ⊢ e₂')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁ e₂' := ap_le_ap (Refine.le_refl e₁) le_right

@[inherit_doc ap_le_ap]
theorem ap_le_ap_left
  {ρ : Bwd α}
  {e₁ e₂ e₁' : FreeMagma α}
  (le_left : ρ ⊢ e₁ ≤ ρ ⊢ e₁')
  : ρ ⊢ e₁ e₂ ≤ ρ ⊢ e₁' e₂ := ap_le_ap le_left (Refine.le_refl e₂)

theorem ap_eval
  {ρ : Bwd α}
  {e₁ e₂ : FreeMagma α} {v : α}
  : ρ ⊢ e₁ e₂ ⇓ v ↔ ∃ v₁ v₂ : α, ρ ⊢ e₁ ⇓ v₁ ∧  ρ ⊢ e₂ ⇓ v₂ ∧ PAS.Ap v₁ v₂ v := by simp [PAS.Eval]

theorem ap_congl
  {ρ : Bwd α}
  {e₁ e₂ : FreeMagma α} {v : α}
  : ρ ⊢ e₁ e₂ ⇓ v ↔ ∃ v₁ : α, ρ ⊢ e₁ ⇓ v₁ ∧ ρ ⊢ v₁ e₂ ⇓ v := by
  simp [PAS.Eval]

theorem ap_congr
  {ρ : Bwd α}
  {e₁ e₂ : FreeMagma α} {v : α}
  : ρ ⊢ e₁ e₂ ⇓ v ↔ ∃ v₂ : α, ρ ⊢ e₂ ⇓ v₂ ∧ ρ ⊢ e₁ v₂ ⇓ v := by
  simp [PAS.Eval]
  apply Iff.intro
  · rintro ⟨ v₁ , v₁_eval , v₂ , v₂_eval , v_ap ⟩
    exact ⟨ v₂ , v₂_eval , v₁ , v₁_eval , v_ap ⟩
  · rintro ⟨ v₂ , v₂_eval , v₁ , v₁_eval , v_ap ⟩
    exact ⟨ v₁ , v₁_eval , v₂ , v₂_eval , v_ap ⟩

@[simp] theorem const_eval
  {ρ : Bwd α}
  {a v : α}
  : ρ ⊢ a ⇓ v ↔ a = v := by
  simp [PAS.Eval]

/-!
### Evaluation Lemmas
-/

/-- Evaluation is a functional relation. -/
theorem eval_functional
    {ρ : Bwd α}
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
  abs_defined : (ρ : Bwd α) → (e : FreeMagma α) → ρ ⊢ $(abs e) ↓
  /-- Bracket abstraction has a β-law. -/
  abs_eval : {ρ : Bwd α} → {e₁ e₂ : FreeMagma α} → {v₁ : α} → ρ ⊢ $(abs e₁) e₂ ⇓ v₁ ↔ (∃ v₂, ρ ⊢ e₂ ⇓ v₂ ∧ (ρ :# v₂) ⊢ e₁ ⇓ v₁)

namespace PCA

variable [PCA α]

def absn (e : FreeMagma α) (n : Nat) : FreeMagma α :=
  match n with
  | 0 => e
  | n+1 => (absn (abs e) n)

theorem absn_le
  {ρ : Bwd α} {e : FreeMagma α} {as : Bwd (FreeMagma α)} {v : α} {vargs : Bwd α}
  (e_eval : ρ ⊢ $(absn e as.length) $[as]* ⇓ v)
  (h : as.length = vargs.length)
  (as_eval : ∀ (i : Fin as.length), ρ ⊢ $(as.get i) ⇓ vargs.get (Fin.cast h i))
  : (ρ ++ vargs) ⊢ e ⇓ v := by
    match as, vargs with
    | .nil, .nil =>
      simp [absn] at *
      exact e_eval
    | .snoc as a, .snoc vargs varg =>
      simp [absn, Bwd.foldBwd_snoc] at *
      have ⟨ vbody , vbody_eval , v_ap ⟩ := PAS.ap_congl.1 e_eval
      have ih_eval := absn_le (vargs := vargs) vbody_eval sorry sorry
      have a_eval := as_eval 0
      simp at a_eval
      have outer_eval : (ρ ++ vargs) ⊢ $(abs e) varg ⇓ v := by
        rw [PAS.ap_congl]
        use _, ih_eval
        sorry
        -- simp [PAS.Eval]
        -- sorry
      have ⟨ varg', varg_eq, final_eval ⟩ := abs_eval.1 outer_eval
      simp at varg_eq
      rwa [varg_eq]

protected def id : FreeMagma α :=
  abs (.var 0)

protected theorem id_le (ρ : Bwd α) (e : FreeMagma α) : ρ ⊢ PCA.id e ≤ ρ ⊢ e := by
  intro v v_eval
  rewrite [PCA.id, PCA.abs_eval] at v_eval
  simp [PAS.Eval] at v_eval
  exact v_eval

protected theorem le_id (ρ : Bwd α) (e : FreeMagma α) : ρ ⊢ e ≤ ρ ⊢ PCA.id e := by
  intro v v_eval
  simp [PCA.id, PCA.abs_eval]
  simp [PAS.Eval]
  exact v_eval

@[simp] protected theorem i_eval {ρ : Bwd α} {e : FreeMagma α} {v : α} : ρ ⊢ PCA.id e ⇓ v ↔ ρ ⊢ e ⇓ v :=
  ⟨ PCA.id_le _ _ , PCA.le_id _ _ ⟩

-- \f g x.
protected def comp : FreeMagma α :=
  abs (abs (abs («magma» `(1) (`(2) `(0)))))

protected theorem comp_le
  {ρ : Bwd α} {e₁ e₂ e₃ : FreeMagma α} {v : α}
  : ρ ⊢ PCA.comp e₁ e₂ e₃ ≤ ρ ⊢ e₂ (e₁ e₃) := by
  intro v v_eval
  sorry

protected theorem le_comp
  {ρ : Bwd α} {e₁ e₂ e₃ : FreeMagma α} {v : α}
  : ρ ⊢ e₂ (e₁ e₃) ≤ ρ ⊢ PCA.comp e₁ e₂ e₃ :=
  sorry


@[simp] protected theorem comp_eval
  {ρ : Bwd α} {e₁ e₂ e₃ : FreeMagma α} {v : α}
  : ρ ⊢ PCA.comp e₁ e₂ e₃ ⇓ v ↔ ρ ⊢ e₂ (e₁ e₃) ⇓ v :=
  ⟨ PCA.comp_le (v := v) , PCA.le_comp (v := v) ⟩
-- @[simp] protected def comp_eval {ρ : Bwd α} {e₁ e₂ e₃ : FreeMagma α} {v : α} : ρ ⊢ PCA.comp e ⇓ v ↔ ρ ⊢ e ⇓ v := sorry

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
