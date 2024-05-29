import Rz.Data.Bwd
import Rz.Syntax.Magma
import Rz.Syntax.Subst

import Rz.Algebra.PCA

universe u v w
variable {α β : Type u}


/-!
# Small-step PCAs

We have opted to use a "big-step" formulation of PCAs, where the
partial binary application is replaced with a functional relation `ρ ⊢ e ⇓ a`
between environments of type `Bwd α`, expressions of type `FreeMagma α`, and
values of type α.

However, this is not the only approach: we can also use a "small-step" variant;
which opts for a ternary relation `a₁ · a₂ ↝ a₃` between elements of `α`.
-/


class SmallStepPAS (α : Type u) where
  /-- `a₁ · a₂ ↝ a₃` denotes that applying a₁ to a₂ reduces to a₃. -/
  Ap : α → α → α → Prop
  /-- The application relation is functional. -/
  ap_functional : {a₁ a₂ v₁ v₂ : α} → Ap a₁ a₂ v₁ → Ap a₁ a₂ v₂ → v₁ = v₂

@[inherit_doc SmallStepPAS.Ap]
syntax term " ⋆ " term " ↝ " term:40 : term

macro_rules
| `($a₁:term ⋆ $a₂:term ↝ $a₃:term) => `(SmallStepPAS.Ap $a₁ $a₂ $a₃)

namespace SmallStepPAS


/-- Extend the small-step relation to a big-step relation on `FreeMagma α`. -/
def Eval [SmallStepPAS α] : (ρ : Bwd α) → FreeMagma α → α → Prop
  | ρ, .var i, v => ∃ h, ρ.get ⟨i, h⟩ = v
  | _, .const a, v => a = v
  | ρ, .ap e₁ e₂, v => ∃ v₁ v₂, Eval ρ e₁ v₁ ∧ Eval ρ e₂ v₂ ∧ v₁ ⋆ v₂ ↝ v

instance [SmallStepPAS α] : HasEval α := ⟨SmallStepPAS.Eval⟩

/-- The derived big-step relation is functional. -/
theorem eval_functional [SmallStepPAS α] {ρ e} {a a' : α}
    (h1 : Eval ρ e a) (h2 : Eval ρ e a') : a = a' := by
  induction e generalizing a a' with simp [HasEval.Eval, Eval] at h1 h2
  | var => obtain ⟨_, rfl⟩ := h1; obtain ⟨_, rfl⟩ := h2; rfl
  | const => exact h1 ▸ h2
  | ap _ _ ih1 ih2 =>
    obtain ⟨_, ev11, _, ev12, h1⟩ := h1
    obtain ⟨_, ev21, _, ev22, h2⟩ := h2
    cases ih1 ev11 ev21
    cases ih2 ev12 ev22
    exact ap_functional h1 h2

/-- A small-step PAS can be canonically extended to a big-step PAS. -/
def toPAS (α : Type u) [SmallStepPAS α] : PAS α where
  eval_functional := eval_functional
  var_zero_eval _ _ := ⟨Nat.succ_pos _, rfl⟩
  var_succ_eval _ _ _ :=
    ⟨fun _ ⟨h, eq⟩ => ⟨Nat.lt_of_succ_lt_succ h, eq⟩, fun _ ⟨h, eq⟩ => ⟨Nat.succ_lt_succ h, eq⟩⟩
  var_zero_diverge := nofun
  const_eval _ _ := rfl
  ap_eval h1 h2 := by
    refine ⟨fun v' ⟨a₁', a₂', e1, e2, H⟩ => ⟨_, _, rfl, rfl, ?_⟩, fun v' ⟨_, _, rfl, rfl, H⟩ => ⟨_, _, h1, h2, H⟩⟩
    cases eval_functional h1 e1
    cases eval_functional h2 e2
    exact H
  ap_left_defined := fun ⟨_, _, _, h, _⟩ => ⟨_, h⟩
  ap_right_defined := fun ⟨_, _, _, _, h, _⟩ => ⟨_, h⟩

/-- Every big-step PAS gives rise to a small-step PAS. -/
def ofPAS (α : Type u) [PAS α] : SmallStepPAS α where
  Ap a₁ a₂ v := .nil ⊢ a₁ a₂ ⇓ v
  ap_functional := PAS.eval_functional

theorem ofPAS_toPAS (α : Type u) [inst : PAS α] : @toPAS α (@ofPAS α inst) = inst := by
  suffices (ofPAS α).Eval = inst.Eval by
    let {..} := inst; unfold ofPAS toPAS instHasEval; congr
  ext ρ e v; constructor <;> intro H
  · induction e generalizing v with simp [SmallStepPAS.Eval] at H
    | const => cases H; apply PAS.const_eval
    | var => obtain ⟨_, rfl⟩ := H; exact PAS.var_get_eval ρ ⟨_, _⟩
    | ap _ _ ih1 ih2 =>
      obtain ⟨_, h1, _, h2, h3⟩ := H
      exact (PAS.ap_eval (ih1 _ h1) (ih2 _ h2)).2 _ h3
  · induction e generalizing v with simp [SmallStepPAS.Eval]
    | const => exact PAS.eval_functional (PAS.const_eval ..) H
    | var =>
      have h := PAS.var_of_converge _ _ ⟨_, H⟩
      exact ⟨h, PAS.eval_functional (PAS.var_get_eval _ ⟨_, h⟩) H⟩
    | ap _ _ ih1 ih2 =>
      have ⟨a₁, h1⟩ := PAS.ap_left_defined ⟨_, H⟩
      have ⟨a₂, h2⟩ := PAS.ap_right_defined ⟨_, H⟩
      exact ⟨_, ih1 _ h1, _, ih2 _ h2, (PAS.ap_eval h1 h2).1 _ H⟩

theorem toPAS_ofPAS (α : Type u) [inst : SmallStepPAS α] : @ofPAS α (@toPAS α inst) = inst := by
  sorry
  -- suffices (@ofPAS α (@toPAS α inst)).Ap = inst.Ap by
  --   let {..} := inst; unfold ofPAS toPAS instHasEval; congr
  -- ext ρ e v; constructor <;> intro H
  -- · exact H
end SmallStepPAS

