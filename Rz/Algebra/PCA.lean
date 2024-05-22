/-
# Partial Combinatory Algebras
-/
import Mathlib.Tactic.Simps.Basic
import Mathlib.Data.Part
import Mathlib.Data.List.Indexes

import Rz.Data.Part
import Rz.Syntax.Magma


universe u v w
variable {α β : Type u}

/-- Notation typeclass for `a ⋆ b`. -/
@[notation_class]
class HasAp (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a ⋆ b` computes to the application of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hAp : α → β → γ

@[inherit_doc] infixl:60 " ⋆ " => HasAp.hAp

/-- Extends application to an operation on partial elements. -/
instance instPartLeft [H : HasAp α β (Part γ)] : HasAp (Part α) β (Part γ) where
  hAp a b := do
    Part.bind a (fun a => H.hAp a b)

@[simp] theorem ap_some_left [HasAp α β (Part γ)] (a : α) (b : β) : Part.some a ⋆ b = a ⋆ b := by
  simp [HasAp.hAp]

@[simp] theorem ap_bind_left_dom [HasAp α β (Part γ)] (a : Part α) (b : β) : a ⋆ b ↓ ↔ ∃ h : a ↓, a.get h ⋆ b ↓ := by
  simp [HasAp.hAp]

instance instPartRight [H : HasAp α β (Part γ)] : HasAp α (Part β) (Part γ) where
  hAp a b := do
    Part.bind b (fun b => H.hAp a b)

@[simp] theorem ap_some_right [HasAp α β (Part γ)] (a : α) (b : β) : a ⋆ Part.some b = a ⋆ b := by
  simp [HasAp.hAp]

@[simp] theorem ap_bind_right_dom [HasAp α β (Part γ)] (a : α) (b : Part β) : a ⋆ b ↓ ↔ ∃ h : b ↓, a ⋆ b.get h ↓ := by
  simp [HasAp.hAp]

/-- Extends application to lists. -/
instance [H : HasAp α β (Part α)] : HasAp α (List β) (Part α) where
  hAp a bs := List.foldlM H.hAp a bs

@[simp] theorem aps_list_nil [HasAp α β (Part α)] (a : α) : a ⋆ ([] : List β) = a := by
  simp [HasAp.hAp]

@[simp] theorem aps_list_cons [HasAp α β (Part α)] (a : α) (b : β) (bs : List β) : a ⋆ (b :: bs) = (a ⋆ b) ⋆ bs := by
  simp [HasAp.hAp]

@[simp] theorem aps_list_append [HasAp α β (Part α)] (a : α) (as bs : List β) : a ⋆ (as ++ bs) = (a ⋆ as) ⋆ bs := by
  simp [HasAp.hAp]


/-- Partial Applicative Structures. -/
class PAS (α : Type u) where
  ap : α → α → Part α

@[default_instance]
instance instPasApply [PAS α] : HasAp α α (Part α) where
  hAp := PAS.ap

/-- Reduce a word in the free magma using `PAS.ap`. -/
def PAS.eval [PAS α] (ρ : List α) : FreeMagma α ρ.length → Part α :=
  FreeMagma.foldM (fun x => pure (List.get ρ x)) pure PAS.ap

@[simp] theorem PAS.var [PAS α] (ρ : List α) (x : Fin ρ.length) : PAS.eval ρ (.var x) = ρ.get x := rfl
@[simp] theorem PAS.eval_const [PAS α] (ρ : List α) (a : α) : PAS.eval ρ (.const a) = a := rfl
@[simp] theorem PAS.op [PAS α] (ρ : List α) (e₁ e₂ : FreeMagma α ρ.length) : PAS.eval ρ (.op e₁ e₂) = PAS.eval ρ e₁ ⋆ PAS.eval ρ e₂ := rfl


-- @[simp] theorem PAS.eval_const_dom [PAS α] (a : α) (ρ : List α) : PAS.eval ρ (.const a) ↓ := by
--   simp [PAS.eval, FreeMagma.foldM]

-- @[simp] theorem PAS.eval_op_dom [PAS α] (ρ : List α) (e₁ e₂ : FreeMagma α ρ.length) : PAS.eval ρ (.op e₁ e₂) ↓ ↔ PAS.eval ρ e₁ ⋆ PAS.eval ρ e₂ ↓ := Iff.rfl

class PCA (α : Type u) extends PAS α where
  rep : {n : Nat} → FreeMagma α (n + 1) → α
  rep_dom
    : (ρ : List α) → (e : FreeMagma α (ρ.length + 1)) → rep e ⋆ ρ ↓
  rep_eval
    : (a : α) → (ρ : List α) → (e : FreeMagma α (ρ.length + 1))
    → rep e ⋆ ρ = PAS.eval (a :: ρ) e

/-- Bracket abstract using `s, k, i : α`. -/
def PAS.abs [PAS α] (s k i : α) : FreeMagma α (n + 1) → FreeMagma α n
| .var x =>
  if h : x = 0 then
    .const i
  else
    .op (.const k) (.var (Fin.pred x h))
| .const a =>
  .op (.const k) (.const a)
| .op l r =>
  .op (.op (.const s) (PAS.abs s k i l)) (PAS.abs s k i r)

/-- Abstracting `e : FreeMagma α (n + 1)` and applying to `n` arguments terminates. -/
def PAS.eval_abs_dom
  [PAS α]
  (s k i : α)
  (s_def : (a b : α) → s ⋆ a ⋆ b ↓)
  (k_def : (a : α) → k ⋆ a ↓)
  (ρ : List α)
  (e : FreeMagma α (ρ.length + 1))
  : PAS.eval ρ (PAS.abs s k i e) ↓ := by
  induction e <;> simp [abs]
  case var x =>
    cases (decEq x 0)
    case isTrue h =>
      simp [dif_pos h]
    case isFalse h =>
      simp [dif_neg h]
      apply k_def
  case const a =>
    apply k_def
  case op e₁ e₂ e₁_ih e₂_ih =>
    exists ⟨ e₁_ih, (s_def _ k).fst ⟩
    exists e₂_ih
    apply (s_def _ _).snd

/-- Iterated bracket abstraction. -/
def PAS.absn [PAS α] {m : Nat} (s k i : α) (n : Nat) (e : FreeMagma α (m + n)) : FreeMagma α m :=
match n with
| 0 => e
| n+1 => PAS.absn s k i n (PAS.abs s k i e)

/-- Iterated bracket abstraction yields values. -/
def PAS.eval_absn_dom
  [PAS α]
  (s k i : α)
  (s_def : (a b : α) → s ⋆ a ⋆ b ↓)
  (k_def : (a : α) → k ⋆ a ↓)
  (ρ : List α)
  (e : FreeMagma α (ρ.length + n + 1))
  : PAS.eval ρ (PAS.absn s k i (n + 1) e) ↓ := by
  induction n <;> simp [absn]
  case zero =>
    exact (PAS.eval_abs_dom s k i s_def k_def ρ e)
  case succ n ih =>
    apply ih


/-- Bracket abstract `n + 1` variables and evaluate -/
def PAS.rep [PAS α]
  (s k i : α)
  (s_def : (a b : α) → (s ⋆ a ⋆ b) ↓)
  (k_def : (a : α) → (k ⋆ a) ↓)
  (ρ : List α) (n : Nat)
  (e : FreeMagma α (ρ.length + n + 1)) : α :=
  (PAS.eval ρ (PAS.absn s k i (n + 1) e)).get (PAS.eval_absn_dom s k i s_def k_def ρ e)


def PAS.rep_dom [PAS α]
  (s k i : α)
  (s_def : (a b : α) → (s ⋆ a ⋆ b) ↓)
  (k_def : (a : α) → (k ⋆ a) ↓)
  (ρ σ : List α)
  (e : FreeMagma α (ρ.length + σ.length + 1))
  : (PAS.rep s k i s_def k_def ρ σ.length e) ⋆ σ ↓ := by
  unfold rep
  induction σ using List.list_reverse_induction <;> simp
  case base => exact (PAS.eval_absn_dom s k i s_def k_def ρ e)
  case ind σ a ih => 
    apply Exists.intro
    case w => 
      simp [absn]
      rw [←List.length_append σ [a]] at *
      apply ih
    case h => sorry
    -- exists (ih _)
    -- sorry
  -- case cons a σ ih => sorry -- rep ⋆ (a :: σ) = (rep ⋆ a) ⋆ σ
--   : ((PAS.rep s k i s_def k_def ρ e) ⋆ σ) ↓ := by
--   induction n generalizing ρ σ
--   case zero => sorry
--   case succ n ih => 
--     cases σ
--     case nil => sorry
--     case cons a σ => 
--       simp [rep, HasAp.hAp] at *
--       sorry

-- match n, a with
-- | Nat.zero, a => by
--   contradiction
-- | Nat.succ n, a => by
--   induction a
--   case var x => 
--     sorry
--   case const a =>
--     have 
--     -- simp [HasAp.hAp, PAS.rep, PAS.abs]
--     -- ap Exists.intro
--     -- · sorry
--     -- · sorry
--   case op l r l_ih r_ih =>
--     have l_def : (rep s k i l) ↓ := by
--       ap Part.Dom.of_bind
--       exact l_ih
--     have r_def : (rep s k i r) ↓ := by
--       ap Part.Dom.of_bind
--       exact r_ih
--     have lr_def : (rep s k i (.op l r)) ↓ := by
--       sorry
--     exists lr_def
--     simp [HasAp.hAp, PAS.rep]
--     sorry
--     -- simp [HasAp.hAp]
--     -- ap Exists.intro
--     -- · sorry
--     -- · simp [PAS.rep]

-- def PCA.k [PCA α] : α :=
--   PCA.rep FreeMagma.k

-- def PCA.s [PCA α] : α :=
--   PCA.rep FreeMagma.s

-- def PCA.i [PCA α] : α :=
--   (PAS.aps PCA.s [PCA.k, PCA.k]).get (PCA.rep_def FreeMagma.s [PCA.k, PCA.k] (by simp))

-- def PCA.abs [PCA α] : FreeMagma α (n + 1) → FreeMagma α n
-- | .var 0 => .const PCA.i
-- | .var ⟨ x+1 , h ⟩ => .op (.const PCA.k) (.var ⟨ x , by omega ⟩)
-- | .const a => .op (.const PCA.k) (.const a)
-- | .op l r => .op (.op (.const PCA.s) (PCA.abs l)) (PCA.abs r)

-- def PCA.s_k_complete
--   [A : PAS α]
--   (s k i : α)
--   (s_def : (a b : α) → (s ⋆ [a, b]) ↓)
--   (k_def : (a : α) → (k ⋆ a) ↓)
--   (s_eval : (a b c : α) → KleeneEquiv (s ⋆ [a, b, c]) (A.evalClosed (.op (.op (.const a) (.const c)) (.op (.const b) (.const c)))))
--   (k_eval : (a b : α) → (k ⋆ [a, b]) = a)
--   (i_eval : (a : α) → (i ⋆ a) = a)
--   : PCA α := {
--   rep := PAS.rep s k i
--   rep_def := _
--   rep_eval := _
-- }
