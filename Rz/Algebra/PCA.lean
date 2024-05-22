/-
# Partial Combinatory Algebras
-/
import Mathlib.Tactic.Simps.Basic
import Mathlib.Data.Part
import Mathlib.Data.List.Indexes

import Rz.Data.Bwd
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

/-- Extends application to (snoc) lists. -/
instance [H : HasAp α β (Part α)] : HasAp α (Bwd β) (Part α) where
  hAp a bs := Bwd.foldBwdM H.hAp a bs

@[simp] theorem aps_bwd_nil [HasAp α β (Part α)] (a : α) : a ⋆ (Bwd.nil : Bwd β) = a := by
  simp [HasAp.hAp]

@[simp] theorem aps_bwd_cons [HasAp α β (Part α)] (a : α) (bs : Bwd β) (b : β) : a ⋆ (bs :# b) = (a ⋆ bs) ⋆ b := by
  simp [HasAp.hAp]

@[simp] theorem aps_list_append [HasAp α β (Part α)] (a : α) (as bs : Bwd β) : a ⋆ (as ++ bs) = (a ⋆ as) ⋆ bs := by
  simp [HasAp.hAp]


/-- Partial Applicative Structures. -/
class PAS (α : Type u) where
  ap : α → α → Part α

@[default_instance]
instance instPasApply [PAS α] : HasAp α α (Part α) where
  hAp := PAS.ap

/-- Reduce a word in the free magma using `PAS.ap`. -/
def PAS.eval [PAS α] (ρ : Bwd α) : FreeMagma α ρ.length → Part α :=
  FreeMagma.foldM (fun x => pure (Bwd.get ρ x)) pure PAS.ap

@[simp] theorem PAS.var [PAS α] (ρ : Bwd α) (x : Fin ρ.length) : PAS.eval ρ (.var x) = ρ.get x := rfl
@[simp] theorem PAS.eval_const [PAS α] (ρ : Bwd α) (a : α) : PAS.eval ρ (.const a) = a := rfl
@[simp] theorem PAS.op [PAS α] (ρ : Bwd α) (e₁ e₂ : FreeMagma α ρ.length) : PAS.eval ρ (.op e₁ e₂) = PAS.eval ρ e₁ ⋆ PAS.eval ρ e₂ := rfl


-- @[simp] theorem PAS.eval_const_dom [PAS α] (a : α) (ρ : List α) : PAS.eval ρ (.const a) ↓ := by
--   simp [PAS.eval, FreeMagma.foldM]

-- @[simp] theorem PAS.eval_op_dom [PAS α] (ρ : List α) (e₁ e₂ : FreeMagma α ρ.length) : PAS.eval ρ (.op e₁ e₂) ↓ ↔ PAS.eval ρ e₁ ⋆ PAS.eval ρ e₂ ↓ := Iff.rfl

class PCA (α : Type u) extends PAS α where
  rep : {n : Nat} → FreeMagma α (n + 1) → α
  rep_dom
    : (ρ : Bwd α) → (e : FreeMagma α (ρ.length + 1)) → rep e ⋆ ρ ↓
  rep_eval
    : (ρ : Bwd α) → (a : α) → (e : FreeMagma α (ρ.length + 1))
    → rep e ⋆ ρ = PAS.eval (ρ :# a) e

/-!
# Completeness of the SKI basis.
-/

class SKI (α : Type u) extends PAS α where
  /-- `s` combinator; analog of the λ-term `fun x y z => (x y) (x z)`. -/
  s : α
  /-- `k` combinator; analog of the λ-term `fun x y => x`. -/
  k : α
  /-- Applying `s` to two arguments is always defined. -/
  sDom : (a b : α) → s ⋆ a ⋆ b ↓
  /-- Applying `k` to one argument is always defined. -/
  kDom : (a : α) → k ⋆ a ↓
  /-- Characterize computational behaviour of `s`. -/
  sEval : (a b c : α) → s ⋆ a ⋆ b ⋆ c = (a ⋆ b) ⋆ (a ⋆ c)
  /-- Characterize computational behaviour of `k`. -/
  kEval : (a b : α) → k ⋆ a ⋆ b = a

  /-- `i` combinator; can be derived from `s` and `k` -/
  i : α := (s ⋆ k ⋆ k).get (sDom k k)
  /-- Characterize computational behaviour of `i`. -/
  iEval : (a : α) → i ⋆ a = a


namespace SKI

@[simp] def s_dom_1 [SKI α] (a : α) : s ⋆ a ↓ := (SKI.sDom a k).fst
@[simp] def s_dom_2 [SKI α] (a b : α) : s ⋆ a ⋆ b ↓ := SKI.sDom a b
@[simp] def s_dom_2_get [SKI α] (a b : α) : (s ⋆ a).get (s_dom_1 a) ⋆ b ↓ := (SKI.sDom a b).snd
@[simp] def k_dom_1 [SKI α] (a : α) : k ⋆ a ↓ := SKI.kDom a

/-- Bracket abstraction. -/
def abs [SKI α] : FreeMagma α (n + 1) → FreeMagma α n
| .var x =>
  if h : x = 0 then
    .const i
  else
    .op (.const k) (.var (Fin.pred x h))
| .const a =>
  .op (.const k) (.const a)
| .op e₁ e₂ =>
  .op (.op (.const s) (abs e₁)) (abs e₂)

/-- Iterated bracket abstraction. -/
def absn [SKI α] {m : Nat} (n : Nat) (e : FreeMagma α (m + n)) : FreeMagma α m :=
match n with
| 0 => e
| n+1 => absn n (abs e)

def eval_abs_dom [SKI α] (ρ : Bwd α) (e : FreeMagma α (ρ.length + 1)) : PAS.eval ρ (abs e) ↓ := by
  induction e <;> simp [abs]
  case var x =>
    cases (decEq x 0)
    case isTrue h =>
      simp [dif_pos h]
    case isFalse h =>
      simp [dif_neg h]
  case op e₁ e₂ e₁_ih e₂_ih =>
    exists e₁_ih
    exists e₂_ih
    apply s_dom_2_get

def eval_absn_dom [SKI α] (n : Nat) (ρ : Bwd α) (e : FreeMagma α (ρ.length + n + 1)) : PAS.eval ρ (absn (n + 1) e) ↓ := by
  induction n <;> simp [absn]
  case zero =>
    exact (eval_abs_dom ρ e)
  case succ n ih =>
    apply ih

def rep [SKI α] (ρ : Bwd α) (n : Nat) (e : FreeMagma α (ρ.length + n + 1)) : α :=
  (PAS.eval ρ (absn (n + 1) e)).get (eval_absn_dom n ρ e)

def rep_dom [SKI α] (ρ σ : Bwd α) (e : FreeMagma α (ρ.length + σ.length + 1)) : rep ρ σ.length e ⋆ σ ↓ := by
  induction σ <;> simp [rep, absn]
  case nil =>
    exact (eval_abs_dom ρ e)
  case snoc σ a ih =>
    exists (ih (abs e))
    sorry
    -- sorry
    -- exact (eval_absn_dom _ ρ e)
end SKI



-- def PAS.rep_dom [PAS α]
--   (s k i : α)
--   (s_def : (a b : α) → (s ⋆ a ⋆ b) ↓)
--   (k_def : (a : α) → (k ⋆ a) ↓)
--   (ρ σ : Bwd α)
--   (e : FreeMagma α (ρ.length + σ.length + 1))
--   : (PAS.rep s k i s_def k_def ρ σ.length e) ⋆ σ ↓ := by
--   unfold rep
--   induction σ
--   case nil =>
--     simp
--     exact (PAS.eval_absn_dom s k i s_def k_def ρ e)
--   case snoc σ a ih =>
--     simp [absn]
--     sorry
--     -- exists (ih (abs s k i e))
    -- sorry

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
