/-!
# Backwards lists
-/

universe u v w
variable {α β γ : Type u}
variable {m : Type u → Type v}

/-- Backwards lists. -/
inductive Bwd (α : Type u) : Type u where
| nil : Bwd α
| snoc : Bwd α → α → Bwd α

infixl:67 " :# " => Bwd.snoc

namespace Bwd

@[reducible] def length : Bwd α → Nat
| .nil => 0
| .snoc as _ => length as + 1

@[simp] def length_nil : length (.nil : Bwd α) = 0 := rfl
@[simp] def length_snoc (as : Bwd α) (a : α) : length (as :# a) = length as + 1 := rfl

def append (as bs : Bwd α) : Bwd α :=
match bs with
| .nil => as
| .snoc bs b => .snoc (append as bs) b

instance : Append (Bwd α) where
  append := append

@[simp] def length_append (as bs : Bwd α) : length (append as bs) = length as + length bs := by
  induction bs <;> simp [append]
  case snoc bs b ih => simp [←Nat.add_assoc, ih]

@[simp] def append_nil (as : Bwd α) : as ++ .nil = as := rfl
@[simp] def append_snoc (as bs : Bwd α) (b : α) : as ++ (bs :# b) = (as ++ bs) :# b := rfl

@[simp] def nil_append (as : Bwd α) : .nil ++ as = as := by
  induction as <;> simpa

def getRev (as : Bwd α) (i : Fin as.length) : α :=
match as with
| .nil => by
  have : i.val < 0 := i.is_lt
  contradiction
| .snoc as a =>
  if h : i = (0 : Fin (as.length + 1)) then
    a
  else
    getRev as (Fin.pred i h)

@[simp] theorem getRev_snoc_zero (as : Bwd α) (a : α) : getRev (snoc as a) 0 = a := rfl
@[simp] theorem getRev_snoc_succ (as : Bwd α) (a : α) (n : Fin as.length) : getRev (snoc as a) (Fin.succ n) = getRev as n := rfl

theorem getRev_snoc_pred_ne_zero (as : Bwd α) (a : α) (n : Fin (as.length + 1)) (h : n ≠ 0) : getRev (snoc as a) n = getRev as (Fin.pred n h) := by
 simp [getRev, dif_neg h]

def foldBwdM [Monad m] (f : β → α → m β) (init : β) : Bwd α → m β
| .nil => pure init
| .snoc as a => do
  let b ← foldBwdM f init as
  f b a

def foldBwd (f : β → α → β) (init : β) (as : Bwd α) : β :=
  Id.run <| foldBwdM f init as

@[simp] def foldBwdM_nil [Monad m]
  (f : β → α → m β) (init : β)
  : foldBwdM f init .nil = pure init := rfl

@[simp] def foldBwdM_snoc [Monad m]
  (f : β → α → m β) (init : β)
  (as : Bwd α) (a : α)
  : foldBwdM f init (.snoc as a) = foldBwdM f init as >>= (fun b => f b a) := rfl

@[simp] def foldBwd_snoc
  (f : β → α → β) (init : β)
  (as : Bwd α) (a : α)
  : foldBwd f init (.snoc as a) = f (foldBwd f init as) a := rfl
