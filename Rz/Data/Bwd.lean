/-!
# Backwards lists
-/

universe u v w
variable {α β γ : Type u}

/-- Backwards lists. -/
inductive Bwd (α : Type u) : Type u where
| nil : Bwd α
| snoc : Bwd α → α → Bwd α

infixl:67 " :# " => Bwd.snoc

namespace Bwd

def length : Bwd α → Nat
| .nil => 0
| .snoc as _ => length as + 1

@[simp] def length_nil : length (.nil : Bwd α) = 0 := rfl
@[simp] def length_snoc (as : Bwd α) (a : α) : length (.snoc as a) = length as + 1 := rfl

def append (as bs : Bwd α) : Bwd α :=
match bs with
| .nil => as
| .snoc bs b => .snoc (append as bs) b

instance : Append (Bwd α) where
  append := append

@[simp] def length_append (as bs : Bwd α) : length (append as bs) = length as + length bs := by
  induction bs <;> simp [append]
  case snoc bs b ih => simp [←Nat.add_assoc, ih]

@[simp] def append_nil (as : Bwd α) : append as .nil = as := rfl
@[simp] def nil_append (as : Bwd α) : append .nil as = as := by
  induction as <;> simpa [append]

def get (as : Bwd α) (i : Fin as.length) : α :=
match as with
| .nil => by
  have : i.val < 0 := i.is_lt
  contradiction
| .snoc as a =>
  if h : i = (0 : Fin (as.length + 1)) then
    a
  else
    get as (Fin.pred i h)

def foldBwdM [Monad m] (f : β → α → m β) (init : β) : Bwd α → m β
| .nil => pure init
| .snoc as a => do
  let b ← foldBwdM f init as
  f b a

@[simp] def foldBwdM_nil [Monad m]
  (f : β → α → m β) (init : β)
  : foldBwdM f init .nil = pure init := rfl

@[simp] def foldBwdM_snoc [Monad m]
  (f : β → α → m β) (init : β)
  (as : Bwd α) (a : α)
  : foldBwdM f init (.snoc as a) = foldBwdM f init as >>= (fun b => f b a) := rfl

@[simp] def foldBwdM_append [Monad m] [LawfulMonad m]
  (f : β → α → m β) (init : β)
  (as bs : Bwd α)
  : foldBwdM f init (as ++ bs) = foldBwdM f init as >>= fun b => foldBwdM f b bs := by
  induction bs <;> simp [foldBwdM, HAppend.hAppend, Append.append] at *
  case snoc bs b ih =>
    simp [ih]
