import Rz.Data.Idx

/-!
# Inductive Vectors
-/

universe u v w

variable {α β : Type u}

inductive Vec (α : Type u) : Nat → Type u where
| nil : Vec α 0
| cons : {n : Nat} → α → Vec α n → Vec α (n + 1)

namespace Vec

@[simp] def get {n : Nat} : (as : Vec α n) → Idx n → α
| .cons a as, .zero => a
| .cons _ as, .succ i => get as i

@[simp] def ofList : (as : List α) → Vec α as.length
| .nil => .nil
| .cons a as => .cons a (ofList as)

@[simp] def toList {n : Nat} : Vec α n → List α
| .nil => .nil
| .cons a as => .cons a (toList as)

@[simp] def replicate (n : Nat) (a : α) : Vec α n :=
match n with
| 0 => .nil
| n+1 => .cons a (replicate n a)

instance {xs : List α} : CoeDep (List α) xs (Vec α xs.length) where
  coe := ofList xs

instance {n : Nat} : CoeOut (Vec α n) (List α) where
  coe xs := toList xs

instance {n : Nat} : Membership α (Vec α n) where
  mem a as := a ∈ as.toList
