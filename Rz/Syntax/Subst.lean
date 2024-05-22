/-
# Substitution

This file contains a lightweight framework for performing and reasoning
about substitution, inspired by `autosubst`.
-/

universe u v w

/-- Notation typeclass for `α [ σ ]`. -/
class HAct (σ : Type u) (α : Type v) (β : outParam (Type w)) where
  hAct : σ → α → β

/-- Notation typeclass for `σ ; α` -/
class HExtend (σ : Type u) (α : Type v) (δ : outParam (Type w)) where
  hExtend : σ → α → δ

notation α:65 " [ " σ:max " ]" => HAct.hAct σ α
infixl:65 " ; " => HExtend.hExtend

/-
# Renamings
-/

/-- Renamings are represented as functions `Nat → Nat`. -/
def Rn : Type := Nat → Nat

/-- Heterogenous renaming. -/
class HRename (α : Type u) (β : outParam (Type v)) where
  hRename : α → Rn → β

/-- Homogenous renaming. -/
class Rename (α : Type u) where
  rename : α → Rn → α

@[default_instance]
instance instHRename [Rename α] : HRename α α where
  hRename a ρ := Rename.rename a ρ

namespace Rn

@[ext] def ext {ξ ρ : Rn} (h : (x : Nat) → ξ x = ρ x) : ξ = ρ := funext h

/-- Identity renaming. -/
protected def id : Rn := fun x => x

/-- Composition of renamings; performs renames in left-to-right order. -/
protected def comp (ρ : Rn) (σ : Rn) : Rn :=
  fun x => σ (ρ x)

/-- Weaken all variables with `i ≤ x` by `n`. -/
protected def wk (i : Nat) (n : Nat) : Rn :=
  fun x => if x < i then x else x + n

/-- Extend a renaming to operate under `n` additional variables. -/
protected def under (ξ : Rn) (n : Nat) : Rn :=
  fun x =>
    if x < n then
      x
    else
      ξ (x - n) + n

/-- Extend a renaming with a variable. -/
protected def extend (ξ : Rn) (n : Nat) : Rn :=
  fun x =>
  match x with
  | 0 => n
  | x+1 => ξ x

instance : HExtend Rn Nat Rn where
  hExtend := Rn.extend

@[simp] theorem comp_id (ξ : Rn) : Rn.comp ξ Rn.id = ξ := rfl
@[simp] theorem id_comp (ξ : Rn) : Rn.comp Rn.id ξ = ξ := rfl
@[simp] theorem comp_assoc (ξ ρ σ : Rn) : Rn.comp (Rn.comp ξ ρ) σ = Rn.comp ξ (Rn.comp ρ σ) := rfl

@[simp] theorem wk_under (ξ : Rn) (n : Nat) : Rn.comp (Rn.wk 0 n) (Rn.under ξ n) = Rn.comp ξ (Rn.wk 0 n) := by
 simp [Rn.wk, Rn.comp]
 sorry
end Rn

/-
# Substitutions
-/

def Sb (α : Type u) : Type u := Nat → α

class HSubst (α : Type u) (β : Type v) (γ : outParam (Type v)) where
  hSubst : α → Sb β → γ

class Subst (α : Type u) where
  subst : α → Sb α → α

class Var (α : Type u) where
  var : Nat → α

@[default_instance]
instance instHSubst [Subst α] : HSubst α α α where
  hSubst a σ := Subst.subst a σ

@[default_instance]
instance [HRename α β] : HSubst α Nat β where
  hSubst a ρ := HRename.hRename a ρ

@[default_instance]
instance [HSubst α β γ] : HAct α (Sb β) γ where
  hAct a σ := HSubst.hSubst a σ

namespace Sb

variable {α : Type u} {β : Type v}

/-- Identity substitution. -/
def id [Var α] : Sb α := Var.var

/-- Composition of substitutions; performs substitutions in left-to-right order. -/
def comp [HSubst α β γ] (σ : Sb α) (δ : Sb β) : Sb γ :=
  fun x => HSubst.hSubst (σ x) δ

/-- Build a substitution from a renaming. -/
def rn [Var α] (ρ : Rn) : Sb α :=
  fun x => Var.var (ρ x)

/-- Postcompose with a weakening. -/
def shift [HRename α β] (σ : Sb α) : Sb β :=
  fun x => HRename.hRename (σ x) (Rn.wk 0 1)

/-- Extend a substitution to operate under `n` additional variables. -/
def under [Rename α] [Var α] (σ : Sb α) (n : Nat) : Sb α :=
  fun x =>
    if x < n then
      Var.var x
    else
      Rename.rename (σ (x - n)) (Rn.wk 0 n)

/-- Extend a substitution `σ` with a term `e` such that `σ 0 ↦ e`. -/
def extend (σ : Sb α) (e : α) : Sb α :=
  fun x =>
  match x with
  | 0 => e
  | x+1 => σ x

instance : HExtend (Sb α) α (Sb α) where
  hExtend σ e := Sb.extend σ e

end Sb
