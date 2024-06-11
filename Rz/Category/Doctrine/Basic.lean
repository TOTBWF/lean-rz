import Lean

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.Category.Preord

import Rz.Category.Cartesian

/-!
# Doctrines
-/

universe w v u

namespace CategoryTheory

/-- A `Doctrine` over a cartesian category `C` is a contravariant functor into the category of posets.
    We opt to define doctrines as a bespoke typeclass to make it easier to extend to regular, coherent,
    first order, etc. This also has the additional benefit of not gunking up our goals with `op`. -/
class Doctrine {C : Type u} (P : C → Type w) [Category.{v} C] [Cartesian C] where
  /-- Every fibre of a doctrine carries the structure of a preorder. -/
  poset : {Γ : C} → PartialOrder (P Γ)
  /-- A doctrine is equipped with an action of substitution. -/
  sub : {Γ Δ : C} → (Δ ⟶ Γ) → P Γ → P Δ
  /-- Substitution is monotone. -/
  sub_monotone : {Γ Δ : C} → (σ : Δ ⟶ Γ) → Monotone (sub σ)
  /-- Substitution along identity is identity. -/
  sub_id : {Γ : C} → (Φ : P Γ) → sub (𝟙 Γ) Φ = Φ
  /-- Substitution along composites is itself a composite. -/
  sub_comp : {Γ Δ Ψ : C} → (σ : Ψ ⟶ Δ) → (δ : Δ ⟶ Γ) → (Φ : P Γ) → sub (σ ≫ δ) Φ = sub σ (sub δ Φ)

notation:70 Φ:71 "^*" σ:71 => Doctrine.sub σ Φ

-- notation:max Φ:max "^* " σ:max => Doctrine.sub σ Φ

variable {C : Type*} [Category C] [Cartesian C]
variable {P : C → Type w} [Doctrine P]

instance {Γ Δ} : GetElem (P Δ) (Γ ⟶ Δ) (P Γ) (fun _ _ => ⊤) where
  getElem φ σ _ := Doctrine.sub σ φ

instance instPosetDoctrine {Γ : C} : PartialOrder (P Γ) := Doctrine.poset
export Doctrine (sub_monotone sub_id sub_comp)

attribute [simp] sub_comp sub_id

/-!
# Notation
-/

open Lean Elab Syntax

declare_syntax_cat doctrine
syntax:max ident : doctrine
syntax:max doctrine:max "[" withoutPosition(term:min) "]" : doctrine
syntax:max "(" doctrine:min ")" : doctrine
syntax:max doctrine:max "(" term,+ ")" : doctrine
syntax "$(" term:min ")" : doctrine

syntax "«doctrine» " doctrine : term

#check BinderInfo.default

macro_rules
| `(«doctrine» $x:ident) => `($x)
| `(«doctrine» $p[$σ:term]) => `((«doctrine» $p)^*($σ))
| `(«doctrine» $p($tms:term,*)) => do
  let tms := tms.getElems
  let (res, _ ) ← tms.foldrM
    (fun tm (acc, n) => do
      let shifted ← (tms.size - n - 1).foldM (fun _ s => `(shift _ $s)) tm
      let applied ← `(($acc)^*(inst $shifted))
      pure (applied , n + 1))
    (← `(«doctrine» $p), 0)
  pure res
| `(«doctrine» ($p)) => `((«doctrine» $p))
| `(«doctrine» $($tm)) => `($tm)

syntax term " ⊨ " term " | " doctrine:min " ⊢ " doctrine:min : term

macro_rules
| `($P ⊨ $ctx | $p ⊢ $q) => `((Doctrine.poset (P := $P) (Γ := $ctx)).le («doctrine» $p) («doctrine» $q))

/-!
# Automation
-/

syntax "doctrine" : tactic

macro_rules
| `(tactic| doctrine) =>
  `(tactic| simp only [←sub_comp]; simp [-sub_comp]; simp only [sub_comp])

/-!
# Commuting substitutions
-/

section Substitutions

class VarComm {Γ Δ : C} (σ : Γ ⟶ Δ) (δ : outParam (Γ ⟶ Δ)) where
  var_comm : σ = δ

/-- Class that governs commutation of substitutions. -/
class SubComm {Γ Δ : C} (φ : P Δ) (σ : Γ ⟶ Δ) (ψ : outParam (P Γ)) where
  sub_comm : φ^*σ = ψ

lemma sub_comm
    {Γ Δ : C} {φ : P Δ} {ψ : P Γ}
    (σ : Γ ⟶ Δ)
    [SubComm φ σ ψ]
    : φ^*σ = ψ := SubComm.sub_comm

lemma sub_expand
    {Γ Δ : C} {ψ : P Γ}
    (φ : P Δ)
    (σ : Γ ⟶ Δ)
    [SubComm φ σ ψ]
    : ψ = φ^*σ := symm SubComm.sub_comm

@[default_instance]
instance (priority := 0) {Γ Δ : C} {σ : Γ ⟶ Δ} : VarComm σ σ where
  var_comm := rfl

@[default_instance]
instance (priority := 0) {Γ Δ : C} {φ : P Δ} {σ : Γ ⟶ Δ} : SubComm φ σ (φ^*σ) where
  sub_comm := rfl


/-!
## Commuting variables
-/

instance
    {Γ Δ X Y : C} {σ : Γ ⟶ Δ} {y : Δ ⟶ Y} {y' : Γ ⟶ Y}
    [V : VarComm (σ ≫ y) y']
    : VarComm (keep σ ≫ shift X y) (shift X y') where
  var_comm := by
    simp [keep, shift, V.var_comm]

instance
    {Γ X : C} {x : Γ ⟶ X}
    : VarComm (inst x ≫ var X) x where
  var_comm := by
    simp [inst, var]

instance
    {Γ Δ X : C} {σ : Γ ⟶ Δ}
    : VarComm (keep σ ≫ var X) (var X) where
  var_comm := by
    simp [keep, var]


instance
    {Γ X Y : C} {x : Γ ⟶ X} {y : Γ ⟶ Y}
    : VarComm (inst x ≫ shift X y) y where
  var_comm := by
    simp [inst, shift]

/-!
## Instantiation
-/

instance
    {Γ X : C} {φ : P X} {x : Γ ⟶ X}
    : SubComm (φ^*(var X)) (inst x) (φ^*x) where
  sub_comm := by
    simp [←sub_comp, var, inst]

instance
    {Γ X Y : C} {φ : P X} {x : Γ ⟶ X} {y : Γ ⟶ Y}
    : SubComm (φ^*(shift Y x)) (inst y) (φ^*x) where
  sub_comm := by
    simp [←sub_comp, shift, inst]

instance
    {Γ X} {φ : P ((Γ ⨯ X) ⨯ X)} (x : Γ ⟶ X)
    : SubComm (φ^*(contr X)) (inst x) ((φ^*(inst (shift X x)))^*(inst x)) where
  sub_comm := by
    simp [←sub_comp, shift, inst, contr]

instance
    {Γ X : C} {φ : P Γ} {x : Γ ⟶ X}
    : SubComm (φ^*(wk X)) (inst x) φ where
  sub_comm := by
    simp [←sub_comp, wk, inst]

-- HACK: This instance is not very general.
instance
    {Γ X : C} {φ : P (Γ ⨯ X)} {x : Γ ⟶ X}
    : SubComm (φ^*(keep (wk X))) (inst (shift X x)) ((φ^*(inst x))^*(wk X)) where
  sub_comm := by
    simp [←sub_comp, keep, wk, inst, shift]

/-!
## Contraction
-/
instance
    {Γ X : C} {φ : P (Γ ⨯ X)}
    : SubComm (φ^*(wk X)) (contr X) φ where
  sub_comm := by
    simp [←sub_comp, wk, contr]

instance
    {Γ X : C} {φ : P X}
    : SubComm (φ^*(var X)) (contr (Γ := Γ) X) (φ^*(var X)) where
  sub_comm := by
    simp [←sub_comp, var, contr]

instance
    {Γ X : C} {φ : P X}
    : SubComm (φ^*(shift X (var X))) (contr (Γ := Γ) X) (φ^*(var X)) where
  sub_comm := by
    simp [←sub_comp, var, shift, contr]

instance
    {Γ X : C} {φ : P (Γ ⨯ X)}
    : SubComm (φ^*(keep (wk X))) (contr X) φ where
  sub_comm := by
    simp [←sub_comp, keep, wk, contr]

instance
    {Γ Δ X : C} {φ : P ((Δ ⨯ X) ⨯ X)} {σ : Γ ⟶ Δ} {ψ : P (Δ ⨯ X)}
    [S : SubComm φ (contr X) ψ]
    : SubComm (φ^*(keep (keep σ))) (contr X) (ψ^*(keep σ)) where
  sub_comm := by
    simp [←sub_comp, keep, contr]
    rw [←S.sub_comm]
    simp [←sub_comp, contr]

/-!
## Weakenings
-/

instance (priority := low)
    {Γ Δ X : C} {φ : P Δ} {σ : Γ ⟶ Δ} {ψ : P (Δ ⨯ X)}
    [S : SubComm φ (wk X) ψ]
    : SubComm (φ^*σ) (wk X) (ψ^*(keep σ)) where
  sub_comm := by
    rw [←S.sub_comm]
    simp [←sub_comp, keep, wk]

/-!
## Fallbacks
-/

instance (priority := low)
    {Γ Δ X : C} {φ : P (Δ ⨯ X)} {σ : Γ ⟶ Δ} {x : Δ ⟶ X} {x' : Γ ⟶ X} {ψ : P (Γ ⨯ X)}
    [S : SubComm φ (keep σ) ψ] [V : VarComm (σ ≫ x) x']
    : SubComm (φ^*(inst x)) σ (ψ^*(inst x')) where
  sub_comm := by
    simp [←sub_comp, inst]
    rw [←S.sub_comm, ←V.var_comm]
    simp [←sub_comp, keep]

/-!
# Inference Rules
-/

def hyp
    {Γ Δ : C} {Φ ψ : P Γ} {ξ : P Δ} {σ : Γ ⟶ Δ}
    (h : Φ ≤ ξ^*σ)
    [S : SubComm ξ σ ψ]
    : Φ ≤ ψ := by rwa [←S.sub_comm]


def begin
    {Γ Δ : C} {Φ ψ : P Γ} {ξ : P Δ} {σ : Γ ⟶ Δ}
    (h : Φ ≤ ψ)
    [S : SubComm ξ σ ψ]
    : Φ ≤ ξ^* σ := by rwa [S.sub_comm]


lemma «Structural».subst
  {Γ Δ : C} {φ ψ : P Δ} {ξ τ : P Γ}
  (σ : Γ ⟶ Δ)
  [L : SubComm φ σ ξ] [R : SubComm ψ σ τ]
  (h : P ⊨ Δ | φ ⊢ ψ)
  : P ⊨ Γ | ξ ⊢ τ := by
  rw [←L.sub_comm, ←R.sub_comm]
  apply sub_monotone
  exact h
