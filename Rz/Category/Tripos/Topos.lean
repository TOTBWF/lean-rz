import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

import Rz.Category.PreHeyt
import Rz.Category.Tripos

/-!
# The tripos-to-topos construction.
-/

open CategoryTheory Opposite CategoricalLogic

universe u v w

variable {P : Type u ᵒᵖ ⥤ PreHeyt.{v}} [Tripos P]

open UniversalDoctrine


abbrev wk
    {Γ : Type u}
    (X : Type u)
    : op Γ ⟶ op (Γ × X) := op Prod.fst

abbrev var
    {Γ : Type u}
    (X : Type u)
    : op X ⟶ op (Γ × X) := op Prod.snd

abbrev shift
    {Γ X : Type u}
    (Y : Type u)
    (x : op X ⟶ op Γ)
    : op X ⟶ op (Γ × Y) := x ≫ wk Y

-- @[reducible]
-- instance {Γ X : Type u} : OfNat (op X ⟶ op (Γ × X)) 0 where
--   ofNat := op Prod.snd

-- @[reducible]
-- instance {Γ X Y : Type u} {n : Nat} [N : OfNat (op X ⟶ op Γ) n] : OfNat (op X ⟶ op (Γ × Y)) (n + 1) where
--   ofNat := N.ofNat ≫ wk Y

def inst
    {Γ X : Type u}
    (x : op X ⟶ op Γ)
    : op (Γ × X) ⟶ op Γ := op (fun ctx => (ctx, x.unop ctx))

def extend
    {Γ Δ X : Type u}
    (σ : op Δ ⟶ op Γ)
    (x : op X ⟶ op Γ)
    : op (Δ × X) ⟶ op Γ := op (fun ctx => (σ.unop ctx, x.unop ctx))

def keep
    {Γ Δ X : Type u}
    (σ : op Δ ⟶ op Γ)
  : op (Δ × X) ⟶ op (Γ × X) := op (fun ctx => (σ.unop ctx.fst, ctx.snd))

-- lemma fst_keep
--     {Γ Δ X : Type u}
--     (σ : op Δ ⟶ op Γ)
--     (Φ : P.obj (op Δ))
--     : P.map (wk X) (P.map σ Φ) = P.map (keep σ) (P.map (wk X) Φ) := by
--   sorry

lemma wk_keep
    {Γ Δ X : Type u} {σ : op Δ ⟶ op Γ}
    : wk X ≫ keep σ = σ ≫ wk X := by
  sorry

notation "∏" X ", " Φ => UniversalDoctrine.Forall (Prod.fst (β := X)) Φ

/-- Push a substitution `σ` through a term. -/
class SubReduce {Γ Δ : Type u} (Φ : P.obj (op Δ)) (σ : op Δ ⟶ op Γ) (Ψ : outParam (P.obj (op Γ))) where
  reduce : P.map σ Φ ≤ Ψ

/-- Pull a substitution `σ` out of a term. -/
class SubExpand {Γ Δ : Type u} (Φ : outParam (P.obj (op Γ))) (σ : op Δ ⟶ op Γ) (Ψ : P.obj (op Δ)) where
  expand : Φ ≤ P.map σ Ψ

/-- Simplify a substitution. -/
class SubSimp {Γ Δ : Type u} (σ : op Δ ⟶ op Γ) (δ : outParam (op Δ ⟶ op Γ)) where
  simp : σ = δ

section Substitution

open SubReduce SubExpand

@[default_instance]
instance {Γ Δ : Type u} {σ : op Δ ⟶ op Γ} : SubSimp σ σ where
  simp := rfl

instance
    {Γ Δ Ψ X : Type u} {δ : op Ψ ⟶ op Δ} {x : op X ⟶ op Δ} {σ : op Δ ⟶ op Γ} {ρ : op Ψ ⟶ op Γ} {x' : op X ⟶ op Γ}
    [S : SubSimp (δ ≫ σ) ρ] [S' : SubSimp (x ≫ σ) x']
    : SubSimp (extend δ x ≫ σ) (extend ρ x') where
  simp := by
    rw [←S.simp, ←S'.simp]
    congr

instance
    {Γ Δ X : Type u} {σ : op Δ ⟶ op Γ}
    : SubSimp (var X ≫ keep σ) (var X) where
  simp := by congr

instance
    {Γ X : Type u} {x : op X ⟶ op Γ}
    : SubSimp (var X ≫ inst x) x where
  simp := by congr

instance
    {Γ Δ X : Type u} {σ : op Δ ⟶ op Γ} {x : op X ⟶ op Γ}
    : SubSimp (shift X σ ≫ inst x) σ where
  simp := by congr

instance
    {Γ Δ Ψ X : Type u} {δ : op Ψ ⟶ op Δ} {σ : op Δ ⟶ op Γ} {ρ : op Ψ ⟶ op Γ}
    [S : SubSimp (δ ≫ σ) ρ]
    : SubSimp (shift X δ ≫ keep σ) (shift X ρ) where
  simp := by
    rw [←S.simp]
    simp [wk_keep]


@[default_instance]
instance {Γ Δ : Type u} {σ δ : op Δ ⟶ op Γ} {Φ : P.obj (op Δ)} [S : SubSimp σ δ] : SubReduce Φ σ (P.map δ Φ) where
  reduce := by rw [S.simp]

@[default_instance]
instance (priority := low) subExpandDefault {Γ Δ : Type u} {σ δ : op Δ ⟶ op Γ} {Φ : P.obj (op Δ)} [S : SubSimp δ σ] : SubExpand (P.map σ Φ) δ Φ where
  expand := by rw [S.simp]

instance
    {Γ Δ Ψ : Type u} {σ : op Δ ⟶ op Γ} {δ : op Ψ ⟶ op Δ} {Φ : P.obj (op Ψ)} {ξ : P.obj (op Γ)}
    [R : SubReduce Φ (δ ≫ σ) ξ]
    : SubReduce (P.map δ Φ) σ ξ where
  reduce := by
    apply le_trans _ R.reduce
    rw [P.map_comp]
    rfl

instance subExpandMap
    {Γ Δ Ψ : Type u} {σ : op Δ ⟶ op Γ} {δ : op Ψ ⟶ op Δ} {Φ : P.obj (op Ψ)} {ξ : P.obj (op Γ)}
    [E : SubExpand ξ (δ ≫ σ) Φ]
    : SubExpand ξ σ (P.map δ Φ) where
  expand := by
    apply le_trans E.expand _
    rw [P.map_comp]
    rfl

instance subReduceImp
    {Γ Δ : Type u} {Φ Ψ : P.obj (op Δ)} {ξ Ξ : P.obj (op Γ)} {σ : op Δ ⟶ op Γ}
    [SubExpand ξ σ Φ] [SubReduce Ψ σ Ξ]
    : SubReduce (Φ ⇨ Ψ) σ (ξ ⇨ Ξ) where
  reduce :=
    le_trans (map_le_himp _ _ _) (Pre.himp_mono expand reduce)

instance
    {Γ Δ : Type u} {Φ Ψ : P.obj (op Δ)} {ξ Ξ : P.obj (op Γ)} {σ : op Δ ⟶ op Γ}
    [SubReduce Φ σ ξ] [SubExpand Ξ σ Ψ]
    : SubExpand (ξ ⇨ Ξ) σ (Φ ⇨ Ψ) where
  expand :=
    le_trans (Pre.himp_mono reduce expand) (himp_le_map _ _ _)


instance {Γ Δ X : Type u} {Φ : P.obj (op (Δ × X))} {ξ : P.obj (op (Γ × X))} {σ : op Δ ⟶ op Γ} [S : SubReduce Φ (keep σ) ξ] : SubReduce (∏ X, Φ) σ (∏ X, ξ) where
  reduce := by sorry
    -- rw [←forall_right_adj, fst_keep]
    -- refine le_trans ?_ S.reduce
    -- apply monotone
    -- rw [forall_right_adj]

end Substitution
-- instance {Γ Δ X : Type u} {Φ : P.obj (op (Δ × X))} {ξ : P.obj (op (Γ × X))} {σ : op Δ ⟶ op Γ} [S : SubReduce (P.map (keep σ) Φ) ξ] : SubReduce (P.map σ (∏ X, Φ)) (∏ X, ξ) where
--   sub := by

-- Congruence rules

def forall_intro
  {Γ X : Type u} {Φ : P.obj (op Γ)} {Ψ : P.obj (op (Γ × X))}
  (h : P.map (wk X) Φ ≤ Ψ)
  : Φ ≤ ∏ X, Ψ := sorry

def forall_elim
  {Γ X : Type u} {Φ ξ : P.obj (op Γ)} {Ψ : P.obj (op (Γ × X))}
  (h : Φ ≤ ∏ X, Ψ)
  (x : op X ⟶ op Γ)
  [SubReduce Ψ (inst x) ξ]
  : Φ ≤ ξ := sorry

elab "tapply" term term* : tactic =>
    Lean.Elab.Tactic.withMainContext do
    return

def imp_elim
    {Γ : Type u} {Φ Ψ ξ : P.obj (op Γ)}
    (h : Φ ≤ Ψ ⇨ ξ)
    (h' : Φ ≤ Ψ)
    : Φ ≤ ξ := by sorry

open Prod

variable (P) in
class InternalPER (X : Type u) where
  Rel : P.obj (op (X × X))
  symm : {Γ : Type u} → {Φ : P.obj (op Γ)} → Φ ≤ ∏ X, ∏ X, P.map (extend (shift X (var X)) (var X)) Rel ⇨ P.map (extend (var X) (shift X (var X))) Rel
  trans : {Γ : Type u} → {Φ : P.obj (op Γ)} → Φ ≤ ∏ X, ∏ X, ∏ X, P.map (extend (shift X (shift X (var X))) (shift X (var X))) Rel ⇨ P.map (extend (shift X (var X)) (var X)) Rel ⇨ P.map (extend (shift X (shift X (var X))) (var X)) Rel

namespace InternalPER

variable {Γ X : Type u} [A : InternalPER P X]

def refl_of_rel_left
    {Γ : Type u} {Φ : P.obj (op Γ)}
    (x y : op X ⟶ op Γ)
    (h : Φ ≤ P.map (extend x y) Rel)
    : Φ ≤ P.map (extend x x) Rel :=
  imp_elim (imp_elim (forall_elim (forall_elim (forall_elim A.trans x) y) x) h)
    (imp_elim (forall_elim (forall_elim A.symm x) y) h)


end InternalPER
