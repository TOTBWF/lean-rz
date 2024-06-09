import Lean
import Batteries.Lean.NameMapAttribute

open Lean Meta Elab Term

universe u

/-!
# The Simp typeclass

The `Simp` typeclass allows us to have a series of blessed simplification rules that we can
use at the type level. The canonical example here is the `forall_elim` rule for in a tripos:

```lean
def forall_elim
  {Γ X : Type u} {Φ ξ : P.obj (op Γ)} {Ψ : P.obj (op (Γ × X))}
  (h : Φ ≤ ∏ X, Ψ)
  (x : op X ⟶ op Γ)
  [SubReduce Ψ (inst x) ξ]
  : Φ ≤ ξ := sorry
```
-/


/-- The `Simp` class gives us access to simplification lemmas when writing type signatures. -/
class Simp {α : Type u} (x : α) (y : outParam α) where
  simplify : x = y

/-- Fallback simplification instance; when we are out of instances to chain, use `rfl`. -/
@[default_instance]
instance (priority := 0) instDefaultSimp {α : Type u} {x : α} : Simp x x where
  simplify := rfl

section SimpClass
syntax (name := simp_class) "simp_class" : attr

-- def getDeclEq (declInfo : ConstantInfo) : MetaM (Array Expr × Expr × Expr × Expr) := do
--     let declTy := declInfo.type
--     let (tele, _, declTy) ← withDefault <| forallMetaTelescopeReducing declTy
--     let failNotEq := throwError
--       "@[simp_class] attribute only applies to theorems proving x = y, got {declTy}"
--     let some (ty, lhs, rhs) := declTy.eq? | failNotEq
--     pure (tele, ty, lhs, rhs)

initialize registerTraceClass `simp_class

initialize registerBuiltinAttribute {
  name := `simp_class
  descr := "Generate a `Simp` instance for this lemma."
  add := fun declName _stx _kind => MetaM.run' do
    -- Ensure that we are looking at a goal of the form 'x = y'.
    let declInfo ← getConstInfo declName
    forallTelescope declInfo.type fun mvars ty => do
    let some (ty, lhs, rhs) := ty.eq? | throwError "@[simp_class] attribute only applies to theorems proving x = y, got {ty}"
    let simpDefnName := declName.mkStr "instSimpClass"
    let lvl ← getDecLevel ty

    -- Construct an instance with type `{tele*} {r : ty} [Simp rhs r] : Simp lhs r`
    Term.TermElabM.run' <| do
      let instTp ←
        mkForallFVars mvars
        <| mkForall `r BinderInfo.implicit ty
        <| mkForall `inst BinderInfo.instImplicit (mkAppN (.const ``Simp [lvl]) #[ty, rhs, .bvar 0])
        <| mkAppN (.const ``Simp [lvl]) #[ty, lhs, .bvar 1]
      trace[simp_class] "Instance type: {instTp}"

      let instImpl ← Term.elabTerm (← `(term| Simp.mk (trans $(mkIdent declName) Simp.simplify))) instTp
      trace[simp_class] "Instance impl: {instImpl}"

      addAndCompile <| Declaration.defnDecl {
        name := simpDefnName
        levelParams := declInfo.levelParams
        type := ← instantiateMVars instTp
        value := ← instantiateMVars instImpl
        hints := ReducibilityHints.abbrev
        safety := DefinitionSafety.safe
      }
    addInstance simpDefnName AttributeKind.global 100
}
end SimpClass
