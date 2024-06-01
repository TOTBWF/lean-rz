import Lean
open Lean Syntax Meta Elab

/-!
# The WHNF Macro

When writing notation macros, it is often useful to have an extensible syntax
class of the form:

```lean
class Syntax (α : Type u) (β : outParam (Type v)) where
  splice : α → Exp β
```

However, this leaves artifacts in the generated terms in the form of `Syntax.splice`
calls. The `whnfI%` elaborator works around this by reducing expressios prefixed by
it so that they are not headed by a typeclass method.
-/

syntax (name := term_whnfI) "whnfI% " ident term:max* : term
syntax (name := term_whnfR) "whnfR% " ident term:max* : term

@[term_elab term_whnfI] def elabWhnfI : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(whnfI% $f $[$args]*) =>
    -- Note: this doesn't seem to add terminfo to `f`
    let some f ← Term.resolveId? f (withInfo := true) | throwUnknownConstant f.getId
    let e ← Term.elabAppArgs f #[] (args.map .stx) expectedType?
      (explicit := false) (ellipsis := false)
    whnfI e
  | _ => throwUnsupportedSyntax

@[term_elab term_whnfR] def elabWhnfR : Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(whnfR% $f $[$args]*) =>
    -- Note: this doesn't seem to add terminfo to `f`
    let some f ← Term.resolveId? f (withInfo := true) | throwUnknownConstant f.getId
    let e ← Term.elabAppArgs f #[] (args.map .stx) expectedType?
      (explicit := false) (ellipsis := false)
    whnfR e
  | _ => throwUnsupportedSyntax
