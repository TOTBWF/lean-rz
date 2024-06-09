import Lake
open Lake DSL

package «lean-rz» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib «Rz» where
