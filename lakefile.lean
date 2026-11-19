import Lake
open Lake DSL

package «RelationalJerkDynamics» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com" @ "v4.12.0"

@[default_target]
lean_lib «RJD» where
  globs := #[.submodules `RJD]
