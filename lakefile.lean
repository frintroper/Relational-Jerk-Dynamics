import Lake
open Lake DSL

package «RelationalJerkDynamics» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «RJD» where
  globs := #[.submodules `RJD]
