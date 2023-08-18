import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package thue {
  moreServerArgs := #["-DautoImplicit=false"]
}

@[default_target]
lean_lib Thue {
  globs := #[.submodules `Thue] 
  moreLeanArgs := #["-DautoImplicit=false"]
}
