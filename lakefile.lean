import Lake
open Lake DSL

require chomsky from git
  "https://github.com/madvorak/chomsky"@"main"

package thue {
  moreServerArgs := #["-DautoImplicit=false"]
}

@[default_target]
lean_lib Thue {
  globs := #[.submodules `Thue] 
  moreLeanArgs := #["-DautoImplicit=false"]
}
