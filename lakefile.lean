import Lake
open Lake DSL

package «SocialChoiceAtlas» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.15.0"

@[default_target]
lean_lib «SocialChoiceAtlas» where
  globs := #[.submodules `SocialChoiceAtlas]
