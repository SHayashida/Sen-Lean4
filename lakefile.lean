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
  -- Build only the library root (and its imports) by default.
  -- SAT/LRAT modules like `SocialChoiceAtlas.Sen.BaseCase24.SATSenGenerated` are optional
  -- and can be built explicitly when a certificate is available.
  globs := #[`SocialChoiceAtlas]
