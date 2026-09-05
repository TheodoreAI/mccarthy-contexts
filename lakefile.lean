import Lake
open Lake DSL

package «mccarthy-contexts» where
  -- Prove2Me elaborates with auto-implicits disabled; matching it here keeps
  -- these sources identical to what the platform verified.
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

-- Each library is built as a set of independent modules rather than through a
-- root file.  `Development/` and `Definitions/`+`Solutions/` are two
-- presentations of the SAME results, so several modules deliberately declare
-- the same names; they compile independently but must not be imported together.

/-- Shared definitions, mirroring the bundles published on Prove2Me. -/
@[default_target]
lean_lib «Definitions» where
  globs := #[.submodules `Definitions]

/-- Platform-shaped proofs: one `theorem solution` per published node. -/
@[default_target]
lean_lib «Solutions» where
  globs := #[.submodules `Solutions]

/-- The readable development, organised by the sections of the paper. -/
@[default_target]
lean_lib «Development» where
  globs := #[.submodules `Development]
