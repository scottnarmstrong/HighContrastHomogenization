import Lake

open Lake DSL

package «HighContrastHomogenization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

require «CoarseGraining» from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4"

/-- The Mathlib-only comparator challenges and their solutions.  Deliberately
**not** a default target: it builds only on demand (`lake build HCPolyAudit`), so the
ordinary project build is unchanged. -/
lean_lib «HCPolyAudit» where
  globs := #[.submodules `HCPolyAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «HCPoly» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

