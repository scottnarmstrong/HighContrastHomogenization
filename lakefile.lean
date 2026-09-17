import Lake

open Lake DSL

package «HighContrastHomogenization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

require «CoarseGraining» from git
  "https://github.com/scottnarmstrong/CoarseGraining" @ "11d802f3f6023f40568cc4511f55cf251aaa974f"

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

