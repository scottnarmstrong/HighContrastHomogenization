/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.SmallContrastSchurFamilies
import HCPoly.Provider.Quenched.SmallContrastSkewDagger
import HCPoly.Provider.Quenched.SmallContrastCanonRecenter
import HCPoly.Provider.Initialization.Reference

/-!
# The recentered certificates, all at one block

`hsharp` and `hrec` were being produced at *different* blocks:
the Dagger gives `blockSharp E ≤ E` at `E`, while
`canonicalShear_recentered_eq_zero` gives vanishing shear only at the recentered
`E' := Response.skewBlockCongr (canonicalShear E) E`.  The isotropic squared-base
weak-value bound takes one block, so one of them had to move.

**The Dagger moves, and the law-side API already moves it.**
`coarseEllipticityDagger_recenteredLaw` (`HCPoly.Provider.Quenched.SmallContrastSkewDagger`)
transports the Dagger to

```
CoarseEllipticityDagger (recenteredLaw P hg) gexp (Response.skewBlockCongr g E) Ψ K (recenteredSource S hg)
```

for any skew `g`.  At `g := canonicalShear E` its block is *exactly* `E'`.  So
`hsharp` at `E'` follows from `blockMatLoewnerLE_blockSharp_reference` applied
to the **transported** Dagger, and's missing commutation lemma is not
needed at all: nothing about `blockSharp` under congruence has to be proved,
because the hypothesis that produces it travels instead.

The account then runs at the recentered law throughout and is carried back by
the invariances.
-/

namespace Homogenization.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The four isotropy certificates, all at the recentered block.**  The Dagger
travels with the law; the shear vanishes; the canonical metric — and hence the
adapted geometry — is unchanged. -/
theorem recentered_certificates [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {gexp : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P gexp E Ψ K S)
    (hE : (toFullBlockMat E).PosDef)
    (hg : IsSkewMat (canonicalShear E))
    [IsProbabilityMeasure (recenteredLaw P hg)] :
    HCPoly.Frozen.CoarseEllipticityDagger (recenteredLaw P hg) gexp
        (Response.skewBlockCongr (canonicalShear E) E) Ψ K
        (recenteredSource S hg) ∧
      canonicalShear (Response.skewBlockCongr (canonicalShear E) E) = 0 ∧
      canonicalMetric (Response.skewBlockCongr (canonicalShear E) E) =
        canonicalMetric E ∧
      BlockMatLoewnerLE
        (blockSharp (Response.skewBlockCongr (canonicalShear E) E))
        (Response.skewBlockCongr (canonicalShear E) E) := by
  have hdag' := coarseEllipticityDagger_recenteredLaw hdag hg
  obtain ⟨hshear, hmetric⟩ := canonicalShear_recentered_eq_zero hE
  exact ⟨hdag', hshear, hmetric,
    Initialization.blockMatLoewnerLE_blockSharp_reference hdag'⟩

end

end Homogenization.HighContrast.Quenched
