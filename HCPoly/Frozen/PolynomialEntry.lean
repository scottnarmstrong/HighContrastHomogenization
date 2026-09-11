/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup
import HCPoly.Provider.Entry.EntryAssembly
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Theorem `t.polynomial.entry`

Polynomial entry with a random source scale.  The calibration triple
`(c_sc, δ_0, c_end)` is quantified with exactly the properties required by the
choice of the small-contrast threshold in `ss.algebraic.convergence`.  The
conclusion is the printed one: an entry generation `m_ent` bounded by the stated
ceiling, at which the annealed contrast is within `c_*` of one, together with
the polynomial bound on `3^{m_ent}`.  The
binder order carries the stated constant independence: `c_*` before `g`; `C`
before the gauge, growth witness, source variable, reference block, law, and
aspect ratio.

The coefficient fields are uniformly elliptic almost everywhere, with ellipticity
constants belonging to the field and entering no estimate;
`e.qualitative.ellipticity` follows from this, and every quantitative object
below — `Π`, the gauge and its growth witness, `Θ_m`, and every dimensional
constant — is independent of them.
-/

/-- **Theorem `t.polynomial.entry`**: polynomial entry with a
random source scale. -/
theorem HCPoly.Frozen.polynomial_entry_random_source
    (d : ℕ) (hd : 2 ≤ d)
    (cSc δ₀ cEnd : ℝ) (hcSc : 0 < cSc) (hδ₀ : δ₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hcEnd : 0 < cEnd)
    (hcal : (1 + δ₀) ^ 2 * (1 + cEnd) ≤ 1 + cSc) :
    ∃ cStar : ℝ, cStar ∈ Set.Ioc 0 (min cSc cEnd) ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C : ℝ, 0 < C ∧
          ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
            (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
            MeasureTheory.IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
            ∃ mEnt : ℕ,
              (mEnt : ℤ) ≤
                ⌈C * Real.logb 3
                  (2 + Homogenization.HighContrast.aspectRatio E * K)⌉ ∧
              Homogenization.HighContrast.annealedContrast P (mEnt : ℤ) - 1 ≤ cStar ∧
              (3 : ℝ) ^ (mEnt : ℕ) ≤
                3 * (2 + Homogenization.HighContrast.aspectRatio E * K) ^ C
    := by
  exact Homogenization.HighContrast.Entry.polynomial_entry_assembly
    d hd cSc δ₀ cEnd hcSc hδ₀ hcEnd hcal
