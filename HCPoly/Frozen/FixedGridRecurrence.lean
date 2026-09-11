/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.Moments
import HCPoly.Provider.Recurrence.RecurrenceAssembly

/-!
# Proposition `p.fixed.geometry.parent.child.recurrence`

The fixed-grid recurrence: on one deterministic rounded adapted grid, at scales
at or above the grid's alignment, the centered normalized moment at the parent
scale is controlled by a geometric contraction of the moment at the child scale,
transported by the determinant increment, plus the increment's own gain.

The alignment of the grid is an explicit binder.  A rounded adapted grid carries
an alignment parameter `ℓ ≥ k_0(d)`, and the aligned subdivision of the
variational coarse block of `s.introduction` — the property that the parent
cell is partitioned by exactly `3^{d(p-j)}` child cells with integral
translation vectors, which is what carries stationarity into the averaging
step — holds only at scales at or above that alignment.  The printed hypothesis
`j ≥ k_0(d)` is the special case `ℓ = k_0(d)`; the consumers of this proposition
read it at the alignment `j_*` of the source window.

The moments are those of the mixed norm `‖·‖_{L^Q(S_Q)}`, valued in `ℝ≥0∞`;
finiteness of the two means and of the two moments is the printed hypothesis
that the means and the moments are finite.
-/

theorem HCPoly.Frozen.fixed_grid_recurrence
    (d : ℕ) (hd : 2 ≤ d) (Q : ℕ) (hQ : 2 ≤ Q) (hQeven : Even Q) :
    ∃ Crec : ℝ, 0 < Crec ∧
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d)),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        ∀ (l : ℤ) (q : Homogenization.Mat d),
          Homogenization.HighContrast.IsRoundedGrid l q →
          ∀ j h : ℤ, l ≤ j → 1 ≤ h →
            Homogenization.Book.Ch02.BlockPosDef
              (Homogenization.HighContrast.adaptedMean P q j) →
            Homogenization.Book.Ch02.BlockPosDef
              (Homogenization.HighContrast.adaptedMean P q (j + h)) →
            Homogenization.HighContrast.HasFiniteAdaptedMean P q j →
            Homogenization.HighContrast.HasFiniteAdaptedMean P q (j + h) →
            Homogenization.HighContrast.centeredMoment P (Q : ℝ) q j ≠ ⊤ →
            Homogenization.HighContrast.centeredMoment P (Q : ℝ) q (j + h) ≠ ⊤ →
            0 ≤ Homogenization.HighContrast.detIncrement P q j (j + h) ∧
              Homogenization.HighContrast.centeredMoment P (Q : ℝ) q (j + h) ≤
                ENNReal.ofReal
                    (Crec * (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) *
                      Real.exp
                        (Homogenization.HighContrast.detIncrement P q j (j + h))) *
                  Homogenization.HighContrast.centeredMoment P (Q : ℝ) q j +
                ENNReal.ofReal
                  (Crec *
                    Homogenization.HighContrast.gainPhi (Q : ℝ)
                      (Homogenization.HighContrast.detIncrement P q j (j + h)))
    := by
  exact Homogenization.HighContrast.Recurrence.fixed_grid_recurrence_assembly d hd Q hQ hQeven
