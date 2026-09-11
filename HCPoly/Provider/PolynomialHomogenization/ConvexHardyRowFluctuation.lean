/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.FractionalMeanOscillation
import HCPoly.Analytic.TestNorms
import HCPoly.Provider.PolynomialHomogenization.CountableDisjointDiagonal
import HCPoly.Provider.PolynomialHomogenization.ConvexWhitneyGeometry

/-!
# Fractional fluctuation control on one Whitney row

Every identity-grid cell in a fixed Whitney row has the same side length.  The
fractional Poincare estimate on each cell therefore has one common coefficient:
after weighting by the inverse fractional scale, the cell volume and diameter
cancel exactly.  Pairwise disjointness then lets the diagonal product energies
sum into the energy of the containing domain.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Function

noncomputable section

variable {d : ℕ}

/-- The fractional Gagliardo kernel used to aggregate diagonal cell energies. -/
def whitneyRowFractionalKernel (s : ℝ) (F : Vec d → Vec d)
    (z : Vec d × Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal
    (vecNormSq (F z.1 - F z.2) /
      Real.sqrt (vecNormSq (z.1 - z.2)) ^ ((d : ℝ) + 2 * s))

private theorem aemeasurable_whitneyRowFractionalKernel
    {V : Set (Vec d)} {F : Vec d → Vec d}
    (hF : Integrable F (volume.restrict V)) {s : ℝ} (hs : 0 ≤ s) :
    AEMeasurable (whitneyRowFractionalKernel s F)
      ((volume.prod volume).restrict (V ×ˢ V)) := by
  rw [← Measure.prod_restrict]
  have hsub : AEMeasurable (fun z : Vec d × Vec d => F z.1 - F z.2)
      ((volume.restrict V).prod (volume.restrict V)) :=
    hF.aestronglyMeasurable.aemeasurable.comp_fst.sub
      hF.aestronglyMeasurable.aemeasurable.comp_snd
  have hnum : AEMeasurable
      (fun z : Vec d × Vec d => vecNormSq (F z.1 - F z.2))
      ((volume.restrict V).prod (volume.restrict V)) :=
    continuous_vecNormSq.measurable.comp_aemeasurable hsub
  have hp : 0 ≤ (d : ℝ) + 2 * s := by
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  have hdist : Continuous
      (fun z : Vec d × Vec d => Real.sqrt (vecNormSq (z.1 - z.2))) :=
    (continuous_vecNormSq.comp (continuous_fst.sub continuous_snd)).sqrt
  have hden : Measurable
      (fun z : Vec d × Vec d =>
        Real.sqrt (vecNormSq (z.1 - z.2)) ^ ((d : ℝ) + 2 * s)) :=
    (hdist.rpow_const fun _ => Or.inr hp).measurable
  exact (hnum.div hden.aemeasurable).ennreal_ofReal

end

end HighContrast
end Homogenization
