/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.AnnealedRows
import HCPoly.Provider.Transport.WhitneyRows
import HCPoly.Provider.Transport.TransportMeanDomination
import HCPoly.Provider.Transport.RowDischarge
import HCPoly.Provider.PortableHistory.CheckpointMoment

/-!
# The pathwise majorant family of a target cell

The exhaustion `e.two.grid.whitney.average` dominates the response of a
target cell of the new grid, pathwise, by the weighted responses of its maximal
old-grid filling plus the below-start term carried by the window multiplier.
This file exhibits that majorant as a genuine *family*: measurable, integrable,
symmetric, with its annealed block computed in closed form, and with the
pathwise domination holding at every sample.

The window multiplier controls the below-start cells only almost surely, so the
raw majorant dominates only almost surely.  Domination at every sample is
recovered by modifying the family on a measurable null set: off the set nothing
changes, on the set the family is the response itself.  Every analytic property
passes through the modification by almost-everywhere congruence, and the two
pathwise properties — domination and symmetry — hold by the case split itself.

The centred family of the majorant splits, at every sample of the raw branch,
into the centred filling sum and the centred multiplier term; this is the
decomposition consumed by the combined bound for the transported fluctuations.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {d : ℕ}

/-- **Domination at every sample from domination almost surely.**  A family
dominating another almost surely is modified on a measurable null set into a
family dominating at every sample; the modification is almost surely the
original family, and symmetry survives the case split. -/
theorem exists_pointwise_majorant {P : Measure (CoeffSpace d)}
    {F G : CoeffSpace d → BlockMat d}
    (hdom : ∀ᵐ a ∂P, toFullBlockMat (F a) ≤ toFullBlockMat (G a))
    (hFsym : ∀ a, IsSymmetricBlockMat (F a))
    (hGsym : ∀ a, IsSymmetricBlockMat (G a)) :
    ∃ Gm : CoeffSpace d → BlockMat d,
      (∀ a, toFullBlockMat (F a) ≤ toFullBlockMat (Gm a)) ∧
        (∀ a, IsSymmetricBlockMat (Gm a)) ∧ Gm =ᵐ[P] G := by
  classical
  set S : Set (CoeffSpace d) :=
    {a | ¬ toFullBlockMat (F a) ≤ toFullBlockMat (G a)} with hSdef
  have hS0 : P S = 0 := ae_iff.mp hdom
  have hT0 : P (toMeasurable P S) = 0 := by
    rw [measure_toMeasurable]
    exact hS0
  refine ⟨(toMeasurable P S).piecewise F G, ?_, ?_, ?_⟩
  · intro a
    by_cases h : a ∈ toMeasurable P S
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]
      by_contra hc
      exact h (subset_toMeasurable P S hc)
  · intro a
    by_cases h : a ∈ toMeasurable P S
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact hFsym a
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]
      exact hGsym a
  · have hae : ∀ᵐ a ∂P, a ∉ toMeasurable P S :=
      (measure_eq_zero_iff_ae_notMem (μ := P)).mp hT0
    filter_upwards [hae] with a ha
    rw [Set.piecewise_eq_of_notMem _ _ _ ha]

end

end Transport
end HighContrast
end Homogenization
