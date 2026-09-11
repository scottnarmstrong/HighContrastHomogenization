/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowMeanEstimates
import HCPoly.Provider.Transport.WindowCellBounds
import HCPoly.Provider.Recurrence.StationarityTransport

/-!
# Finiteness of translated cells across the response window

The retained finite means control every aligned cell at or above the starting
scale.  Below the starting scale, the window enclosure controls each aligned
cell whose center belongs to one of the source cells.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Every aligned subcell of either source cell has an integrable coarse
response.  The below-start branch uses the window multiplier directly, so no
all-scale finite-mean premise is exposed. -/
theorem hasIntegrableCoarseBlock_adaptedCellAt_of_window_telescope
    {P : Measure (CoeffSpace d)} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K Cd : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef) (hqeq : q = roundedGrid jStar m0)
    (hgrid : IsRoundedGrid jStar q)
    {s t : ℤ}
    (hbelow : ∀ k : ℤ, k < jStar → ∀ v : ℤ,
      v = s ∨ v = t → ∀ z ∈ containedCenters q k v,
        adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hblocks : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    {k v : ℤ} (hkv : k ≤ v) (hvt : v ≤ t)
    (hvs : v = s ∨ v = t) {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex q k v) :
    HasIntegrableCoarseBlock P (adaptedCellAt q k w) := by
  by_cases hjk : jStar ≤ k
  · exact Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hstat hgrid hjk
      (hblocks k hjk (hkv.trans hvt)).1 w
  · have hkj : k < jStar := lt_of_not_ge hjk
    have hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
    have hcenter : adaptedCellCenter q k w ∈ containedCenters q k v :=
      ⟨⟨w, rfl⟩, (mem_alignedIndex_iff hq hkv).mp hw⟩
    have hcont : adaptedCellTranslate q k (adaptedCellCenter q k w) ⊆
        centeredCube d M := hbelow k hkj v hvs _ hcenter
    subst q
    have hint := Transport.hasIntegrableCoarseBlock_adaptedCellTranslate
      hY hm0 hgrid k (adaptedCellCenter (roundedGrid jStar m0) k w) hcont
    simpa only [← Transport.adaptedCellAt_eq_adaptedCellTranslate] using hint

end

end Homogenization.HighContrast.Response
