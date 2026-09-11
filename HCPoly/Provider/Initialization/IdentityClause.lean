/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.IdentityConstant
import HCPoly.Provider.Initialization.IdentityTransport

/-!
# Identity-grid initialization clause

All identity-grid conclusions are assembled here.  The only reference input
left exposed is the upper comparison of the intrinsic identity constant by the
aspect ratio.
-/

namespace Homogenization
namespace HighContrast
namespace Initialization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The complete identity-grid clause, conditional on the external reference
comparison and on one common constant dominating its two explicit consumers. -/
theorem identity_clause_of_initIdentityConst_le [NeZero d] [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {Cd CdQ : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hIup : initIdentityConst E ≤ 24 * aspectRatio E)
    (hMoment : 2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
      (1 + 2 * (d : ℝ)) ≤ CdQ)
    (hLog : 2 * (d : ℝ) * (1 + Real.log 24 / Real.log 3) ≤ CdQ) :
    roundedGrid jStar (1 : Mat d) = (1 : Mat d) ∧
      1 ≤ initIdentityConst E ∧
      initIdentityConst E ≤ 24 * aspectRatio E ∧
      2 * (d : ℝ) * Real.log (initIdentityConst E) ≤
        CdQ * Real.log (2 + aspectRatio E) ∧
      ∀ r T : ℤ, jStar ≤ r → r ≤ T → T ≤ M →
        BlockMatLoewnerLE (blockScale (2 : ℝ)⁻¹ (blockSharp E))
            (adaptedMean P (roundedGrid jStar (1 : Mat d)) r) ∧
          BlockMatLoewnerLE
            (adaptedMean P (roundedGrid jStar (1 : Mat d)) r)
            (blockScale 2 E) ∧
          centeredMoment P ((initExpQ d g : ℕ) : ℝ)
              (roundedGrid jStar (1 : Mat d)) r ≤
            ENNReal.ofReal (CdQ * initIdentityConst E) ∧
          BlockMatLoewnerLE
            (adaptedMean P (roundedGrid jStar (1 : Mat d)) T)
            (adaptedMean P (roundedGrid jStar (1 : Mat d)) r) ∧
          BlockMatLoewnerLE
            (adaptedMean P (roundedGrid jStar (1 : Mat d)) r)
            (blockScale (initIdentityConst E)
              (adaptedMean P (roundedGrid jStar (1 : Mat d)) T)) ∧
          0 ≤ detIncrement P (roundedGrid jStar (1 : Mat d)) r T ∧
          detIncrement P (roundedGrid jStar (1 : Mat d)) r T ≤
            2 * (d : ℝ) * Real.log (initIdentityConst E) := by
  have hE := hdag.refBlock_isSymm
  have hEpd := hdag.refBlock_posDef
  have hsharp := blockMatLoewnerLE_blockSharp_reference hdag
  have hI1 := one_le_initIdentityConst hE hEpd hsharp
  have hPi := one_le_aspectRatio_of_coarseEllipticityDagger hdag
  refine ⟨roundedGrid_one hw, hI1, hIup,
    identity_log_bound hPi hI1 hIup hLog, ?_⟩
  intro r T hjr hrT hTM
  have hrM : r ≤ M := hrT.trans hTM
  have hmean := identity_mean_reference_comparison
    hg hE hEpd hw hY hjr hrM
  have hmoment := identity_centeredMoment_le_of_constant
    hg hE hEpd hsharp hw hY hjr hrM hMoment
  have horder := identity_mean_order hP hw hY hjr hrT hTM
  have hupper := identity_mean_le_later
    hg hE hEpd hsharp hw hY hjr hrT hTM
  have hdet := identity_detIncrement_bounds
    hP hg hE hEpd hsharp hw hY hjr hrT hTM
  exact ⟨hmean.1, hmean.2, hmoment, horder, hupper, hdet.1, hdet.2⟩

end

end Initialization
end HighContrast
end Homogenization
