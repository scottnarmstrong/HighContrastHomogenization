/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.BridgeComparison
import HCPoly.Provider.ShortHop.Normalization
import HCPoly.Provider.ShortHop.OrderedChoice
import HCPoly.Provider.ShortHop.WindowGuard
import HCPoly.Provider.Transport.WhitneySquareWeights

/-!
# The conclusion of the successful short test

This is the second half of the proof of `p.successful.short.bridge`,
assembled: from the two mean comparisons and the shifted determinant drift of
`p.successful.short.bridge` read at the intermediate
scale, together with the determinant test preceding a change of geometry and the
two threshold inequalities of the ordered choice, it derives the near isometry
and the new-grid drift bound of
`e.successful.short.near`.

The route is the printed one.  The window makes the old grid's annealed blocks
positive definite and ordered on exactly the scales read, so its linear drift is
nonnegative and the determinant test converts into the normalization display.
The two comparison errors are then squeezed between zero and the envelopes of
the ordered choice, the near isometry follows from the bridge-error threshold
inequality, and the lower half — which is exactly the hypothesis the shifted
drift asks for — feeds the shifted drift, whose right-hand side the new-grid
drift threshold inequality closes.

The rounded-hop constant is not assumed nonnegative: it dominates the cross-grid
factor, which is at least one.

Three inputs are consumed as hypotheses because they belong to neighbouring
results: the drift of the old grid at the two scales read is bounded by the two
drift envelopes, which is the fixed-grid determinant drift lemma
`e.fixed.geometry.drift.advance` applied twice; and the three source
remainders lie between zero and the source allowance, which is the hop-index
bootstrap `e.global.selection.eccentricity`.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- **The conclusion of the successful short test.**  The near isometry and the
new-grid drift bound, from the two-grid comparisons, the shifted drift, the
short test and the ordered choice. -/
theorem shortHop_conclusion [NeZero d] (hd0 : d ≠ 0) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd Qexp : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d Qexp K jStar M) {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {mu mu' : Mat d} (hmu : mu.PosDef)
    {u l0 : ℤ} (hju : jStar ≤ u) (hl0 : 0 ≤ l0)
    (hcontOld : ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * l0 →
      adaptedCell (roundedGrid jStar mu) j ⊆ centeredCube d M)
    {C Khop rhoDr etaX etaNew deltaShort etaPre tauSrc : ℝ}
    (hC : 0 ≤ C)
    (hKfac : gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop)
    (hden : C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2)
    (hetaPre : 0 ≤ etaPre) (hdelta : 0 ≤ deltaShort) (hetaX4 : etaX ≤ 1 / 4)
    (hdet : adaptedDetRoot P (roundedGrid jStar mu) u ≤
      (1 + deltaShort) * adaptedDetRoot P (roundedGrid jStar mu) (u + 2 * l0))
    (hthr : ∀ b delta R1 R2 R3 : ℝ, 0 ≤ b → b ≤ etaPre → 0 ≤ delta → delta ≤ deltaShort →
      0 ≤ R1 → R1 ≤ tauSrc → 0 ≤ R2 → R2 ≤ tauSrc → 0 ≤ R3 → R3 ≤ tauSrc →
      shortBridgeErr d C Khop rhoDr l0 b delta R1 R2 ≤ etaX ∧
        shortNewDrift d C Khop rhoDr l0 b delta R2 R3 ≤ etaNew)
    (hR1nn : 0 ≤ bridgeCmpRemainder C Cd g rhoDr E jStar mu mu' (u + l0))
    (hR1 : bridgeCmpRemainder C Cd g rhoDr E jStar mu mu' (u + l0) ≤ tauSrc)
    (hR2nn : 0 ≤ bridgeCmpRemainder C Cd g rhoDr E jStar mu' mu (u + 2 * l0))
    (hR2 : bridgeCmpRemainder C Cd g rhoDr E jStar mu' mu (u + 2 * l0) ≤ tauSrc)
    (hR3nn : 0 ≤ bridgeShiftedRemainder C Cd g rhoDr E jStar mu mu' (u + l0) l0)
    (hR3 : bridgeShiftedRemainder C Cd g rhoDr E jStar mu mu' (u + l0) l0 ≤ tauSrc)
    (hDn : linearDrift P rhoDr (roundedGrid jStar mu) jStar (u + l0) ≤
      shortDriftNew d rhoDr l0 etaPre deltaShort)
    (hDt : linearDrift P rhoDr (roundedGrid jStar mu) jStar (u + 2 * l0) ≤
      shortDriftTerm d rhoDr l0 etaPre deltaShort)
    (hcmpUp : BlockMatLoewnerLE
      (blockSub (adaptedMean P (roundedGrid jStar mu') (u + l0))
        (adaptedMean P (roundedGrid jStar mu) u))
      (blockScale (bridgeErrUpper C Cd g rhoDr
          (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
          (u + l0) l0)
        (adaptedMean P (roundedGrid jStar mu) (u + l0))))
    (hcmpLo : BlockMatLoewnerLE
      (blockScale (-bridgeErrLower C Cd g rhoDr
          (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
          (u + l0) l0)
        (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0)))
      (blockSub (adaptedMean P (roundedGrid jStar mu') (u + l0))
        (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0))))
    (hsdrift : ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
      BlockMatLoewnerLE
        (blockScale (1 - eta) (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0)))
        (adaptedMean P (roundedGrid jStar mu') (u + l0)) →
      linearDrift P rhoDr (roundedGrid jStar mu') jStar (u + l0) ≤
        C * (eta + gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') *
              (3 : ℝ) ^ (-(l0 : ℝ)) +
            (1 + gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) *
              (3 : ℝ) ^ (2 * rhoDr * (l0 : ℝ)) *
              linearDrift P rhoDr (roundedGrid jStar mu) jStar (u + 2 * l0) +
            bridgeShiftedRemainder C Cd g rhoDr E jStar mu mu' (u + l0) l0)) :
    BlockMatLoewnerLE
        (blockScale (1 - etaX) (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0)))
        (adaptedMean P (roundedGrid jStar mu') (u + l0)) ∧
      BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar mu') (u + l0))
        (blockScale (1 + etaX) (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0))) ∧
      linearDrift P rhoDr (roundedGrid jStar mu') jStar (u + l0) ≤ etaNew := by
  -- the guard chain on the old grid
  have hPU := posDef_adaptedMean_of_window hw hY hmu hju (by omega) hcontOld
  have hPN := posDef_adaptedMean_of_window hw hY hmu (by omega : jStar ≤ u + l0)
    (by omega) hcontOld
  have hPT := posDef_adaptedMean_of_window hw hY hmu (by omega : jStar ≤ u + 2 * l0)
    le_rfl hcontOld
  have hmonoNU := adaptedMean_le_of_window hstat hw hY hmu hju (by omega : u ≤ u + l0)
    (by omega) hcontOld
  have hmonoTU := adaptedMean_le_of_window hstat hw hY hmu hju
    (by omega : u ≤ u + 2 * l0) le_rfl hcontOld
  have hDnn := linearDrift_nonneg_of_window (rhoDr := rhoDr) hstat hw hY hmu
    (by omega : jStar ≤ u + l0) (by omega : u + l0 ≤ u + 2 * l0) hcontOld
  have hDtnn := linearDrift_nonneg_of_window (rhoDr := rhoDr) hstat hw hY hmu
    (by omega : jStar ≤ u + 2 * l0) le_rfl hcontOld
  -- the normalization display
  have hnorm := normalization_of_short_test hd0 hPU hPT hmonoTU hdet
  -- the cross-grid factor
  have hKfac0 : (0 : ℝ) ≤ gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') :=
    le_trans zero_le_one (Transport.one_le_gridRatio _ _)
  have hdenK : C * gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') *
      (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2 := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(l0 : ℝ)) := by positivity
    exact le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKfac hC) h3.le) hden
  -- the shape the two comparison errors are read in
  have hshift : u + l0 + l0 = u + 2 * l0 := by ring
  have hepnn := bridgeErrUpper_nonneg (Cd := Cd) (g := g) (mq' := mu') (l := l0) hC hKfac0
    hDnn hR1nn
  have hemnn : 0 ≤ bridgeErrLower C Cd g rhoDr
      (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
      (u + l0) l0 := by
    refine bridgeErrLower_nonneg hC hKfac0 hdenK ?_ ?_
    · rw [hshift]; exact hDtnn
    · rw [hshift]; exact hR2nn
  have heple := bridgeErrUpper_le_shortErrUpper (Cd := Cd) (g := g) (E := E) (mq' := mu')
    (Khop := Khop) (b := etaPre) (delta := deltaShort)
    (R1 := bridgeCmpRemainder C Cd g rhoDr E jStar mu mu' (u + l0))
    hC hKfac0 hKfac hDnn hDn le_rfl
  have hemle : bridgeErrLower C Cd g rhoDr
      (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
      (u + l0) l0 ≤
      shortErrLower d C Khop rhoDr l0 etaPre deltaShort
        (bridgeCmpRemainder C Cd g rhoDr E jStar mu' mu (u + 2 * l0)) := by
    refine bridgeErrLower_le_shortErrLower hC hKfac0 hKfac hden ?_ ?_ ?_
    · rw [hshift]; exact hDtnn
    · rw [hshift]; exact hDt
    · rw [hshift]
  -- the two threshold inequalities, at the corner of the box
  obtain ⟨hbrX, hndX⟩ := hthr etaPre deltaShort
    (bridgeCmpRemainder C Cd g rhoDr E jStar mu mu' (u + l0))
    (bridgeCmpRemainder C Cd g rhoDr E jStar mu' mu (u + 2 * l0))
    (bridgeShiftedRemainder C Cd g rhoDr E jStar mu mu' (u + l0) l0)
    hetaPre le_rfl hdelta le_rfl hR1nn hR1 hR2nn hR2 hR3nn hR3
  have hbrmax : max (bridgeErrLower C Cd g rhoDr
        (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
        (u + l0) l0)
      ((1 + bridgeErrUpper C Cd g rhoDr
        (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
        (u + l0) l0) * (1 + deltaShort) ^ d - 1) ≤ etaX := by
    refine max_le (le_trans hemle (le_trans (le_max_left _ _) hbrX)) ?_
    have hpow : (0 : ℝ) ≤ (1 + deltaShort) ^ d := by positivity
    have hstep := mul_le_mul_of_nonneg_right
      (by linarith only [heple] :
        1 + bridgeErrUpper C Cd g rhoDr
            (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
            (u + l0) l0 ≤
          1 + shortErrUpper d C Khop rhoDr l0 etaPre deltaShort
            (bridgeCmpRemainder C Cd g rhoDr E jStar mu mu' (u + l0))) hpow
    exact le_trans (by linarith only [hstep]) (le_trans (le_max_right _ _) hbrX)
  -- the near isometry
  obtain ⟨hlow, hhigh⟩ := nearIsometry_of_comparisons
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu') (u + l0))
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu) u)
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu) (u + l0))
    (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu) (u + 2 * l0))
    hPT.posSemidef hepnn hbrmax hcmpUp hcmpLo (blockMatLoewnerLE_of_le hmonoNU) hnorm
  refine ⟨hlow, hhigh, ?_⟩
  -- the shifted drift, at the lower comparison error
  have hem4 : bridgeErrLower C Cd g rhoDr
      (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
      (u + l0) l0 ≤ 1 / 4 :=
    le_trans (le_trans (le_max_left _ _) hbrmax) hetaX4
  have hloc : BlockMatLoewnerLE
      (blockScale (1 - bridgeErrLower C Cd g rhoDr
        (gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu')) P E jStar mu mu'
        (u + l0) l0)
        (adaptedMean P (roundedGrid jStar mu) (u + 2 * l0)))
      (adaptedMean P (roundedGrid jStar mu') (u + l0)) := by
    refine blockMatLoewnerLE_of_le ?_
    rw [toFullBlockMat_blockScale]
    exact lower_nearIsometry hPT.posSemidef le_rfl
      (le_of_blockMatLoewnerLE
        (isSymmetricBlockMat_blockScale _
          (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu) (u + 2 * l0)))
        (isSymmetricBlockMat_blockSub
          (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu') (u + l0))
          (Recurrence.isSymmetricBlockMat_adaptedMean P (roundedGrid jStar mu) (u + 2 * l0)))
        hcmpLo)
  refine le_trans (hsdrift _ hemnn hem4 hloc) (le_trans ?_ hndX)
  exact shifted_le_shortNewDrift hC hKfac0 hKfac hDtnn hDt hemle le_rfl

end

end ShortHop
end HighContrast
end Homogenization
