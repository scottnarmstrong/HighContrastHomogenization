/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.RowDischarge
import HCPoly.Provider.Transport.TransportMeanDomination
import HCPoly.Provider.Transport.WhitneyRows
import HCPoly.Provider.Transport.WindowDefinedness
import HCPoly.Provider.Transport.WindowWholeCell
import HCPoly.Provider.Transport.WindowMomentBound
import HCPoly.Provider.Transport.WindowTerminalNormalization
import HCPoly.Provider.Transport.TransportCoefficients
import HCPoly.Provider.PortableHistory.CheckpointMoment

/-!
# The per-level data of the transported nonlinear history

The two branches of `e.two.grid.whitney.mean.bound` are stated over data the
transport must exhibit at every target level of the new grid, and the two
regimes exhibit different data.

*A continued level.*  `l.two.grid.whitney` supplies the maximal
filling of the target cell by the old grid; every cell of every row lies inside
the target, so the containment of the target in the window is inherited by all
of them and the containment hypotheses of the window carriers are discharged for
free.  Averaged, `e.two.grid.whitney.average` puts the adapted mean of the
target cell below the weighted adapted means of the filling plus the mean of the
below-start term, and `e.two.grid.whitney.mean.bound` carries that onto the
new terminal normalization through the bridge — which is exactly
`P_{j,n}^{q'} ≤ S^tP̄_WS-(1-m_W)S^tS+R_W`.  The below-start term is a nonnegative
multiple of the reference block, and
`e.two.grid.source.normalization` measures it against the new
terminal mean, exhibiting the printed `ε_j`.

*An early level.*  There the whole target cell is one source residual: the
whole-cell source bound at the early target scales puts the mean of
the target cell below `B_{q'}\E[Y_P]` times the reference block, the terminal
normalization measures that block against the new terminal mean, and the
universal moment bound `‖Y_P‖_{L^Q}≤𝒰=2` closes the square.  What comes out is
the printed early coefficient `𝖣_early^{tr,𝒮}(q') = C_dκ_𝐄B_{q'}²𝒰²`, the factor
`C_d ≥ 1` being the only slack used.

The remaining datum the row consumes, the near-isometry bound `S^tS ≤ (1+η)I`,
is the bridge normalization clause of `p.two.grid.transport`
itself, read through `Transport.toFullBlockMat_bridgeGram`; it is not a property of the
filling and is therefore not produced here.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## A continued target level -/

/-- **The filling data of one continued target level.**  For an aligned target
cell of the new grid inside the window, there are a maximal filling of it by the
old grid up to the scale `m`, a transported convex combination `P̄_W`, its bridge
excess `M_W` and positive part `\widehat P_W`, an upper mean `K_W` dominating the
target's relative mean, and a normalized source residual `R_W` below the printed
`ε_j` — in exactly the shapes the two branches of
`e.two.grid.whitney.mean.bound` consume. -/
theorem exists_continued_level_filling [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ} (hd : 1 ≤ d) (hCd : 0 < Cd) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu nu' : Mat d}
    (hnu : nu.PosDef) (hnu' : nu'.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu))
    (hq' : IsRoundedGrid jStar (roundedGrid jStar nu'))
    {Khop : ℝ} (hK : gridRatio (roundedGrid jStar nu) (roundedGrid jStar nu') ≤ Khop)
    {t n j m : ℤ} (hjt : jStar ≤ t) (hjn : jStar ≤ n) (hjm : jStar ≤ m)
    (hjj : jStar ≤ j) (z : Fin d → ℤ)
    (hcontt : adaptedCell (roundedGrid jStar nu) t ⊆ centeredCube d M)
    (hcontn : adaptedCell (roundedGrid jStar nu') n ⊆ centeredCube d M)
    (hcontz : adaptedCellAt (roundedGrid jStar nu') j z ⊆ centeredCube d M) :
    ∃ (Z : ℤ → Finset (Fin d → ℤ)) (Pbar Mblk Phat KW Rm : BlockMat d),
      (∀ r, ↑(Z r) = fillingIndex (roundedGrid jStar nu) m
        (adaptedCellAt (roundedGrid jStar nu') j z) r) ∧
      toFullBlockMat Pbar =
          ∑ r ∈ Finset.Icc jStar m,
              (∑ w ∈ Z r, (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
                (volume (adaptedCellAt (roundedGrid jStar nu') j z)).toReal) •
                toFullBlockMat (relMean P (roundedGrid jStar nu) r t) +
            (1 - ∑ r ∈ Finset.Icc jStar m,
              ∑ w ∈ Z r, (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
                (volume (adaptedCellAt (roundedGrid jStar nu') j z)).toReal) •
              (1 : FullBlockMat d) ∧
      toFullBlockMat Mblk =
          (bridgeMap (adaptedMean P (roundedGrid jStar nu) t)
              (adaptedMean P (roundedGrid jStar nu') n))ᵀ * toFullBlockMat Pbar *
            bridgeMap (adaptedMean P (roundedGrid jStar nu) t)
              (adaptedMean P (roundedGrid jStar nu') n) - 1 ∧
      toFullBlockMat Phat = 1 + toFullBlockMat (blockPosPart Mblk) ∧
      toFullBlockMat KW =
          (bridgeMap (adaptedMean P (roundedGrid jStar nu) t)
              (adaptedMean P (roundedGrid jStar nu') n))ᵀ * toFullBlockMat Pbar *
              bridgeMap (adaptedMean P (roundedGrid jStar nu) t)
                (adaptedMean P (roundedGrid jStar nu') n) -
            (1 - ∑ r ∈ Finset.Icc jStar m,
              ∑ w ∈ Z r, (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
                (volume (adaptedCellAt (roundedGrid jStar nu') j z)).toReal) •
              ((bridgeMap (adaptedMean P (roundedGrid jStar nu) t)
                  (adaptedMean P (roundedGrid jStar nu') n))ᵀ *
                bridgeMap (adaptedMean P (roundedGrid jStar nu) t)
                  (adaptedMean P (roundedGrid jStar nu') n)) +
            toFullBlockMat Rm ∧
      toFullBlockMat (relMean P (roundedGrid jStar nu') j n) ≤ toFullBlockMat KW ∧
      toFullBlockMat Rm ≤
        (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * zetaG g *
              (3 : ℝ) ^ (jStar - j) * (∫ a, Y a ∂P) *
            (kappaRef E * (boundaryConst Cd g nu' * ∫ a, Y a ∂P))) •
          (1 : FullBlockMat d) := by
  classical
  have hqpd : (roundedGrid jStar nu).PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hq'pd : (roundedGrid jStar nu').PosDef := Recurrence.posDef_of_isRoundedGrid hq'
  have hHpd : (toFullBlockMat (adaptedMean P (roundedGrid jStar nu) t)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _)
      (blockPosDef_adaptedMean_of_isWindowMultiplier hY hnu hq hjt hcontt)
  have hFpd : (toFullBlockMat (adaptedMean P (roundedGrid jStar nu') n)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _)
      (blockPosDef_adaptedMean_of_isWindowMultiplier hY hnu' hq' hjn hcontn)
  obtain ⟨Z, hZ, hsub, -, -, -, -, -, -⟩ := maximal_filling hq'pd hqpd m j
    (adaptedCellCenter (roundedGrid jStar nu') j z)
  have hZ' : ∀ r, ↑(Z r) = fillingIndex (roundedGrid jStar nu) m
      (adaptedCellAt (roundedGrid jStar nu') j z) r := hZ
  have hcontcell : ∀ (r : ℤ), ∀ w ∈ Z r,
      adaptedCellAt (roundedGrid jStar nu) r w ⊆ centeredCube d M := fun r w hw =>
    (hsub r w hw).trans hcontz
  have hKh : (0 : ℝ) ≤ Khop :=
    le_trans (le_trans zero_le_one (one_le_gridRatio _ _)) hK
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hYint : (0 : ℝ) ≤ ∫ a, Y a ∂P :=
    le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  have hc0 : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu *
      zetaG g * (3 : ℝ) ^ (jStar - j) * ∫ a, Y a ∂P :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (by linarith only [hdR]) (Real.sqrt_nonneg _)) hKh)
        (zero_le_boundaryConst hCd.le hg1 nu)) (zero_lt_zetaG hg1).le)
      (zpow_nonneg (by norm_num) _)) hYint
  have hdom := adaptedMean_le_filling_rows (Khop := Khop) hd hCd.le hg1 hE hEpd hP hY
    hnu hnu' hq hq' hK hjm hjj hZ' hcontcell hcontz
  -- the six blocks
  set S : FullBlockMat d := bridgeMap (adaptedMean P (roundedGrid jStar nu) t)
    (adaptedMean P (roundedGrid jStar nu') n) with hSdef
  set theta : ℤ → ℝ := fun r => ∑ w ∈ Z r,
    (volume (adaptedCellAt (roundedGrid jStar nu) r w)).toReal /
      (volume (adaptedCellAt (roundedGrid jStar nu') j z)).toReal with hthetadef
  set cb : ℝ := 6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g nu * zetaG g *
    (3 : ℝ) ^ (jStar - j) * ∫ a, Y a ∂P with hcbdef
  set Pbar : BlockMat d := ofFullBlockMat
    (∑ r ∈ Finset.Icc jStar m,
        theta r • toFullBlockMat (relMean P (roundedGrid jStar nu) r t) +
      (1 - ∑ r ∈ Finset.Icc jStar m, theta r) • (1 : FullBlockMat d)) with hPbardef
  have hPbar : toFullBlockMat Pbar =
      ∑ r ∈ Finset.Icc jStar m,
          theta r • toFullBlockMat (relMean P (roundedGrid jStar nu) r t) +
        (1 - ∑ r ∈ Finset.Icc jStar m, theta r) • (1 : FullBlockMat d) :=
    toFullBlockMat_ofFullBlockMat _
  set Rm : BlockMat d := ofFullBlockMat
    (matSqrt ((toFullBlockMat (adaptedMean P (roundedGrid jStar nu') n))⁻¹) *
      (cb • toFullBlockMat E) *
      matSqrt ((toFullBlockMat (adaptedMean P (roundedGrid jStar nu') n))⁻¹)) with hRmdef
  have hRm : toFullBlockMat Rm =
      matSqrt ((toFullBlockMat (adaptedMean P (roundedGrid jStar nu') n))⁻¹) *
        (cb • toFullBlockMat E) *
        matSqrt ((toFullBlockMat (adaptedMean P (roundedGrid jStar nu') n))⁻¹) :=
    toFullBlockMat_ofFullBlockMat _
  have hPK := relMean_le_of_annealedBlock_le (R := Finset.Icc jStar m) (theta := theta)
    (Pbar := Pbar) (Rm := Rm) (G := cb • toFullBlockMat E) hHpd hFpd hPbar hRm hdom
  refine ⟨Z, Pbar, ofFullBlockMat (Sᵀ * toFullBlockMat Pbar * S - 1),
    ofFullBlockMat (1 + toFullBlockMat
      (blockPosPart (ofFullBlockMat (Sᵀ * toFullBlockMat Pbar * S - 1)))),
    ofFullBlockMat (Sᵀ * toFullBlockMat Pbar * S -
      (1 - ∑ r ∈ Finset.Icc jStar m, theta r) • (Sᵀ * S) + toFullBlockMat Rm),
    Rm, hZ', hPbar, toFullBlockMat_ofFullBlockMat _, toFullBlockMat_ofFullBlockMat _,
    toFullBlockMat_ofFullBlockMat _, ?_, ?_⟩
  · rw [toFullBlockMat_ofFullBlockMat]
    exact hPK
  · exact toFullBlockMat_le_srcRow_smul_one hCd hg1 hE hEpd hY hnu' hq' hjn hcontn hc0 hRm

/-! ## An early target level -/

/-- **The upper mean of one early target level.**  Below the buffer the whole
target cell is a single source residual: its relative mean at the new terminal
scale is the identity perturbed by at most the printed early coefficient
`𝖣_early^{tr,𝒮}(q')`, so the upper mean of
`e.two.grid.whitney.mean.bound`'s early branch may be taken to be the relative
mean itself. -/
theorem exists_early_level_upper_mean [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    {Q : ℝ} (hQ : 1 ≤ Q) (hCd : 1 ≤ Cd) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu' : Mat d} (hnu' : nu'.PosDef)
    (hq' : IsRoundedGrid jStar (roundedGrid jStar nu')) {n j : ℤ} (hjn : jStar ≤ n)
    (hjj : jStar ≤ j)
    (hcontn : adaptedCell (roundedGrid jStar nu') n ⊆ centeredCube d M)
    (hcontj : adaptedCell (roundedGrid jStar nu') j ⊆ centeredCube d M) :
    ∃ eps : ℝ, 0 ≤ eps ∧ eps ≤ transportEarlyCoeff Cd g E nu' ∧
      toFullBlockMat (relMean P (roundedGrid jStar nu') j n) ≤
        1 + eps • (1 : FullBlockMat d) := by
  have hCd0 : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hB0 : (0 : ℝ) ≤ boundaryConst Cd g nu' := zero_le_boundaryConst hCd0.le hg1 nu'
  have hkap0 : (0 : ℝ) ≤ kappaRef E := by
    rw [kappaRef, blockSize]
    exact Real.sInf_nonneg fun _ hx => hx.1
  have hYint0 : (0 : ℝ) ≤ ∫ a, Y a ∂P :=
    le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  -- the universal moment bound
  have hYtwo : (∫ a, Y a ∂P) ≤ 2 := by
    have h := le_trans (ofReal_integral_le_lqNorm hY hQ) (lqNorm_le_two hQ hw hY)
    have h2 : ENNReal.ofReal (∫ a, Y a ∂P) ≤ ENNReal.ofReal 2 := by
      simpa only [show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 by norm_num] using h
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h2
  -- the two blocks of the terminal normalization
  have hFpd : Book.Ch02.BlockPosDef (adaptedMean P (roundedGrid jStar nu') n) :=
    blockPosDef_adaptedMean_of_isWindowMultiplier hY hnu' hq' hjn hcontn
  have hFsym : IsSymmetricBlockMat (adaptedMean P (roundedGrid jStar nu') n) :=
    Recurrence.isSymmetricBlockMat_adaptedMean _ _ _
  have hFfull : (toFullBlockMat (adaptedMean P (roundedGrid jStar nu') n)).PosDef :=
    posDef_toFullBlockMat hFsym hFpd
  have hEjsym : IsSymmetricBlockMat (adaptedMean P (roundedGrid jStar nu') j) :=
    Recurrence.isSymmetricBlockMat_adaptedMean _ _ _
  -- the whole-cell bound on the mean of the target level
  have hcell : adaptedCellTranslate (roundedGrid jStar nu') j
      (adaptedCellCenter (roundedGrid jStar nu') j 0) ⊆ centeredCube d M := by
    rw [← adaptedCellAt_eq_adaptedCellTranslate, PortableHistory.adaptedCellAt_zero]
    exact hcontj
  have hmeaneq : adaptedMean P (roundedGrid jStar nu') j =
      annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu') j
        (adaptedCellCenter (roundedGrid jStar nu') j 0)) := by
    rw [← adaptedCellAt_eq_adaptedCellTranslate, PortableHistory.adaptedCellAt_zero]
    rfl
  have h1 : blockSize (adaptedMean P (roundedGrid jStar nu') j)
      (adaptedMean P (roundedGrid jStar nu') n) ≤
      boundaryConst Cd g nu' * (∫ a, Y a ∂P) *
        blockSize E (adaptedMean P (roundedGrid jStar nu') n) := by
    rw [hmeaneq]
    exact blockSize_annealedBlock_le hCd0.le hg1 hE hEpd hY hnu' hq' hFsym hFpd hjj _ hcell
  have h2 : blockSize E (adaptedMean P (roundedGrid jStar nu') n) ≤
      kappaRef E * (boundaryConst Cd g nu' * ∫ a, Y a ∂P) :=
    blockSize_adaptedMean_le hCd0 hg1 hE hEpd hY hnu' hq' hjn hcontn
  have hEbound : (0 : ℝ) ≤ blockSize E (adaptedMean P (roundedGrid jStar nu') n) :=
    PortableHistory.blockSize_nonneg hE hFsym hFpd
  have htle : blockSize (adaptedMean P (roundedGrid jStar nu') j)
      (adaptedMean P (roundedGrid jStar nu') n) ≤ transportEarlyCoeff Cd g E nu' := by
    have hstep : boundaryConst Cd g nu' * (∫ a, Y a ∂P) *
        blockSize E (adaptedMean P (roundedGrid jStar nu') n) ≤
        boundaryConst Cd g nu' * (∫ a, Y a ∂P) *
          (kappaRef E * (boundaryConst Cd g nu' * ∫ a, Y a ∂P)) :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hB0 hYint0)
    have hsq : boundaryConst Cd g nu' * (∫ a, Y a ∂P) *
        (kappaRef E * (boundaryConst Cd g nu' * ∫ a, Y a ∂P)) ≤
        kappaRef E * boundaryConst Cd g nu' ^ 2 * 4 := by
      have hYsq : (∫ a, Y a ∂P) * (∫ a, Y a ∂P) ≤ 4 := by
        nlinarith only [hYtwo, hYint0]
      have hkb : (0 : ℝ) ≤ kappaRef E * boundaryConst Cd g nu' ^ 2 :=
        mul_nonneg hkap0 (pow_nonneg hB0 2)
      nlinarith only [mul_le_mul_of_nonneg_left hYsq hkb]
    have hCdstep : kappaRef E * boundaryConst Cd g nu' ^ 2 * 4 ≤
        transportEarlyCoeff Cd g E nu' := by
      rw [transportEarlyCoeff]
      have hpos : (0 : ℝ) ≤ kappaRef E * boundaryConst Cd g nu' ^ 2 * 4 :=
        mul_nonneg (mul_nonneg hkap0 (pow_nonneg hB0 2)) (by norm_num)
      nlinarith only [mul_le_mul_of_nonneg_right hCd hpos]
    linarith only [h1, hstep, hsq, hCdstep]
  -- the witness
  refine ⟨max 0 (blockSize (adaptedMean P (roundedGrid jStar nu') j)
      (adaptedMean P (roundedGrid jStar nu') n) - 1), le_max_left _ _, ?_, ?_⟩
  · refine max_le (zero_le_transportEarlyCoeff hCd0.le hg1 E nu') ?_
    linarith only [htle]
  · have hsand := (PortableHistory.blockSize_sandwich hEjsym hFsym hFpd).1
    have hconj := (conj_normalize hFfull
      (blockSize (adaptedMean P (roundedGrid jStar nu') j)
        (adaptedMean P (roundedGrid jStar nu') n))).mp hsand
    rw [← Recurrence.toFullBlockMat_relMean] at hconj
    refine le_trans hconj ?_
    have hone : (1 : FullBlockMat d) +
        (max 0 (blockSize (adaptedMean P (roundedGrid jStar nu') j)
          (adaptedMean P (roundedGrid jStar nu') n) - 1)) • (1 : FullBlockMat d) =
        (1 + max 0 (blockSize (adaptedMean P (roundedGrid jStar nu') j)
          (adaptedMean P (roundedGrid jStar nu') n) - 1)) • (1 : FullBlockMat d) := by
      rw [add_smul, one_smul]
    rw [hone]
    refine Matrix.le_iff.mpr ?_
    rw [← sub_smul]
    refine (Matrix.PosSemidef.one).smul ?_
    have := le_max_right (0 : ℝ) (blockSize (adaptedMean P (roundedGrid jStar nu') j)
      (adaptedMean P (roundedGrid jStar nu') n) - 1)
    linarith only [this]

end

end Transport
end HighContrast
end Homogenization
