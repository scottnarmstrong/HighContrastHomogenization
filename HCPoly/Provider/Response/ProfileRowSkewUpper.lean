/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowSkewCarriers

/-!
# Upper bounds for fixed-skew all-earlier rows

The block-row estimate is stable under the fixed shear because a congruent
quadratic form is the original form at the sheared doubled vector.  The Schur
estimate is then applied to each hatted block, retaining its exact factor two.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem profilePrimalHattedQuadraticLoadRowPartial_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Cd : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {m0 : Mat d} (hCd : 0 < Cd) (hg : g < 1) (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid jStar (roundedGrid jStar m0))
    {rhoDr : ℝ} (hrho : rhoDr < 3 / 2)
    {s t : ℤ} (hjs : jStar ≤ s)
    (hcont : adaptedCell (roundedGrid jStar m0) s ⊆ centeredCube d M)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ s →
      HasFiniteAdaptedMean P (roundedGrid jStar m0) k)
    (hfields : IsWindowedSourceFields P g Cd E jStar m0 s t Y)
    (h0 : Mat d) (Klo : ℤ) (Pcen Qcen : Vec d) :
    ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
        avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          profileQuadraticLoad
            (profileHattedBlock h0
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w))) Pcen Qcen) ≤
      profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E jStar m0 s *
        profileQuadraticLoad
          (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
          Pcen Qcen := by
  let XP : BlockVec d := (Pcen, matVecMul h0 Pcen)
  let XQ : BlockVec d := (0, Qcen)
  have hp := profilePrimalQuadraticRowPartial_le hstat hY hCd hg hm0 hgrid
    hrho hjs hcont hfin hfields Klo XP
  have hq := profilePrimalQuadraticRowPartial_le hstat hY hCd hg hm0 hgrid
    hrho hjs hcont hfin hfields Klo XQ
  have hhat :
      ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
          avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
            profileQuadraticLoad
              (profileHattedBlock h0
                (annealedBlock P
                  (adaptedCellAt (roundedGrid jStar m0) k w))) Pcen Qcen) ≤
        profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E jStar m0 s *
          profileQuadraticLoad
            (profileHattedBlock h0
              (adaptedMean P (roundedGrid jStar m0) s)) Pcen Qcen := by
    simpa only [profileQuadraticLoad, profileHattedBlock,
      blockQuadratic_skewBlockCongr, matVecMul_zero, zero_add, add_zero,
      avsum_add, mul_add, Finset.sum_add_distrib, XP, XQ] using
      add_le_add hp hq
  simpa only [profileHattedBlock_adaptedMean] using hhat

/-- A finite primal hatted Schur row has the exact upper factor
`2 * Γ_s^ᵎ * ᵌ_s^-`. -/
theorem profilePrimalHattedRowPartial_le_two_gamma [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Cd : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {m0 : Mat d} (hCd : 0 < Cd) (hg : g < 1) (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid jStar (roundedGrid jStar m0))
    {rhoDr : ℝ} (hrho : rhoDr < 3 / 2)
    {s t : ℤ} (hjs : jStar ≤ s)
    (hcont : adaptedCell (roundedGrid jStar m0) s ⊆ centeredCube d M)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ s →
      HasFiniteAdaptedMean P (roundedGrid jStar m0) k)
    (hfields : IsWindowedSourceFields P g Cd E jStar m0 s t Y)
    (h0 : Mat d) (Klo : ℤ) (Pcen Qcen : Vec d) :
    profilePrimalHattedRowPartial P (roundedGrid jStar m0) h0 Klo s
        Pcen Qcen ≤
      2 * profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E jStar m0 s *
        profileQuadraticLoad
          (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
          Pcen Qcen := by
  have hpoint : ∀ k ∈ Finset.Icc Klo s,
      avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          profileSchurLoad
            (profileHattedBlock h0
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w))) Pcen Qcen) ≤
        2 * avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          profileQuadraticLoad
            (profileHattedBlock h0
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w))) Pcen Qcen) := by
    intro k hk
    have hks := (Finset.mem_Icc.mp hk).2
    calc
      avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          profileSchurLoad
            (profileHattedBlock h0
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w))) Pcen Qcen) ≤
        avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          2 * profileQuadraticLoad
            (profileHattedBlock h0
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w))) Pcen Qcen) := by
        refine avsum_le_avsum fun w hw ↦ ?_
        apply profileSchurLoad_le_two_mul_profileQuadraticLoad
        · exact isSymmetricBlockMat_skewBlockCongr
            (Recurrence.isSymmetricBlockMat_annealedBlock P _)
        · exact blockPosDef_skewBlockCongr
            (profileAnnealedCell_blockPosDef hY hm0 hgrid hks hcont hw)
      _ = _ := avsum_const_mul _ 2 _
  have hschur :
      profilePrimalHattedRowPartial P (roundedGrid jStar m0) h0 Klo s
          Pcen Qcen ≤
        2 * ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
          avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
            profileQuadraticLoad
              (profileHattedBlock h0
                (annealedBlock P
                  (adaptedCellAt (roundedGrid jStar m0) k w))) Pcen Qcen) := by
    rw [profilePrimalHattedRowPartial, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hw0 : 0 ≤ profileRowWeight k s := Real.rpow_nonneg (by norm_num) _
    have h := mul_le_mul_of_nonneg_left (hpoint k hk) hw0
    linarith only [h]
  have hquad := profilePrimalHattedQuadraticLoadRowPartial_le hstat hY hCd hg
    hm0 hgrid hrho hjs hcont hfin hfields h0 Klo Pcen Qcen
  calc
    profilePrimalHattedRowPartial P (roundedGrid jStar m0) h0 Klo s
        Pcen Qcen ≤
      2 * ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
        avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          profileQuadraticLoad
            (profileHattedBlock h0
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w))) Pcen Qcen) := hschur
    _ ≤ 2 * (profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E
          jStar m0 s *
        profileQuadraticLoad
          (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
          Pcen Qcen) := mul_le_mul_of_nonneg_left hquad (by norm_num)
    _ = _ := by ring

/-- A finite adjoint hatted Schur row has the same exact factor, with
independent centers and the `D`-congruent hatted terminal block. -/
theorem profileAdjointHattedRowPartial_le_two_gamma [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Cd : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {m0 : Mat d} (hCd : 0 < Cd) (hg : g < 1) (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid jStar (roundedGrid jStar m0))
    {rhoDr : ℝ} (hrho : rhoDr < 3 / 2)
    {s t : ℤ} (hjs : jStar ≤ s)
    (hcont : adaptedCell (roundedGrid jStar m0) s ⊆ centeredCube d M)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ s →
      HasFiniteAdaptedMean P (roundedGrid jStar m0) k)
    (hfields : IsWindowedSourceFields P g Cd E jStar m0 s t Y)
    (h0 : Mat d) (Klo : ℤ) (Pcen Qcen : Vec d) :
    profileAdjointHattedRowPartial P (roundedGrid jStar m0) h0 Klo s
        Pcen Qcen ≤
      2 * profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E jStar m0 s *
        profileQuadraticLoad
          (profileRecenteredAdjointMean P (roundedGrid jStar m0) h0 s)
          Pcen Qcen := by
  have hpartial :
      profileAdjointHattedRowPartial P (roundedGrid jStar m0) h0 Klo s
          Pcen Qcen =
        profilePrimalHattedRowPartial P (roundedGrid jStar m0) h0 Klo s
          Pcen Qcen := by
    rw [profileAdjointHattedRowPartial, profilePrimalHattedRowPartial]
    simp_rw [profileHattedAdjointBlock, profileSchurLoad_adjointBlock]
  have hterm :
      profileQuadraticLoad
          (profileRecenteredAdjointMean P (roundedGrid jStar m0) h0 s)
          Pcen Qcen =
        profileQuadraticLoad
          (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
          Pcen Qcen := by
    change profileQuadraticLoad
        (profileAdjointBlock
          (profileRecenteredMean P (roundedGrid jStar m0) h0 s))
        Pcen Qcen = _
    exact profileQuadraticLoad_adjointBlock _ Pcen Qcen
  rw [hpartial, hterm]
  exact profilePrimalHattedRowPartial_le_two_gamma hstat hY hCd hg hm0 hgrid
    hrho hjs hcont hfin hfields h0 Klo Pcen Qcen

end

end Homogenization.HighContrast.Response
