/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowSkewUpper

/-!
# The fixed-skew all-earlier response-row conclusion

The scale row and every earlier row are built from the hatted primal blocks
`G_hᵀ A G_h`; the adjoint row is their subsequent `D`-congruence.  The two
orientations retain independent center pairs.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem profilePrimalHattedScaleLoad_le_partial [NeZero d]
    {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {jStar : ℤ} {m0 : Mat d}
    (hgrid : IsRoundedGrid jStar (roundedGrid jStar m0))
    {s : ℤ} (hjs : jStar ≤ s)
    (hfin : HasFiniteAdaptedMean P (roundedGrid jStar m0) s)
    (h0 : Mat d) (Pcen Qcen : Vec d) :
    profileSchurLoad
        (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
        Pcen Qcen ≤
      profilePrimalHattedRowPartial P (roundedGrid jStar m0) h0 s s
        Pcen Qcen := by
  have hmeas : HasMeasurableCoarseBlock P
      (adaptedCell (roundedGrid jStar m0) s) :=
    fun α β ↦ (hfin α β).aestronglyMeasurable
  have hcell : ∀ w ∈ alignedIndex (roundedGrid jStar m0) s s,
      profileSchurLoad
          (profileHattedBlock h0
            (annealedBlock P
              (adaptedCellAt (roundedGrid jStar m0) s w))) Pcen Qcen =
        profileSchurLoad
          (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
          Pcen Qcen := by
    intro w _
    rw [Recurrence.annealedBlock_adaptedCellAt_eq_adaptedMean
      hstat hgrid hjs hmeas w, profileHattedBlock_adaptedMean]
  have hav :
      avsum (alignedIndex (roundedGrid jStar m0) s s) (fun w ↦
          profileSchurLoad
            (profileHattedBlock h0
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) s w))) Pcen Qcen) =
        profileSchurLoad
          (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
          Pcen Qcen := by
    calc
      avsum (alignedIndex (roundedGrid jStar m0) s s) (fun w ↦
          profileSchurLoad
            (profileHattedBlock h0
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) s w))) Pcen Qcen) =
        avsum (alignedIndex (roundedGrid jStar m0) s s) (fun _ ↦
          profileSchurLoad
            (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
            Pcen Qcen) := by
          rw [avsum_eq, avsum_eq]
          congr 1
          exact Finset.sum_congr rfl hcell
      _ = _ := avsum_const
        (alignedIndex_nonempty (Recurrence.posDef_of_isRoundedGrid hgrid) le_rfl) _
  rw [profilePrimalHattedRowPartial]
  simp only [Finset.Icc_self, Finset.sum_singleton, profileRowWeight,
    sub_self, mul_zero, Real.rpow_zero, one_mul, hav, le_refl]

private theorem profileAdjointHattedScaleLoad_le_partial [NeZero d]
    {P : Measure (CoeffSpace d)}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {jStar : ℤ} {m0 : Mat d}
    (hgrid : IsRoundedGrid jStar (roundedGrid jStar m0))
    {s : ℤ} (hjs : jStar ≤ s)
    (hfin : HasFiniteAdaptedMean P (roundedGrid jStar m0) s)
    (h0 : Mat d) (Pcen Qcen : Vec d) :
    profileSchurLoad
        (profileRecenteredAdjointMean P (roundedGrid jStar m0) h0 s)
        Pcen Qcen ≤
      profileAdjointHattedRowPartial P (roundedGrid jStar m0) h0 s s
        Pcen Qcen := by
  change profileSchurLoad
      (profileAdjointBlock
        (profileRecenteredMean P (roundedGrid jStar m0) h0 s))
      Pcen Qcen ≤ _
  rw [profileSchurLoad_adjointBlock]
  rw [profileAdjointHattedRowPartial]
  simp_rw [profileHattedAdjointBlock, profileSchurLoad_adjointBlock]
  exact profilePrimalHattedScaleLoad_le_partial hstat hgrid hjs hfin h0
    Pcen Qcen

/-- **The fixed-skew all-earlier response-row bound**
`ᴹ_s^⋄ ≤ ᴸ_s^⋄ ≤ 2 Γ_s^ᵎ ᵌ_s^⋄` in both orientations.  The primal blocks are
first sheared by the source skew `h0`; the coefficient-transpose blocks are
then obtained by `D`-congruence, and the center pairs are independent. -/
theorem profileAllEarlierRows [NeZero d]
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
    (h0 : {h : Mat d // IsSkewMat h})
    (Pminus Qminus Pplus Qplus : Vec d) :
    (ENNReal.ofReal
          (profileSchurLoad
            (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
            Pminus Qminus) ≤
        profilePrimalHattedEarlierRow P (roundedGrid jStar m0) h0 s
          Pminus Qminus ∧
      profilePrimalHattedEarlierRow P (roundedGrid jStar m0) h0 s
          Pminus Qminus ≤
        ENNReal.ofReal
          (2 * profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E
              jStar m0 s *
            profileQuadraticLoad
              (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
              Pminus Qminus)) ∧
    (ENNReal.ofReal
          (profileSchurLoad
            (profileRecenteredAdjointMean P (roundedGrid jStar m0) h0 s)
            Pplus Qplus) ≤
        profileAdjointHattedEarlierRow P (roundedGrid jStar m0) h0 s
          Pplus Qplus ∧
      profileAdjointHattedEarlierRow P (roundedGrid jStar m0) h0 s
          Pplus Qplus ≤
        ENNReal.ofReal
          (2 * profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E
              jStar m0 s *
            profileQuadraticLoad
              (profileRecenteredAdjointMean P (roundedGrid jStar m0) h0 s)
              Pplus Qplus)) := by
  have hlowMinus := profilePrimalHattedScaleLoad_le_partial hstat hgrid hjs
    (hfin s hjs le_rfl) h0 Pminus Qminus
  have hlowPlus := profileAdjointHattedScaleLoad_le_partial hstat hgrid hjs
    (hfin s hjs le_rfl) h0 Pplus Qplus
  have hupMinus :
      profilePrimalHattedEarlierRow P (roundedGrid jStar m0) h0 s
          Pminus Qminus ≤
        ENNReal.ofReal
          (2 * profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E
              jStar m0 s *
            profileQuadraticLoad
              (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
              Pminus Qminus) := by
    refine iSup_le fun Klo ↦ ?_
    exact ENNReal.ofReal_le_ofReal
      (profilePrimalHattedRowPartial_le_two_gamma hstat hY hCd hg hm0 hgrid
        hrho hjs hcont hfin hfields h0 Klo Pminus Qminus)
  have hupPlus :
      profileAdjointHattedEarlierRow P (roundedGrid jStar m0) h0 s
          Pplus Qplus ≤
        ENNReal.ofReal
          (2 * profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E
              jStar m0 s *
            profileQuadraticLoad
              (profileRecenteredAdjointMean P (roundedGrid jStar m0) h0 s)
              Pplus Qplus) := by
    refine iSup_le fun Klo ↦ ?_
    exact ENNReal.ofReal_le_ofReal
      (profileAdjointHattedRowPartial_le_two_gamma hstat hY hCd hg hm0 hgrid
        hrho hjs hcont hfin hfields h0 Klo Pplus Qplus)
  refine ⟨⟨?_, hupMinus⟩, ⟨?_, hupPlus⟩⟩
  · calc
      ENNReal.ofReal
          (profileSchurLoad
            (profileRecenteredMean P (roundedGrid jStar m0) h0 s)
            Pminus Qminus) ≤
        ENNReal.ofReal
          (profilePrimalHattedRowPartial P (roundedGrid jStar m0) h0 s s
            Pminus Qminus) := ENNReal.ofReal_le_ofReal hlowMinus
      _ ≤ profilePrimalHattedEarlierRow P (roundedGrid jStar m0) h0 s
          Pminus Qminus := le_iSup (fun Klo : ℤ ↦
            ENNReal.ofReal
              (profilePrimalHattedRowPartial P (roundedGrid jStar m0) h0
                Klo s Pminus Qminus)) s
  · calc
      ENNReal.ofReal
          (profileSchurLoad
            (profileRecenteredAdjointMean P (roundedGrid jStar m0) h0 s)
            Pplus Qplus) ≤
        ENNReal.ofReal
          (profileAdjointHattedRowPartial P (roundedGrid jStar m0) h0 s s
            Pplus Qplus) := ENNReal.ofReal_le_ofReal hlowPlus
      _ ≤ profileAdjointHattedEarlierRow P (roundedGrid jStar m0) h0 s
          Pplus Qplus := le_iSup (fun Klo : ℤ ↦
            ENNReal.ofReal
              (profileAdjointHattedRowPartial P (roundedGrid jStar m0) h0
                Klo s Pplus Qplus)) s

end

end Homogenization.HighContrast.Response
