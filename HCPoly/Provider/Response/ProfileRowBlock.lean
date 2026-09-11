/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRowSource

/-!
# Full annealed block rows

The below-start source row and the finite stationary row are joined here for
an arbitrary lower cutoff.  Both orientations are kept separate, with the
coefficient-transpose orientation transported by the diagonal sign
congruence.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem sum_Icc_le_add_of_below {jStar s : ℤ} (hjs : jStar ≤ s)
    {row : ℤ → ℝ} {Galign Gsource : ℝ}
    (hrow0 : ∀ k : ℤ, k ≤ s → 0 ≤ row k)
    (hGsource0 : 0 ≤ Gsource)
    (hbelow : ∀ J : ℤ, J < jStar →
      ∑ k ∈ Finset.Ico J jStar, row k ≤ Gsource)
    (haligned : ∑ k ∈ Finset.Icc jStar s, row k ≤ Galign)
    (J : ℤ) :
    ∑ k ∈ Finset.Icc J s, row k ≤ Galign + Gsource := by
  rcases le_or_gt jStar J with hle | hlt
  · have hmono := Finset.sum_le_sum_of_subset_of_nonneg
      (f := row) (Finset.Icc_subset_Icc hle le_rfl)
      (fun k hk _ ↦ hrow0 k (Finset.mem_Icc.mp hk).2)
    exact hmono.trans (haligned.trans (le_add_of_nonneg_right hGsource0))
  · have hdisj : Disjoint (Finset.Ico J jStar) (Finset.Icc jStar s) := by
      refine Finset.disjoint_left.mpr fun k hk hk' ↦ ?_
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_Icc] at hk'
      omega
    have hsplit :
        Finset.Icc J s = Finset.Ico J jStar ∪ Finset.Icc jStar s := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hsum := add_le_add (hbelow J hlt) haligned
    linarith only [hsum]

/-- Every aligned cell inside the source window has a positive definite
annealed response block. -/
theorem profileAnnealedCell_blockPosDef
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Cd : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid jStar (roundedGrid jStar m0))
    {k s : ℤ} (hks : k ≤ s)
    (hcont : adaptedCell (roundedGrid jStar m0) s ⊆ centeredCube d M)
    {w : Fin d → ℤ}
    (hw : w ∈ alignedIndex (roundedGrid jStar m0) k s) :
    BlockPosDef
      (annealedBlock P (adaptedCellAt (roundedGrid jStar m0) k w)) := by
  have hsub := adaptedCellAt_subset_of_mem_alignedIndex
    (Recurrence.posDef_of_isRoundedGrid hgrid) hks hw
  have hint : HasIntegrableCoarseBlock P
      (adaptedCellAt (roundedGrid jStar m0) k w) := by
    rw [adaptedCellAt_eq_adaptedCellTranslate]
    exact Transport.hasIntegrableCoarseBlock_adaptedCellTranslate hY hm0 hgrid k
      (adaptedCellCenter (roundedGrid jStar m0) k w) (hsub.trans hcont)
  exact Recurrence.blockPosDef_annealedBlock_adaptedCellAt
    (Recurrence.posDef_of_isRoundedGrid hgrid) k w hint

private theorem primalQuadraticRowTerm_nonneg
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g Cd : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {m0 : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid jStar (roundedGrid jStar m0))
    {s k : ℤ} (hks : k ≤ s)
    (hcont : adaptedCell (roundedGrid jStar m0) s ⊆ centeredCube d M)
    (X : BlockVec d) :
    0 ≤ profileRowWeight k s *
      avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
        blockVecDot X
          (blockMatVecMul
            (annealedBlock P
              (adaptedCellAt (roundedGrid jStar m0) k w)) X)) := by
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) (avsum_nonneg ?_)
  intro w hw
  have hpd := profileAnnealedCell_blockPosDef hY hm0 hgrid hks hcont hw
  by_cases hX : X = 0
  · subst hX
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
  · exact (hpd X hX).le

/-- Every primal finite lower-cutoff quadratic row is bounded by the cap-two
response coefficient times the terminal quadratic form. -/
theorem profilePrimalQuadraticRowPartial_le [NeZero d]
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
    (Klo : ℤ) (X : BlockVec d) :
    ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
        avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          blockVecDot X
            (blockMatVecMul
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w)) X)) ≤
      profileRowGamma P rhoDr (roundedGrid jStar m0) Cd g E jStar m0 s *
        blockVecDot X
          (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X) := by
  let row : ℤ → ℝ := fun k ↦ profileRowWeight k s *
    avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
      blockVecDot X
        (blockMatVecMul
          (annealedBlock P
            (adaptedCellAt (roundedGrid jStar m0) k w)) X))
  let Galign : ℝ :=
    (1 + linearDrift P rhoDr (roundedGrid jStar m0) jStar s) /
        (1 - (3 : ℝ) ^ (-(3 / 2 : ℝ))) *
      blockVecDot X
        (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X)
  let Gsource : ℝ :=
    kappaRef E * boundaryConst Cd g m0 ^ 2 * 2 ^ 2 /
        ((3 : ℝ) ^ (3 / 2 - g) - 1) *
      (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) *
      blockVecDot X
        (blockMatVecMul (adaptedMean P (roundedGrid jStar m0) s) X)
  have hrow0 : ∀ k : ℤ, k ≤ s → 0 ≤ row k := by
    intro k hks
    exact primalQuadraticRowTerm_nonneg hY hm0 hgrid hks hcont X
  have haligned : ∑ k ∈ Finset.Icc jStar s, row k ≤ Galign := by
    exact profilePrimalAlignedQuadraticRow_le hstat hgrid hrho hjs hfin X
  have hbelow : ∀ J : ℤ, J < jStar →
      ∑ k ∈ Finset.Ico J jStar, row k ≤ Gsource := by
    intro J hJ
    exact profilePrimalSourceQuadraticRow_le
      hCd hg hm0 hgrid hjs hfields hJ X
  have hGsource0 : 0 ≤ Gsource := by
    have hnon : 0 ≤ ∑ k ∈ Finset.Ico (jStar - 1) jStar, row k :=
      Finset.sum_nonneg fun k hk ↦ hrow0 k (by
        have := (Finset.mem_Ico.mp hk).2
        omega)
    exact hnon.trans (hbelow (jStar - 1) (by omega))
  calc
    ∑ k ∈ Finset.Icc Klo s, profileRowWeight k s *
        avsum (alignedIndex (roundedGrid jStar m0) k s) (fun w ↦
          blockVecDot X
            (blockMatVecMul
              (annealedBlock P
                (adaptedCellAt (roundedGrid jStar m0) k w)) X)) =
      ∑ k ∈ Finset.Icc Klo s, row k := rfl
    _ ≤ Galign + Gsource :=
      sum_Icc_le_add_of_below hjs hrow0 hGsource0 hbelow haligned Klo
    _ = _ := by
      dsimp only [Galign, Gsource, profileRowGamma]
      ring

end

end Homogenization.HighContrast.Response
