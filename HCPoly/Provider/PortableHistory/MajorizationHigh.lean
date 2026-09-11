/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationLow

/-!
# The centered maximum above the checkpoint

The second display of the majorization step of `p.fixed.geometry.one.grid.propagation` bounds
the part of the centered maximum `e.scale.selection.fluctuation.history` at the
terminal scale `T` carried by the scales strictly above the checkpoint:

`E[(sup_{b < j ≤ T} 3^{-ρ(T-j)} max_{z ∈ 3^j 𝕃_q ∩ ⋄_T^q} |·|_{E_T^q})^Q]`
`  ≤ Σ_{j=b+1}^T 3^{-a(T-j)} e^{QΔ_{j,T}^q} (v_j^q)^Q`.

At each scale the aligned cells inside `⋄_T^q` number exactly `3^{d(T-j)}` and
all carry the same law by stationarity of the coefficient law, so max-to-sum over the cells
costs that factor; the change from `E_j^q` to `E_T^q` costs
`|P_{j,T}^q| ≤ e^{Δ_{j,T}^q}`, and the scalar size is dominated by the Schatten
size, which is what turns each term into the centered moment `v_j^q`.  The
admissibility `a ≤ Qρ_max - d` again absorbs the counting factor.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix ENNReal

noncomputable section

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- **One scale above the checkpoint.**  The centered maximum over the aligned
cells of a single scale inside the terminal cell is the centered moment of that
scale, up to the terminal renormalization and the counting factor. -/
theorem centered_scale_le [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ}
    (hQ : 0 < Q) (hadm : a ≤ Q * rhoMax - (d : ℝ))
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ TMax → HasFiniteAdaptedMean P q r)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    ∫⁻ x, (⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q T))) ^ Q ∂P ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
        Real.exp (Q * detIncrement P q j T)) * centeredMoment P Q q j ^ Q := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hlj' : l ≤ j := le_trans hlj hj
  have hjTM : j ≤ TMax := le_trans hjT hT
  have hEj : (toFullBlockMat (adaptedMean P q j)).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hq j (hfin j hj hjTM)
  have hET : (toFullBlockMat (adaptedMean P q T)).PosDef :=
    Recurrence.posDef_toFullBlockMat_adaptedMean hq T (hfin T (le_trans hj hjT) hT)
  have hpdj : Book.Ch02.BlockPosDef (adaptedMean P q j) :=
    (blockPosDef_iff_posDef (Recurrence.isSymmetricBlockMat_adaptedMean P q j)).mpr hEj
  have hpdT : Book.Ch02.BlockPosDef (adaptedMean P q T) :=
    (blockPosDef_iff_posDef (Recurrence.isSymmetricBlockMat_adaptedMean P q T)).mpr hET
  obtain ⟨hlam, -⟩ := blockSize_sandwich (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
    (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT
  have hlam0 : (0 : ℝ) ≤ blockSize (adaptedMean P q j) (adaptedMean P q T) :=
    blockSize_nonneg (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT
  obtain ⟨Z, hZ, hcard, -, -, -, hint⟩ := Recurrence.aligned_subdivision hq hlj' hjT
  have hmem : ∀ w : Fin d → ℤ, adaptedCellCenter q j w ∈ adaptedCell q T → w ∈ Z := by
    intro w hw
    have hw' : w ∈ (↑Z : Set (Fin d → ℤ)) := by rw [hZ]; exact hw
    exact hw'
  -- the statistic at the cell of the origin, and its measurability
  have hcell : AEMeasurable (fun x : CoeffSpace d =>
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
          (adaptedMean P q T)) ^ Q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((aemeasurable_blockSize_coarseBlock_sub
          (Recurrence.hasMeasurableCoarseBlock_adaptedCell P hqPD j)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT).const_mul _))
  -- each aligned cell contributes the centered moment
  have hterm : ∀ w ∈ Z,
      ∫⁻ x, ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q T)) ^ Q ∂P ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
          blockSize (adaptedMean P q j) (adaptedMean P q T)) ^ Q *
        centeredMoment P Q q j ^ Q := by
    intro w hw
    obtain ⟨vw, hvw⟩ := hint w hw
    have hshift : (fun x : CoeffSpace d =>
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q T)) ^ Q) =
        fun x : CoeffSpace d =>
          (fun z : CoeffSpace d => ENNReal.ofReal
            ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
              blockSize (blockSub (coarseBlock (adaptedCell q j) z) (adaptedMean P q j))
                (adaptedMean P q T)) ^ Q) (translateCoeff vw x) := by
      funext x
      rw [Recurrence.adaptedResponse_eq_coarseBlock_translateCoeff hvw x]
    rw [hshift, lintegral_comp_translateCoeff hP hcell vw, centeredMoment_rpow P hQ q j,
      ← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hQ.le ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun x => ?_
    have hsize := blockSize_le_mul_blockSize
      (H := blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
      (isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock _ x)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q j))
      (Recurrence.isSymmetricBlockMat_adaptedMean P q j) hpdj
      (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT hlam0 hlam
    have hschatten := blockSize_le_schattenSize
      (H := blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
      (F := adaptedMean P q j)
      (isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock (adaptedCell q j) x)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q j))
      (Recurrence.isSymmetricBlockMat_adaptedMean P q j) hpdj hQ
    have hreal : (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
          (adaptedMean P q T) ≤
        (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
            blockSize (adaptedMean P q j) (adaptedMean P q T) *
          schattenSize Q (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
            (adaptedMean P q j) := by
      have hchain := hsize.trans (mul_le_mul_of_nonneg_left hschatten hlam0)
      calc (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
              blockSize (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
                (adaptedMean P q T)
          ≤ (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
              (blockSize (adaptedMean P q j) (adaptedMean P q T) *
                schattenSize Q
                  (blockSub (coarseBlock (adaptedCell q j) x) (adaptedMean P q j))
                  (adaptedMean P q j)) :=
            mul_le_mul_of_nonneg_left hchain (by positivity)
        _ = _ := by ring
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hQ.le,
      ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hlam0)]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hreal) hQ.le
  -- the counting factor, absorbed by the admissibility
  have hconst : ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (adaptedMean P q j) (adaptedMean P q T)) ^ Q * (Z.card : ℝ≥0∞) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
        Real.exp (Q * detIncrement P q j T)) := by
    have htj : (0 : ℝ) ≤ (T : ℝ) - (j : ℝ) := by
      have hcastle : (j : ℝ) ≤ (T : ℝ) := by exact_mod_cast hjT
      linarith only [hcastle]
    have htoNat : (((T - j).toNat : ℕ) : ℝ) = (T : ℝ) - (j : ℝ) := by
      have hz : ((T - j).toNat : ℤ) = T - j := Int.toNat_of_nonneg (by omega)
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
    have hcast : ((Z.card : ℕ) : ℝ) = (3 : ℝ) ^ ((d : ℝ) * ((T : ℝ) - (j : ℝ))) := by
      rw [hcard]
      push_cast
      rw [← Real.rpow_natCast (3 : ℝ) (d * (T - j).toNat)]
      congr 1
      push_cast [htoNat]
      ring
    obtain ⟨-, -, -, hnorm, -⟩ := Recurrence.determinant_transport_adaptedMean hP hq hlj' hjT
      (hfin j hj hjTM) (hfin T (le_trans hj hjT) hT)
    have hsizeeq : blockSize (adaptedMean P q j) (adaptedMean P q T) =
        ‖toFullBlockMat (relMean P q j T)‖ :=
      blockSize_eq_norm (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT
    have hlamle : blockSize (adaptedMean P q j) (adaptedMean P q T) ≤
        Real.exp (detIncrement P q j T) := by rw [hsizeeq]; exact hnorm
    have hlamQ : blockSize (adaptedMean P q j) (adaptedMean P q T) ^ Q ≤
        Real.exp (Q * detIncrement P q j T) := by
      have hpow := Real.rpow_le_rpow hlam0 hlamle hQ.le
      rwa [mul_comm Q (detIncrement P q j T), Real.exp_mul]
    have hsplitpow := three_rpow_admissible_le (Q := Q) (rhoMax := rhoMax) hadm htj hlam0 hlamQ
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity) hlam0) hQ.le,
      ← ENNReal.ofReal_natCast, hcast,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (by positivity) hlam0) Q)]
    exact ENNReal.ofReal_le_ofReal hsplitpow
  calc ∫⁻ x, (⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
          ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
              (adaptedMean P q T))) ^ Q ∂P
      ≤ ∫⁻ x, ∑ w ∈ Z, ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
              (adaptedMean P q T)) ^ Q ∂P := by
        refine lintegral_mono fun x => le_trans (ENNReal.rpow_le_rpow ?_ hQ.le)
          (iSup_finset_rpow_le_sum Z _ hQ)
        exact iSup_le fun w => iSup_le fun hw => le_iSup_of_le w
          (le_iSup_of_le (hmem w hw) le_rfl)
    _ = ∑ w ∈ Z, ∫⁻ x, ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
            blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
              (adaptedMean P q T)) ^ Q ∂P := by
        refine lintegral_finset_sum' Z fun w _ => ?_
        exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          (ENNReal.measurable_ofReal.comp_aemeasurable
            ((aemeasurable_blockSize_coarseBlock_sub
              (Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hqPD j w)
              (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
              (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT).const_mul _))
    _ ≤ ∑ _w ∈ Z, ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
            blockSize (adaptedMean P q j) (adaptedMean P q T)) ^ Q *
          centeredMoment P Q q j ^ Q := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
            blockSize (adaptedMean P q j) (adaptedMean P q T)) ^ Q * (Z.card : ℝ≥0∞) *
          centeredMoment P Q q j ^ Q := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ _ := mul_le_mul_left hconst _

/-- **The scales above the checkpoint.**  The part of the centered maximum at the
terminal scale carried by the scales strictly above `b` is the second row of the
profile `e.scale.selection.complete.profile`. -/
theorem centered_high_le [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ}
    (hQ : 0 < Q) (hadm : a ≤ Q * rhoMax - (d : ℝ))
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ TMax → HasFiniteAdaptedMean P q r)
    {b T : ℤ} (hjb : jStar ≤ b) (hbT : b ≤ T) (hT : T ≤ TMax) :
    ∫⁻ x, (⨆ (j : ℤ) (_ : b + 1 ≤ j) (_ : j ≤ T) (w : Fin d → ℤ)
        (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q T))) ^ Q ∂P ≤
      ∑ j ∈ Finset.Icc (b + 1) T,
        ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
          Real.exp (Q * detIncrement P q j T)) * centeredMoment P Q q j ^ Q := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hpdT : Book.Ch02.BlockPosDef (adaptedMean P q T) :=
    (blockPosDef_iff_posDef (Recurrence.isSymmetricBlockMat_adaptedMean P q T)).mpr
      (Recurrence.posDef_toFullBlockMat_adaptedMean hq T (hfin T (le_trans hjb hbT) hT))
  calc ∫⁻ x, (⨆ (j : ℤ) (_ : b + 1 ≤ j) (_ : j ≤ T) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q T))) ^ Q ∂P
      ≤ ∫⁻ x, ∑ j ∈ Finset.Icc (b + 1) T,
          (⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
            ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
              blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
                (adaptedMean P q T))) ^ Q ∂P := by
        refine lintegral_mono fun x => le_trans (ENNReal.rpow_le_rpow ?_ hQ.le)
          (iSup_finset_rpow_le_sum (Finset.Icc (b + 1) T) _ hQ)
        exact iSup_le fun j => iSup_le fun h1 => iSup_le fun h2 =>
          le_iSup_of_le j (le_iSup_of_le (Finset.mem_Icc.mpr ⟨h1, h2⟩) le_rfl)
    _ = ∑ j ∈ Finset.Icc (b + 1) T,
          ∫⁻ x, (⨆ (w : Fin d → ℤ) (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
            ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
              blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
                (adaptedMean P q T))) ^ Q ∂P := by
        refine lintegral_finset_sum' _ fun j _ => ?_
        exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
          (aemeasurable_adaptedCellSup hqPD (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT
            ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ)))) j (adaptedCell q T))
    _ ≤ _ := by
        refine Finset.sum_le_sum fun j hjmem => ?_
        rw [Finset.mem_Icc] at hjmem
        exact centered_scale_le hQ hadm hP hq hlj hfin (by omega) hjmem.2 hT

end Window

end

end PortableHistory
end HighContrast
end Homogenization
