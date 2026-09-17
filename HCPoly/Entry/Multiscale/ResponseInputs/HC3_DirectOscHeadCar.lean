import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectHeadDepth
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectBlkAll
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEntBridge
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscNonneg
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCellQuad

/-!
# The annealed head of one descendant generation at the carriers

The descendant sum of `p.response.transfer` reads the generation-`n` layer of the source load
`𝓛_s` against the expectation of the flat average, over the depth-`(H+n)` aligned cells of the
terminal cell, of the squared pathwise two-term head
`(⟨Y₁, 𝐛_V Y₁⟩^{1/2} + ⟨Y₂, σ_{*,V}^{-1} Y₂⟩^{1/2})²`.  `HC3_DirectHeadDepth` proves that bound
from nine analytic side conditions on the pathwise coarse blocks.  This module discharges all nine
at the carriers, from the coarse-block integrability of the sample on every aligned cell of the
response grid and the nonnegativity of the two diagonal forms, so that the head bound carries no
analytic side condition.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The annealed head of a descendant generation is at most the corresponding layer of the
source load, minus sign, at the carriers.**  The expectation of the flat average over the
depth-`(H+n)` aligned cells of the squared pathwise two-term head of `a_- = a - g` is at most the
flat average over the generation-`n` cells of the squared annealed two-term head, i.e. the
generation-`n` layer of `𝓛_s^-` of `p.response.transfer`. -/
theorem integral_avsum_sq_head_descendant_le_respCoeffMinus_car {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H n : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s)
    (Y : BlockVec d) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffMinus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffMinus F a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffMinus F)).lowerRight Y.2))) ^ 2 := by
  have hblk : ∀ W : Fin d → ℤ, HasIntegrableCoarseBlock P
      (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W) :=
    fun W => hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag jStar
      hjStar F hm (s - (n : ℤ)) W
  have hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft i k) P :=
    fun W => integrable_coarseBlockMatrix_upperLeft_respCoeffMinus P jStar hjStar F hm
      (s - (n : ℤ)) W (hblk W)
  have hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight i k) P :=
    fun W => integrable_coarseBlockMatrix_lowerRight_respCoeffMinus P jStar hjStar F hm
      (s - (n : ℤ)) W (hblk W)
  have hmeas : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft i k) P :=
    fun W i k => (hULe W i k).aestronglyMeasurable
  have hmeas' : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight i k) P :=
    fun W i k => (hLRe W i k).aestronglyMeasurable
  have hUL0 : ∀ (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1) :=
    fun W a => (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm
      (s - (n : ℤ)) a Y W).1
  have hLR0 : ∀ (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2) :=
    fun W a => (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm
      (s - (n : ℤ)) a Y W).2
  have hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1)) P :=
    fun W => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).upperLeft) Y.1 (hULe W)
  have hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2)) P :=
    fun W => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffMinus F a)).lowerRight) Y.2 (hLRe W)
  exact integral_avsum_sq_head_descendant_le_respCoeffMinus P hstat jStar F H n s hjs Y
    hUL hLR hULe hLRe hmeas hmeas' hUL0 hLR0
    (fun W => integrable_sqrt_mul_sqrt_gen (hUL0 W) (hLR0 W) (hUL W) (hLR W))
    (fun W => integrable_sq_sqrt_add_sqrt_gen (hUL0 W) (hLR0 W) (hUL W) (hLR W))

/-- **The annealed head of a descendant generation is at most the corresponding layer of the
source load, plus sign, at the carriers.**  The expectation of the flat average over the
depth-`(H+n)` aligned cells of the squared pathwise two-term head of `a_- = a - g` is at most the
flat average over the generation-`n` cells of the squared annealed two-term head, i.e. the
generation-`n` layer of `𝓛_s^-` of `p.response.transfer`. -/
theorem integral_avsum_sq_head_descendant_le_respCoeffPlus_car {d : ℕ} [NeZero d]
    (hd : 2 ≤ d) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (hstat : IsStationaryLaw P) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
    (Src : CoeffSpace d → ℝ) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H n : ℕ) (s : ℤ) (hjs : (jStar : ℤ) ≤ s)
    (Y : BlockVec d) :
    (∫ a, (((triadicIndexBox d (H + n)).card : ℝ))⁻¹ * ∑ W ∈ triadicIndexBox d (H + n),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffPlus F a)).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul
              (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
                (respCoeffPlus F a)).lowerRight Y.2))) ^ 2 ∂P)
      ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).upperLeft Y.1))
            + Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z)
                  (respCoeffPlus F)).lowerRight Y.2))) ^ 2 := by
  have hblk : ∀ W : Fin d → ℤ, HasIntegrableCoarseBlock P
      (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W) :=
    fun W => hasIntegrableCoarseBlock_adaptedCellAtCenter_respGrid hd P γ E Ψ Kg Src hstat hdag jStar
      hjStar F hm (s - (n : ℤ)) W
  have hULe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft i k) P :=
    fun W => integrable_coarseBlockMatrix_upperLeft_respCoeffPlus P jStar hjStar F hm
      (s - (n : ℤ)) W (hblk W)
  have hLRe : ∀ W : Fin d → ℤ, ∀ i k : Fin d, Integrable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight i k) P :=
    fun W => integrable_coarseBlockMatrix_lowerRight_respCoeffPlus P jStar hjStar F hm
      (s - (n : ℤ)) W (hblk W)
  have hmeas : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft i k) P :=
    fun W i k => (hULe W i k).aestronglyMeasurable
  have hmeas' : ∀ W : Fin d → ℤ, ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight i k) P :=
    fun W i k => (hLRe W i k).aestronglyMeasurable
  have hUL0 : ∀ (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1) :=
    fun W a => (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm
      (s - (n : ℤ)) a Y W).1
  have hLR0 : ∀ (W : Fin d → ℤ) (a : CoeffSpace d), 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2) :=
    fun W a => (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm
      (s - (n : ℤ)) a Y W).2
  have hUL : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1)) P :=
    fun W => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).upperLeft) Y.1 (hULe W)
  have hLR : ∀ W : Fin d → ℤ, Integrable (fun a => vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2)) P :=
    fun W => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) W)
        (respCoeffPlus F a)).lowerRight) Y.2 (hLRe W)
  exact integral_avsum_sq_head_descendant_le_respCoeffPlus P hstat jStar F H n s hjs Y
    hUL hLR hULe hLRe hmeas hmeas' hUL0 hLR0
    (fun W => integrable_sqrt_mul_sqrt_gen (hUL0 W) (hLR0 W) (hUL W) (hLR W))
    (fun W => integrable_sq_sqrt_add_sqrt_gen (hUL0 W) (hLR0 W) (hUL W) (hLR W))

end

end Homogenization.HighContrast.Multiscale
