import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectMeanCancel
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock

/-!
# The constant cell means cancel after expectation

In the cell half of the cutoff-mean row of `p.response.transfer`, the weighted flat average, over
the coarse subcells of the terminal cell, of the ANNEALED cell means of each subcell's own
optimizer state vanishes.  Above the scale `j_*` the subcells are integer translates of one
another and the law is stationary, so the annealed block of every subcell agrees; the pathwise cell
mean of the optimizer state is `x + R 𝐀 x` (`AK.HC (2.32)`), and its expectation is
`x + R 𝐀̄ x` with the common annealed block `𝐀̄`.  The weights — the subcell means of the cutoff
fluctuation `φ - 1` — have normalized sum zero because the cutoff has mean one on the terminal cell.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Mean-zero weighting of a common expectation.**  If the weights `c` have normalized sum zero
and every cell functional `G w` has the same law-integral `m`, then the normalized weighted sum of
the integrals vanishes.  This packages the elementary finite-sum manipulation together with
`integral_avsum_mul_eq_zero`; it is the expectation form of the cancellation in
`p.response.transfer`. -/
private theorem normalized_integral_weighted_eq_zero {d : ℕ}
    (P : Measure (CoeffSpace d)) (n : ℕ) (c : (Fin d → ℤ) → ℝ)
    (G : (Fin d → ℤ) → CoeffSpace d → ℝ) (m : ℝ)
    (hc : (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w = 0)
    (hG : ∀ w ∈ triadicIndexBox d n, (∫ a, G w a ∂P) = m)
    (hint : ∀ w ∈ triadicIndexBox d n, Integrable (G w) P) :
    (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, c w * (∫ a, G w a ∂P) = 0 := by
  have hlin : (∫ a, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * G w a ∂P)
      = (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, c w * (∫ a, G w a ∂P) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum _ (fun w hw => (hint w hw).const_mul (c w))]
    exact Finset.sum_congr rfl fun w _ => by rw [integral_const_mul]
  rw [← hlin]
  exact integral_avsum_mul_eq_zero P n c G m hc hG hint

/-- **The weighted cell means of the subcell optimizers cancel, negative sign.**  In the cell half
of the cutoff-mean row of `p.response.transfer`, let the cell mean of the doubled optimizer state of
each coarse subcell `U_w` of the terminal cell `U_t` be the block response of the recentred
coefficient `a_- = a - g` at the load `x^- = (-p, q^-)`, with a common annealed block `A` above
`j_*`.  Then the normalized sum, over the subcells, of the subcell mean of `φ - 1` times the
expectation of each coordinate of that optimizer mean is zero.  The expectation of `x^- + R 𝐀 x^-`
is `x^- + R A x^-` at every subcell by `integral_blockResponseMean`, because the subcell's annealed
block is `A`; the weights have normalized sum zero by `avsum_volumeAverage_sub_one_eq_zero`, the
cutoff having mean one. -/
theorem avsum_weighted_integral_cellAverage_subcellOptimizer_eq_zero {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (hq : IsUnit (respGrid jStar F)) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (ht : t = s + (H : ℤ))
    (Mv : (Fin d → ℤ) → CoeffSpace d → BlockVec d)
    (A : BlockMat d)
    (hMv : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      Mv w a = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)) (-respP (respMean P jStar F t) e, respqMinus P jStar F t e))
    (hann : ∀ w ∈ triadicIndexBox d H,
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F) = A)
    (hint : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (Mv w a).1 i) P ∧ Integrable (fun a => (Mv w a).2 i) P)
    (hblkint : ∀ w ∈ triadicIndexBox d H,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hquad : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      HasQuadraticMu (adaptedCellAtCenter (respGrid jStar F) s w) (⇑a.1 : CoeffField d)) :
    (∀ i : Fin d, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
          * ∫ a, (Mv w a).1 i ∂P = 0)
      ∧ (∀ i : Fin d, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
          * ∫ a, (Mv w a).2 i ∂P = 0) := by
  have hts : t - (H : ℤ) = s := by omega
  have hφint : IntegrableOn φ (HighContrast.adaptedCell (respGrid jStar F) t) :=
    ((hφ.contDiff.continuous).integrable_of_hasCompactSupport hφ.hasCompactSupport).integrableOn
  have hVfin : volume (HighContrast.adaptedCell (respGrid jStar F) t) ≠ ⊤ := by
    rw [← adaptedCellTranslate_zero (respGrid jStar F) t]
    exact Geometry.volume_adaptedCellTranslate_ne_top (respGrid jStar F) t 0
  have hintφ : IntegrableOn (fun x => φ x - 1) (HighContrast.adaptedCell (respGrid jStar F) t) :=
    hφint.sub (integrableOn_const hVfin)
  have hvol : (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal ≠ 0 := by
    rw [Geometry.volume_adaptedCell_toReal]
    exact mul_ne_zero
      (abs_ne_zero.mpr (IsUnit.ne_zero
        ((Matrix.isUnit_iff_isUnit_det (respGrid jStar F)).mp hq)))
      (pow_ne_zero _ (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 3) t)))
  have hc : (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0 := by
    have h := avsum_volumeAverage_sub_one_eq_zero (qq := respGrid jStar F) hq t H hφ hintφ hvol hφint
    simpa only [hts] using h
  have hA : ∀ w ∈ triadicIndexBox d H, ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)) α β) P := by
    intro w hw
    have hb : ∀ a : CoeffSpace d,
        coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)
          = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) s w) a) :=
      fun a => coarseBlockMatrix_sub_skew_eq_blockCongr (respg_isSkew F) (hquad w hw a)
    exact integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (respG F) (hblkint w hw) hb
  constructor
  · intro i
    refine normalized_integral_weighted_eq_zero P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => (Mv w a).1 i)
      ((blockResponseMean A (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i)
      hc ?_ ?_
    · intro w hw
      have hpath : (∫ a, (Mv w a).1 i ∂P)
          = ∫ a, (blockResponseMean (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a))
              (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i ∂P := by
        apply integral_congr_ae
        filter_upwards with a
        rw [hMv w hw a]
      rw [hpath]
      have hpair := integral_blockResponseMean P (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F) (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)
        (hA w hw)
      have h1 : (∫ a, (blockResponseMean (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a))
            (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i ∂P)
          = (blockResponseMean (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w)
              (respCoeffMinus F))
              (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i :=
        congrFun (congrArg Prod.fst hpair) i
      rw [h1]
      exact congrArg (fun M : BlockMat d => (blockResponseMean M
        (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).1 i) (hann w hw)
    · intro w hw
      exact (hint w hw i).1
  · intro i
    refine normalized_integral_weighted_eq_zero P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => (Mv w a).2 i)
      ((blockResponseMean A (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i)
      hc ?_ ?_
    · intro w hw
      have hpath : (∫ a, (Mv w a).2 i ∂P)
          = ∫ a, (blockResponseMean (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a))
              (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i ∂P := by
        apply integral_congr_ae
        filter_upwards with a
        rw [hMv w hw a]
      rw [hpath]
      have hpair := integral_blockResponseMean P (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F) (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)
        (hA w hw)
      have h1 : (∫ a, (blockResponseMean (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a))
            (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i ∂P)
          = (blockResponseMean (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w)
              (respCoeffMinus F))
              (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i :=
        congrFun (congrArg Prod.snd hpair) i
      rw [h1]
      exact congrArg (fun M : BlockMat d => (blockResponseMean M
        (-respP (respMean P jStar F t) e, respqMinus P jStar F t e)).2 i) (hann w hw)
    · intro w hw
      exact (hint w hw i).2

/-- **The weighted cell means of the subcell optimizers cancel, adjoint sign.**  The adjoint twin of
`avsum_weighted_integral_cellAverage_subcellOptimizer_eq_zero` for the recentred coefficient
`a_+ = aᵗ + g` at the load `x^+ = (-p, q^+)`: the normalized sum, over the coarse subcells of the
terminal cell, of the subcell mean of `φ - 1` times the expectation of each coordinate of the
optimizer mean vanishes, for the adjoint coarse block. -/
theorem avsum_weighted_integral_cellAverage_subcellOptimizerPlus_eq_zero {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
    (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (hq : IsUnit (respGrid jStar F)) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (ht : t = s + (H : ℤ))
    (Mv : (Fin d → ℤ) → CoeffSpace d → BlockVec d)
    (A : BlockMat d)
    (hMv : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      Mv w a = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)) (-respP (respMean P jStar F t) e, respqPlus P jStar F t e))
    (hann : ∀ w ∈ triadicIndexBox d H,
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F) = A)
    (hint : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (Mv w a).1 i) P ∧ Integrable (fun a => (Mv w a).2 i) P)
    (hblkint : ∀ w ∈ triadicIndexBox d H,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hquad : ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      HasQuadraticMu (adaptedCellAtCenter (respGrid jStar F) s w) (⇑a.1 : CoeffField d)) :
    (∀ i : Fin d, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
          * ∫ a, (Mv w a).1 i ∂P = 0)
      ∧ (∀ i : Fin d, ((triadicIndexBox d H).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)
          * ∫ a, (Mv w a).2 i ∂P = 0) := by
  have hts : t - (H : ℤ) = s := by omega
  have hφint : IntegrableOn φ (HighContrast.adaptedCell (respGrid jStar F) t) :=
    ((hφ.contDiff.continuous).integrable_of_hasCompactSupport hφ.hasCompactSupport).integrableOn
  have hVfin : volume (HighContrast.adaptedCell (respGrid jStar F) t) ≠ ⊤ := by
    rw [← adaptedCellTranslate_zero (respGrid jStar F) t]
    exact Geometry.volume_adaptedCellTranslate_ne_top (respGrid jStar F) t 0
  have hintφ : IntegrableOn (fun x => φ x - 1) (HighContrast.adaptedCell (respGrid jStar F) t) :=
    hφint.sub (integrableOn_const hVfin)
  have hvol : (volume (HighContrast.adaptedCell (respGrid jStar F) t)).toReal ≠ 0 := by
    rw [Geometry.volume_adaptedCell_toReal]
    exact mul_ne_zero
      (abs_ne_zero.mpr (IsUnit.ne_zero
        ((Matrix.isUnit_iff_isUnit_det (respGrid jStar F)).mp hq)))
      (pow_ne_zero _ (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 3) t)))
  have hc : (((triadicIndexBox d H).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d H,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1) = 0 := by
    have h := avsum_volumeAverage_sub_one_eq_zero (qq := respGrid jStar F) hq t H hφ hintφ hvol hφint
    simpa only [hts] using h
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    ext i j
    have h := congrFun (congrFun (respg_isSkew F) i) j
    simp only [matTranspose, Matrix.transpose_apply, Matrix.neg_apply] at h ⊢
    linarith [h]
  have hA : ∀ w ∈ triadicIndexBox d H, ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)) α β) P := by
    intro w hw
    have hb : ∀ a : CoeffSpace d,
        coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)
          = blockCongr (ofFullBlockMat (toFullBlockMat (blockD d) *
              toFullBlockMat (⟨1, 0, -respg F, 1⟩ : BlockMat d)))
              (coarseBlock (adaptedCellAtCenter (respGrid jStar F) s w) a) := by
      intro a
      have h1 : respCoeffPlus F a
          = fun x => (adjointCoeffField (⇑a.1 : CoeffField d)) x - (-(respg F)) := by
        funext x
        simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
      have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr
        (U := adaptedCellAtCenter (respGrid jStar F) s w)
        (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
        (hasQuadraticMu_adjointCoeffField (hquad w hw a))
      have h3 : coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
            (adjointCoeffField (⇑a.1 : CoeffField d))
          = blockCongr (blockD d) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) s w) a) := by
        rw [coarseBlockMatrix_adjointCoeffField_of_exists
          (exists_coarseBlockMatrix_of_hasQuadraticMu (hquad w hw a)), ← blockCongr_blockD]
        rfl
      rw [h1, h2, h3, blockCongr_blockCongr]
    exact integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr _ (hblkint w hw) hb
  constructor
  · intro i
    refine normalized_integral_weighted_eq_zero P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => (Mv w a).1 i)
      ((blockResponseMean A (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i)
      hc ?_ ?_
    · intro w hw
      have hpath : (∫ a, (Mv w a).1 i ∂P)
          = ∫ a, (blockResponseMean (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a))
              (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i ∂P := by
        apply integral_congr_ae
        filter_upwards with a
        rw [hMv w hw a]
      rw [hpath]
      have hpair := integral_blockResponseMean P (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F) (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)
        (hA w hw)
      have h1 : (∫ a, (blockResponseMean (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a))
            (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i ∂P)
          = (blockResponseMean (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w)
              (respCoeffPlus F))
              (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i :=
        congrFun (congrArg Prod.fst hpair) i
      rw [h1]
      exact congrArg (fun M : BlockMat d => (blockResponseMean M
        (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).1 i) (hann w hw)
    · intro w hw
      exact (hint w hw i).1
  · intro i
    refine normalized_integral_weighted_eq_zero P H
      (fun w => volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
      (fun w a => (Mv w a).2 i)
      ((blockResponseMean A (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i)
      hc ?_ ?_
    · intro w hw
      have hpath : (∫ a, (Mv w a).2 i ∂P)
          = ∫ a, (blockResponseMean (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a))
              (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i ∂P := by
        apply integral_congr_ae
        filter_upwards with a
        rw [hMv w hw a]
      rw [hpath]
      have hpair := integral_blockResponseMean P (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F) (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)
        (hA w hw)
      have h1 : (∫ a, (blockResponseMean (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a))
            (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i ∂P)
          = (blockResponseMean (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) s w)
              (respCoeffPlus F))
              (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i :=
        congrFun (congrArg Prod.snd hpair) i
      rw [h1]
      exact congrArg (fun M : BlockMat d => (blockResponseMean M
        (-respP (respMean P jStar F t) e, respqPlus P jStar F t e)).2 i) (hann w hw)
    · intro w hw
      exact (hint w hw i).2

end

end Homogenization.HighContrast.Multiscale

