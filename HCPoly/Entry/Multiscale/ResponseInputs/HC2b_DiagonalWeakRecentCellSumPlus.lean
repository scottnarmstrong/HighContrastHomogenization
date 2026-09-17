import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentCellSum

/-!
# The `weakCellSum` half of the recent head for the adjoint sample

This is the adjoint (`a_+ = aᵗ + g`) twin of the `weakCellSum` half of the recent-head
cell-defect estimate `e.response.weak.estimate`.  The normalized finite-cell root-mean-square
of the child-optimizer mean defects is the reflected coarse-block defect action of the adjoint
coefficient `a_+ = respCoeffPlus F a` at the adjoint load `x^+ = (-p, q^+)`; summing the
per-depth bound against the weights `3^{-n/2}` over the window `n ≤ H` produces exactly
`weakCellSum`, with the printed prefactor
`√‖M_0^{-1/2} Ê_+^t M_0^{-1/2}‖ · L^+`.

The only inputs that are specialised to the recentred (minus) carriers are the two mean
identities for the optimizer field; their adjoint counterparts are provided here.  Every
reflected-defect comparison it consumes is stated for a generic coefficient field, block and
load, and so applies to the adjoint sample unchanged.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter blockSub normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The adjoint optimizer-mean identities -/

/-- The adjoint twin of the optimizer-mean identity on an aligned adapted subcell: the cell average of
the optimizer field for `a_+ = aᵗ + g` equals the block response mean of the coarse block matrix
at the adjoint loading `(-p, r)`.  The elliptic datum is the a.e.-representative one, so no
ellipticity hypothesis is added. -/
theorem h6a_cellAverage_optimizerField_respCoeffPlus_eq_at
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) (u : AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter q k w))
    (hu : IsResponseMaximizer (adaptedCellAtCenter q k w) p r (respCoeffPlus F a) u) :
    cellAverage (adaptedCellAtCenter q k w) (optimizerField (respCoeffPlus F a) u) =
      blockResponseMean
        (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffPlus F a)) (-p, r) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (adaptedCellAtCenter q k w) (fun x => matTranspose (f x) + respg F) :=
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F)
  refine cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w)
    (volume_adaptedCellAtCenter_toReal_pos q hq k w) hEll' ?_ p r u hu
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffPlus, hx]

/-- The adjoint optimizer-mean identity on the centred cell `U_t`: the cell average of the optimizer
field for `a_+ = aᵗ + g` equals the block response mean of the coarse block matrix at `(-p, r)`. -/
theorem h6a_cellAverage_optimizerField_respCoeffPlus_eq
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u) :
    cellAverage (HighContrast.adaptedCell q t) (optimizerField (respCoeffPlus F a) u) =
      blockResponseMean
        (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a)) (-p, r) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (HighContrast.adaptedCell q t) (fun x => matTranspose (f x) + respg F) :=
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F)
  refine cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (adaptedCell_isOpenBoundedConvexDomain q hq t) ?_ hEll' ?_ p r u hu
  · have hset : HighContrast.adaptedCell q t =
        translateSet 0 ((matVecMul q) '' (openCubeSet (originCube d t))) := by
      rw [← Annealed.adaptedCellTranslate_eq_cg_affine q t 0]
      simp [HighContrast.adaptedCellTranslate]
    rw [hset]; exact volume_affine_openCube_toReal_pos q hq t 0
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]

/-- The adjoint pointwise comparison identity: the child-cell minus parent-cell optimizer mean
difference for `a_+ = aᵗ + g` is exactly the reflected action of the coarse-block defect that
`weakCellDefect` normalizes. -/
theorem h6a_cellAverage_optimizerField_respCoeffPlus_sub_eq
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (k : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (v : AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter q k w))
    (hv : IsResponseMaximizer (adaptedCellAtCenter q k w) p r (respCoeffPlus F a) v)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffPlus F a) u) :
    cellAverage (adaptedCellAtCenter q k w) (optimizerField (respCoeffPlus F a) v) -
        cellAverage (HighContrast.adaptedCell q t) (optimizerField (respCoeffPlus F a) u) =
      blockMatVecMul (blockSwap d)
        (blockMatVecMul
          (blockSub (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffPlus F a))
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffPlus F a))) (-p, r)) := by
  rw [h6a_cellAverage_optimizerField_respCoeffPlus_eq_at q hq k w F a p r v hv,
    h6a_cellAverage_optimizerField_respCoeffPlus_eq q hq t F a p r u hu,
    blockResponseMean_sub_blockResponseMean]

/-! ## Adjoint child maximizer selection -/

/-- Nonemptiness of an aligned adapted subcell. -/
private theorem h6a_adaptedCellAtCenter_nonempty (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) : (adaptedCellAtCenter q k w).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hpos := volume_adaptedCellAtCenter_toReal_pos q hq k w
  rw [h] at hpos
  simp at hpos

/-- Existence of a canonical maximizer for `a_+ = aᵗ + g` on every aligned adapted subcell; the
adjoint twin of the subcell maximizer-existence lemma for `a_- = a - g`. -/
theorem h6a_nonempty_scalarCanonicalMaximizer_respCoeffPlus_at
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q k w) p r (respCoeffPlus F a)) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (adaptedCellAtCenter q k w) (fun x => matTranspose (f x) + respg F) :=
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F)
  have hbase : Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q k w) p r
      (fun x => matTranspose (f x) + respg F)) :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
      (h6a_adaptedCellAtCenter_nonempty q hq k w) (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w)
      hEll' p r
  refine nonempty_scalarCanonicalMaximizer_of_aeEq ?_ p r hbase
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffPlus, hx]

/-- Child response maximizers for the adjoint coefficient can be chosen simultaneously at every
depth and cell label. -/
theorem h6a_nonempty_childMaximizerFamily_plus
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) :
    Nonempty ((n : ℕ) → (w : Fin d → ℤ) →
      ScalarCanonicalMaximizer (adaptedCellAtCenter q (t - (n : ℤ)) w) p r
        (respCoeffPlus F a)) := by
  exact ⟨fun n w => Classical.choice
    (h6a_nonempty_scalarCanonicalMaximizer_respCoeffPlus_at q hq (t - (n : ℤ)) w F a p r)⟩

/-! ## The `weakCellSum` half for the adjoint sample -/

/-- **`e.response.weak.estimate`, `weakCellSum` half, at one depth, for `a_+`.**  The normalized
finite-cell root-mean-square of the depth-`n` child-optimizer mean defects, measured in `M_0`, is
bounded by `√K_0 · L^+ · weakCellDefect`, where `K_0 = ‖M_0^{-1/2} Ê_+^t M_0^{-1/2}‖` and
`(L^+)^2 = x^+ · Ê_+^t x^+`. -/
theorem h6a_childMean_defect_avsum_le_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (V : (w : Fin d → ℤ) →
      ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a))
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a)
                    ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a)
                    ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))))
      ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ *
          Real.sqrt (respLsqPlus P jStar F t e) *
          weakCellDefect (respGrid jStar F) t n (respEhatPlus P jStar F t)
            (respCoeffPlus F a) := by
  have hstep : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffPlus F a)
                  ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffPlus F a)
                  ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
        = blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (respCoeffPlus F a))
                    (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
                      (respCoeffPlus F a)))
                  (respxPlus P jStar F t e))))
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (respCoeffPlus F a))
                    (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
                      (respCoeffPlus F a)))
                  (respxPlus P jStar F t e)))) := by
    intro w _
    simp only [respCell]
    rw [h6a_cellAverage_optimizerField_respCoeffPlus_sub_eq (respGrid jStar F) hgrid t
      (t - (n : ℤ)) w F a (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) (V w).isMaximizer u hu]
    rfl
  rw [Finset.sum_congr rfl hstep]
  exact h6a_weakCellDefect_avsum_le' (respGrid jStar F) t n (respCoeffPlus F a) hE
    (respxPlus P jStar F t e)

/-- **`e.response.weak.estimate`, THE `weakCellSum` HALF OF THE RECENT HEAD, for `a_+`.**  For the
adjoint sample `a_+ = respCoeffPlus F a`, the adjoint response matrix
`E_+^t = respEhatPlus P jStar F t` and the adjoint load `x^+`, choosing the child maximizers
simultaneously and summing the per-depth bound against the weights `3^{-n/2}` over the window
`n ≤ H` produces exactly `weakCellSum`, with the printed prefactor
`√‖M_0^{-1/2} Ê_+^t M_0^{-1/2}‖ · L^+`. -/
theorem h6a_weakCellSum_half_le_plus
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (H : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) u)
    (hE : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a),
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffPlus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffPlus F a) u))))
        ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ *
            Real.sqrt (respLsqPlus P jStar F t e) *
            weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F a) := by
  obtain ⟨V⟩ := h6a_nonempty_childMaximizerFamily_plus (respGrid jStar F) hgrid t F a
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
  refine ⟨V, ?_⟩
  set K : ℝ :=
    Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))‖ with hK
  set L : ℝ := Real.sqrt (respLsqPlus P jStar F t e) with hL
  have hterm : ∀ n ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-((n : ℝ) / 2)) *
          Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffPlus F a)
                        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                    cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffPlus F a)
                        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                    cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))))
        ≤ K * L *
            ((3 : ℝ) ^ (-((n : ℝ) / 2)) *
              weakCellDefect (respGrid jStar F) t n (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
    intro n _
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) := Real.rpow_nonneg (by norm_num) _
    have hcell := h6a_childMean_defect_avsum_le_plus P jStar F t e hgrid a n u hu (V n) hE
    calc (3 : ℝ) ^ (-((n : ℝ) / 2)) * _
        ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            (K * L *
              weakCellDefect (respGrid jStar F) t n (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by
          exact mul_le_mul_of_nonneg_left hcell hw
      _ = K * L *
            ((3 : ℝ) ^ (-((n : ℝ) / 2)) *
              weakCellDefect (respGrid jStar F) t n (respEhatPlus P jStar F t)
                (respCoeffPlus F a)) := by ring
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [weakCellSum, Finset.mul_sum]

end

end Homogenization.HighContrast.Multiscale
