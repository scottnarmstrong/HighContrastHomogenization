import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectStatCell

/-!
# Entrywise integrability of the coarse block response on every aligned subcell

The stationarity input of the terminal-optimizer replacement of `p.response.transfer` needs the
annealed response on each aligned cell of a fixed scale, so the pathwise response must be
`P`-integrable there for every aligned cell and not only for the centred one.  On an aligned cell
the pathwise response is a quadratic form in the entries of the recentred coarse block, and the
entries of that block are fixed real linear combinations of the entries of the coarse block of
the sample; `HasIntegrableCoarseBlock` therefore transfers to the recentred block and the
response is integrable.  This module records that consequence for the two recentred families
`a_-` and `a_+`.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  blockVecDot_blockMatVecMul_eq_sum coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Entrywise integrability of the response on an aligned subcell, minus sign.**  If every
entry of the coarse block of the sample is `P`-integrable on the aligned cell
`adaptedCellAtCenter q j w` of the scale `3^j q ℤ^d`, then the pathwise response
`ResponseJ (adaptedCellAtCenter q j w) p r a_-` of the recentred coefficient `a_- = a - g` is
`P`-integrable. -/
theorem integrable_responseJ_respCoeffMinus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] {q : Mat d} (hq : IsUnit q)
    (F : BlockMat d) (j : ℤ) (w : Fin d → ℤ) (p r : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    Integrable (fun a => ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffMinus F a)) P := by
  have hquad : ∀ a : CoeffSpace d,
      HasQuadraticMu (adaptedCellAtCenter q j w) (⇑a.1 : CoeffField d) :=
    fun a => by
      simpa only [adaptedCellAtCenter] using
        h7_hasQuadraticMu_adaptedCellTranslate q hq j (adaptedCellCenter q j w) a
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)
        = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q j w) a) :=
    fun a => coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter q j w)
      (a := (⇑a.1 : CoeffField d)) (g := respg F) (respg_isSkew F) (hquad a)
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := respG F)
      (V := adaptedCellAtCenter q j w) (b := respCoeffMinus F) hint hb
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, r) α *
        (blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter q j w)
          (respCoeffMinus F a)) α β * toFullBlockVec (-p, r) β)) P :=
    fun α β =>
      ((hint' α β).mul_const (toFullBlockVec (-p, r) β)).const_mul (toFullBlockVec (-p, r) α)
  have hQint : Integrable (fun a => blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter q j w)
        (respCoeffMinus F a)) (-p, r))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hpath : ∀ a : CoeffSpace d,
      ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffMinus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a))
              (-p, r))
          - vecDot p r :=
    fun a => h6a_responseJ_adaptedCellAtCenter_respCoeffMinus q hq j w F a p r
  have hfun : (fun a => ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffMinus F a))
      = fun a => (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a))
              (-p, r))
          - vecDot p r :=
    funext hpath
  rw [hfun]
  exact (hQint.const_mul (1 / 2 : ℝ)).sub (integrable_const (vecDot p r))

/-- **Entrywise integrability of the response on an aligned subcell, plus sign.**  If every
entry of the coarse block of the sample is `P`-integrable on the aligned cell
`adaptedCellAtCenter q j w` of the scale `3^j q ℤ^d`, then the pathwise response
`ResponseJ (adaptedCellAtCenter q j w) p r a_+` of the transposed recentred coefficient
`a_+ = aᵀ + g` is `P`-integrable. -/
theorem integrable_responseJ_respCoeffPlus_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] {q : Mat d} (hq : IsUnit q)
    (F : BlockMat d) (j : ℤ) (w : Fin d → ℤ) (p r : Vec d)
    (hint : HasIntegrableCoarseBlock P (adaptedCellAtCenter q j w)) :
    Integrable (fun a => ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffPlus F a)) P := by
  have hb : ∀ a : CoeffSpace d,
      coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)
        = blockCongr (h68_respGPlus F) (coarseBlock (adaptedCellAtCenter q j w) a) :=
    fun a => h68_coarseBlockMatrix_respCoeffPlus_at hq j w F a
  have hint' : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry
      (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β) P :=
    integrable_blockMatEntry_coarseBlockMatrix_of_blockCongr (G := h68_respGPlus F)
      (V := adaptedCellAtCenter q j w) (b := respCoeffPlus F) hint hb
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, r) α *
        (blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter q j w)
          (respCoeffPlus F a)) α β * toFullBlockVec (-p, r) β)) P :=
    fun α β =>
      ((hint' α β).mul_const (toFullBlockVec (-p, r) β)).const_mul (toFullBlockVec (-p, r) α)
  have hQint : Integrable (fun a => blockVecDot (-p, r)
      (blockMatVecMul (coarseBlockMatrix (adaptedCellAtCenter q j w)
        (respCoeffPlus F a)) (-p, r))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hpath : ∀ a : CoeffSpace d,
      ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffPlus F a)
        = (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a))
              (-p, r))
          - vecDot p r :=
    fun a => h6a_responseJ_adaptedCellAtCenter_respCoeffPlus q hq j w F a p r
  have hfun : (fun a => ResponseJ (adaptedCellAtCenter q j w) p r (respCoeffPlus F a))
      = fun a => (1 / 2 : ℝ) * blockVecDot (-p, r)
            (blockMatVecMul
              (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a))
              (-p, r))
          - vecDot p r :=
    funext hpath
  rw [hfun]
  exact (hQint.const_mul (1 / 2 : ℝ)).sub (integrable_const (vecDot p r))

end

end Homogenization.HighContrast.Multiscale
