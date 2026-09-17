import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCellEnergyBound
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import Homogenization.PDE.Harmonic

/-!
# The Fenchel bound on a triadic subcell of the response cell

The cell-average half of AK.HC (2.15) restricted to a triadic subcell `adaptedCellAtCenter q (t - n) w`
of the response cell `U_t = adaptedCell q t`: a field harmonic on the whole cell restricts to the
subcell, its gradient — hence its optimizer field and scalar variation energy integrand — is
unchanged, and the squared doubled cell average of the optimizer field over the subcell is
controlled by the pathwise symmetric energy of the field times any positive constant `K` that
bounds above the quadratic form of the coarse block of `b` on the subcell augmented by the swap
block `𝐑`.
-/

open Homogenization.HighContrast.CG

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cell-average energy bound on a triadic subcell of the response cell: for `v` harmonic on
the response cell `U_t`, the squared doubled cell average over the depth-`n` subcell
`adaptedCellAtCenter q (t - n) w` of its optimizer field is bounded by the pathwise symmetric energy of
the field over that subcell times any positive constant `K` that bounds above the quadratic form of
the coarse block of `b` on the subcell augmented by the swap block `𝐑`.  This is the cell-average
half of AK.HC (2.15) on a subcell of `U_t`; the proof restricts `v` to the subcell and applies the
cell-average bound there. -/
theorem blockVecDot_cellAverage_subcell_le {d : ℕ} [NeZero d]
    {q : Mat d} (hq : IsUnit q) (t : ℤ) (n : ℕ) {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n)
    {lam Lam : ℝ} {b : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) b)
    (v : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (K : ℝ) (hK : 0 < K)
    (hB : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
            + toFullBlockMat (blockSwap d))) X) ≤ K * blockVecDot X X) :
    blockVecDot (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
        (cellAverage (adaptedCellAtCenter q (t - (n : ℤ)) w) (optimizerField b v))
      ≤ K * volumeAverage (adaptedCellAtCenter q (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand b v) := by
  have hConv : IsOpenBoundedConvexDomain (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
    rw [adaptedCellAtCenter, Annealed.adaptedCellTranslate_eq_cg_affine]
    exact isOpenBoundedConvexDomain_affine_openCube q hq (t - (n : ℤ)) _
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) :=
    hConv.isFiniteMeasure_restrict_volume
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hUopen : IsOpen (HighContrast.adaptedCell q t) :=
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) b :=
    hEll.mono hConv.isOpen.measurableSet hVU
  have hvol : 0 < (volume (adaptedCellAtCenter q (t - (n : ℤ)) w)).toReal := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det q).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ (t - (n : ℤ))) d)
  have hgrad :
      (v.restrictOfIsEllipticFieldOn hUopen hConv.isOpen hVU hEllV).toH1.grad =
        v.toH1.grad := by
    rw [AHarmonicFunction.toH1_restrictOfIsEllipticFieldOn]
    simp only [H1Function.restrict]
  simpa only [optimizerField, scalarVariationEnergyIntegrand, hgrad] using!
    (blockVecDot_cellAverage_optimizerField_self_le hConv hEllV hvol
      (v.restrictOfIsEllipticFieldOn hUopen hConv.isOpen hVU hEllV) K hK hB)

end

end Homogenization.HighContrast.Multiscale
