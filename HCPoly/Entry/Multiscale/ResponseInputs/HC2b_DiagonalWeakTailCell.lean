import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakParentMapPort
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakSubcellCoeffOn
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCoarseBridge
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCarrierInputs

/-!
# The tail's per-cell hypothesis at the estimate's own carriers

`h6a_scaleTail_carrier` (`HC2b_DiagonalWeakTailCarrier.lean`) is the per-scale older-scale bound
at the estimate's carriers.  Its only analytic input is `hcell`: for every aligned depth-`n`
subcell, the metric square of the transported cell average of the parent optimizer field is
bounded by the printed geometric square times twice the subcell energy average.

`h6a_parentEnergyMap_port` (`HC2b_DiagonalWeakParentMapPort.lean`) proves exactly that shape, but
at a pointwise elliptic representative of the recentred coefficient and with the subcell energy
written through the restricted Chapter-2 solution `z`.  This module supplies that data from the
parent harmonic optimizer and transports the port's conclusion back to the estimate's carrier.

The transport uses the pointwise elliptic representative of the recentred field on the parent
cell (`exists_globally_elliptic_representative_ae_eq_on`): it is the same field on every aligned
subcell, so the parent optimizer is harmonic against it there, and it is a.e. equal to
`respCoeffMinus F a` on the parent cell, so the cell average and the energy density are unchanged.
`Book.Ch02.Solution.ofAEEq` / `aHarmonicFunctionOfAEEqCoeff` and the restriction
`h6a_exists_restrict_solution_adaptedCellAtCenter` produce the restricted Chapter-2 solution.  Finally
`h6a_weakOptimizerEnergy_sq` and a.e. invariance replace the port's energy square by the
estimate's volume average.
-/

open Homogenization.HighContrast (CoeffSpace blockSub coarseBlock
  exists_globally_elliptic_representative_ae_eq_on normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The per-cell hypothesis of the older-scale tail.**  For an invertible selected grid, a
generation `t`, a depth `n`, and a parent harmonic optimizer attached to the recentred response
coefficient, every aligned depth-`n` subcell satisfies the per-cell metric bound of
`h6a_scaleTail_carrier`: the transported cell-average metric square of the parent optimizer field
is at most the printed geometric square times twice its energy average.  The bound is the
port `h6a_parentEnergyMap_port` at a pointwise elliptic representative, transported back along the
a.e. equality of the representative with `respCoeffMinus F a`; the cell-average step and the energy
step are both a.e. invariant. -/
theorem h6a_tailCell_of_bridge (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) u)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
              (optimizerField (respCoeffMinus F a) u x).2)) := by
  classical
  -- A pointwise elliptic representative of the recentred field on the parent cell.
  have hParentConv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hgrid t
  obtain ⟨lam0, Lam0, fa, hlam0, _hle0, hmeas_fa, hEll_fa, hae_fa⟩ :=
    exists_globally_elliptic_representative_ae_eq_on (a := (a.1 : Source.AKL.Field d)) a.2
      hParentConv.isBoundedDomain.isBounded
  let f : CoeffField d := fun x => fa x - respg F
  let Lam' : ℝ := 2 * Lam0 + 2 * ‖respg F‖ ^ 2 / lam0
  have hle' : lam0 ≤ Lam' := by
    have hn : 0 ≤ 2 * ‖respg F‖ ^ 2 / lam0 := by positivity
    dsimp only [Lam']
    linarith
  have hEllFaOf : ∀ (S : Set (Vec d)) (_hS : MeasurableSet S),
      IsEllipticFieldOn lam0 Lam0 S fa := by
    intro S hS
    refine ⟨?_, fun x _ => hEll_fa x⟩
    exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hmeas_fa)).ite hS
        measurable_const
  have hEllOf : ∀ (S : Set (Vec d)) (hS : MeasurableSet S),
      IsEllipticFieldOn lam0 Lam' S f := by
    intro S hS
    have h := isEllipticFieldOn_sub_skew (hEllFaOf S hS) (respg F) (respg_isSkew F)
    simpa only [f, Lam'] using h
  have hae : respCoeffMinus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f := by
    filter_upwards [hae_fa] with x hx
    simp only [respCoeffMinus, f]
    rw [hx]
  have hEllParent : IsEllipticFieldOn lam0 Lam' (respCell jStar F t) f :=
    hEllOf (respCell jStar F t) hParentConv.isOpen.measurableSet
  let parentRepCoeff : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hgrid t) :=
    coeffOnOfIsEllipticFieldOn hlam0 hle' hEllParent
  let aU : (w : Fin d → ℤ) → Book.Ch02.CoeffOn
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) :=
    fun w => coeffOnOfIsEllipticFieldOn hlam0 hle'
      (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)
  let uRep : AHarmonicFunction f (respCell jStar F t) :=
    aHarmonicFunctionOfAEEqCoeff hae u
  let zeroH : AHarmonicFunction f (respCell jStar F t) :=
    ⟨0, isAHarmonicGradient_zero⟩
  -- The parent optimizer on the representative; the branch outside the box is irrelevant and
  -- exists only so that the port's total hypotheses are supplied.
  let uFam : (w : Fin d → ℤ) → AHarmonicFunction (aU w).toCoeffField (respCell jStar F t) :=
    fun w => if hw : w ∈ triadicIndexBox d n then uRep else zeroH
  have hzExists : ∀ (w : Fin d → ℤ), w ∈ triadicIndexBox d n →
      ∃ z : Book.Ch02.Solution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w),
        z.toH1.grad = uRep.toH1.grad := by
    intro w hw
    exact h6a_exists_restrict_solution_adaptedCellAtCenter (respGrid jStar F) hgrid t n hw
      (lam := lam0) (Lam := Lam') (b := parentRepCoeff) (c := aU w) rfl
      (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)
      uRep
  let zFam : (w : Fin d → ℤ) → Book.Ch02.Solution
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) :=
    fun w => if hw : w ∈ triadicIndexBox d n then Classical.choose (hzExists w hw)
      else Book.Ch02.zeroSolution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
        (aU w)
  have hzFam : ∀ w, (zFam w).toH1.grad = (uFam w).toH1.grad := by
    intro w
    by_cases hw : w ∈ triadicIndexBox d n
    · have hz : zFam w = Classical.choose (hzExists w hw) := dif_pos hw
      have hu : uFam w = uRep := dif_pos hw
      rw [hz, hu]
      exact Classical.choose_spec (hzExists w hw)
    · have hz : zFam w = Book.Ch02.zeroSolution
          (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) := dif_neg hw
      have hu : uFam w = zeroH := dif_neg hw
      rw [hz, hu]
      rfl
  have hEllFam : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField :=
    fun w => hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet
  have hcoarseFam : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w)
        = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ))
            w) a) := by
    intro w hw
    have hsub : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hcell : respCoeffMinus F a =ᵐ[volumeMeasureOn
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] f :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) hae
    have hcellSymm : f =ᵐ[volumeMeasureOn
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] respCoeffMinus F a := by
      filter_upwards [hcell] with x hx
      exact hx.symm
    have hae_w : Book.Ch02.CoeffOn.AEEq (aU w)
        (canonicalRespCoeffMinusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a) := by
      show (aU w).toCoeffField =ᵐ[volumeMeasureOn
        ((adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) : Set (Vec d))]
        (canonicalRespCoeffMinusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a).toCoeffField
      rw [canonicalRespCoeffMinusOnAt_toFun]
      exact hcellSymm
    rw [Book.Ch02.coarseBlockMatrix_eq_ofAEEq hae_w]
    exact h6a_hcoarse_minus (respGrid jStar F) hgrid (t - (n : ℤ)) w F a
      (canonicalRespCoeffMinusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a)
      (canonicalRespCoeffMinusOnAt_toFun (respGrid jStar F) hgrid (t - (n : ℤ)) w F a)
  have hport := h6a_parentEnergyMap_port (P := P) (γ := γ) (jStar := jStar) (F := F) (t := t)
    (hgrid := hgrid) (a := a) (n := n) (aU := aU) (V := respCell jStar F t)
    (u := uFam) (z := zFam) (hz := hzFam) (hEll := hEllFam)
    (hm := hm) (hEmean := hEmean) (hEhat := hEhat) (hM0 := hM0) (hbdd := hbdd)
    (hcoarse := hcoarseFam)
  intro w hw
  have h := hport w hw
  have huFam_w : uFam w = uRep := dif_pos hw
  have haU_w : (aU w).toCoeffField = f := rfl
  have huRep_grad : uRep.toH1.grad = u.toH1.grad := rfl
  have hgrad_z : (zFam w).toH1.grad = u.toH1.grad := by
    rw [hzFam w, huFam_w]
    exact huRep_grad
  have hcellAvg : cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (optimizerField (aU w).toCoeffField (uFam w))
      = cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (optimizerField (respCoeffMinus F a) u) := by
    refine cellAverage_congr_ae (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) ?_
    filter_upwards [hae.symm] with x hx
    rw [huFam_w]
    simp only [optimizerField, huRep_grad, haU_w, hx]
  have haeSub : f =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)]
      respCoeffMinus F a := by
    filter_upwards [MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) le_rfl) hae] with x hx
    exact hx.symm
  have hnn : 0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (fun x => vecDot (optimizerField (aU w).toCoeffField (zFam w) x).1
        (optimizerField (aU w).toCoeffField (zFam w) x).2) :=
    h6a_volumeAverage_energyDensity_nonneg_of_aeEq
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet hlam0
      (hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet)
      (Filter.EventuallyEq.rfl) (zFam w)
  have hEw : weakOptimizerEnergy (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (aU w).toCoeffField (zFam w) ^ 2
      = volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
          (optimizerField (respCoeffMinus F a) u x).2) := by
    refine (h6a_weakOptimizerEnergy_sq (u := zFam w) hnn).trans ?_
    unfold volumeAverage
    congr 1
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [haeSub] with x hx
    simp only [optimizerField, hgrad_z, haU_w]
    rw [← hx]
  rw [hcellAvg, hEw] at h
  exact h

end

end Homogenization.HighContrast.Multiscale
