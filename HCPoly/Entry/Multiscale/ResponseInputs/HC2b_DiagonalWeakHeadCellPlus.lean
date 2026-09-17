import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakTailCellPlus

/-!
# The head's per-cell hypothesis at the estimate's own carriers, adjoint sign

`h6a_headCell_of_bridge` supplies the per-cell hypothesis of the recent difference by carrying a
**pointwise elliptic representative** of the recentred coefficient: `IsEllipticFieldOn` is
pointwise, while a point of `CoeffSpace d` is only an a.e. class, so the recentred field cannot be
fed to the port directly.  This module performs the same representative transport for the adjoint
recentred coefficient `a_+ = aᵀ + g`.

The port is `h6a_recentEnergyMap_port_plus`, whose data are the parent optimizer restricted to each
aligned subcell and a child optimizer attached to the same coefficient there.  The difference of
the two optimizer fields is a single doubled state on the subcell, and on the subcell the
pointwise block identity `X · 𝐀 X = 2 ξ · a ξ` converts the port's Chapter-2 difference energy
into the estimate's `2 * volumeAverage` shape.  Both the cell average and the energy average are
a.e. invariant under the representative, so the conclusion returns to `respCoeffPlus F a`.
-/

open Homogenization.HighContrast (CoeffSpace blockSub coarseBlock
  exists_globally_elliptic_representative_ae_eq_on normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The per-cell hypothesis of the head's recent difference, adjoint sign.**  For an invertible
selected grid, a generation `t`, a depth `n`, a parent harmonic optimizer attached to the
transposed recentred response coefficient and a child optimizer on every aligned depth-`n` subcell,
the transported cell-average metric square of the difference of their optimizer fields is at most
the printed geometric square times twice the difference energy average there.

The bound is the recent-difference port `h6a_recentEnergyMap_port_plus` at a pointwise elliptic
representative of `respCoeffPlus F a`, transported back along the a.e. equality of the
representative with `respCoeffPlus F a`.  The port's right-hand side, the Chapter-2 average of the
doubled block energy density of the difference, is converted to the estimate's `2 * volumeAverage`
through the pointwise identity for a doubled state `(ξ, a ξ)`; both the cell average and the energy
average are a.e. invariant, so the conclusion is stated at `respCoeffPlus F a`. -/
theorem h6a_headCell_of_bridge_plus (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → AHarmonicFunction (respCoeffPlus F a)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
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
              (fun x => optimizerField (respCoeffPlus F a) u x -
                optimizerField (respCoeffPlus F a) (v w) x)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (fun x => optimizerField (respCoeffPlus F a) u x -
                optimizerField (respCoeffPlus F a) (v w) x)))
        ≤ (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F)))
            * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 *
          (2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot
              (optimizerField (respCoeffPlus F a) u x -
                optimizerField (respCoeffPlus F a) (v w) x).1
              (optimizerField (respCoeffPlus F a) u x -
                optimizerField (respCoeffPlus F a) (v w) x).2)) := by
  classical
  -- A pointwise elliptic representative of the adjoint recentred field on the parent cell.
  have hParentConv : IsOpenBoundedConvexDomain (respCell jStar F t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hgrid t
  obtain ⟨lam0, Lam0, fa, hlam0, _hle0, hmeas_fa, hEll_fa, hae_fa⟩ :=
    exists_globally_elliptic_representative_ae_eq_on (a := (a.1 : Source.AKL.Field d)) a.2
      hParentConv.isBoundedDomain.isBounded
  let f : CoeffField d := fun x => matTranspose (fa x) + respg F
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
    have h := isEllipticFieldOn_transpose_add_skew (hEllFaOf S hS) (respg F) (respg_isSkew F)
    simpa only [f, Lam'] using h
  have hae : respCoeffPlus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f := by
    filter_upwards [hae_fa] with x hx
    simp only [respCoeffPlus, f]
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
  -- The parent optimizer restricted to each aligned subcell.
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
  have hzFam : ∀ w ∈ triadicIndexBox d n, (zFam w).toH1.grad = uRep.toH1.grad := by
    intro w hw
    dsimp only [zFam]
    rw [dif_pos hw]
    exact Classical.choose_spec (hzExists w hw)
  -- The child optimizer transported along the representative restricted to its subcell.
  have haeSub : ∀ w ∈ triadicIndexBox d n,
      respCoeffPlus F a =ᵐ[volumeMeasureOn
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] f := by
    intro w hw
    exact MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) le_rfl) hae
  let vFam : (w : Fin d → ℤ) → Book.Ch02.Solution
      (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) (aU w) :=
    fun w => if hw : w ∈ triadicIndexBox d n then
        aHarmonicFunctionOfAEEqCoeff (haeSub w hw) (v w)
      else Book.Ch02.zeroSolution (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
        (aU w)
  have hvFam : ∀ w ∈ triadicIndexBox d n, (vFam w).toH1.grad = (v w).toH1.grad := by
    intro w hw
    dsimp only [vFam]
    rw [dif_pos hw]
    rfl
  have hEllFam : ∀ w : Fin d → ℤ, IsEllipticFieldOn (aU w).lam (aU w).Lam
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (aU w).toCoeffField :=
    fun w => hEllOf (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet
  -- The coarse-block identification, exactly as in the adjoint tail module.
  have hcoarseFam : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.coarseBlockMatrix (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (aU w)
        = blockCongr (blockD d) (blockCongr (respG F)
            (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)) := by
    intro w hw
    have hsub : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hcell : respCoeffPlus F a =ᵐ[volumeMeasureOn
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] f :=
      MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) hae
    have hcellSymm : f =ᵐ[volumeMeasureOn
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] respCoeffPlus F a := by
      filter_upwards [hcell] with x hx
      exact hx.symm
    have hae_w : Book.Ch02.CoeffOn.AEEq (aU w)
        (canonicalRespCoeffPlusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a) := by
      show (aU w).toCoeffField =ᵐ[volumeMeasureOn
        ((adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w) : Set (Vec d))]
        (canonicalRespCoeffPlusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a).toCoeffField
      rw [canonicalRespCoeffPlusOnAt_toFun]
      exact hcellSymm
    rw [Book.Ch02.coarseBlockMatrix_eq_ofAEEq hae_w]
    exact h6a_hcoarse_plus (respGrid jStar F) hgrid (t - (n : ℤ)) w F a
      (canonicalRespCoeffPlusOnAt (respGrid jStar F) hgrid (t - (n : ℤ)) w F a)
      (canonicalRespCoeffPlusOnAt_toFun (respGrid jStar F) hgrid (t - (n : ℤ)) w F a)
  -- The two optimizer differences: on the representative, and at the estimate's coefficient.
  let Xf : (w : Fin d → ℤ) → Vec d → BlockVec d :=
    fun w x => optimizerField (aU w).toCoeffField (zFam w) x -
      optimizerField (aU w).toCoeffField (vFam w) x
  let Xr : (w : Fin d → ℤ) → Vec d → BlockVec d :=
    fun w x => optimizerField (respCoeffPlus F a) u x -
      optimizerField (respCoeffPlus F a) (v w) x
  -- The representative and the recentred coefficient agree a.e. on every aligned subcell.
  have hXae : ∀ w ∈ triadicIndexBox d n,
      Xf w =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)] Xr w := by
    intro w hw
    filter_upwards [haeSub w hw] with x hx
    have hg1 : (Xf w x).1 = (Xr w x).1 := by
      simp only [Xf, Xr, optimizerField, Prod.fst_sub]
      rw [hzFam w hw, hvFam w hw]
      rfl
    have hg2 : (Xf w x).2 = (Xr w x).2 := by
      simp only [Xf, Xr, optimizerField, Prod.snd_sub, hx]
      rw [hzFam w hw, hvFam w hw]
      rfl
    exact Prod.ext hg1 hg2
  -- The Chapter-2 difference energy is the doubled pointwise energy on the representative.
  have hAve_f : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x)))
        = 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (Xf w x).1 (Xf w x).2) := by
    intro w hw
    have hpt : Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x)))
        = Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => 2 * vecDot (Xf w x).1 (Xf w x).2) := by
      refine Book.Ch02.average_eq_of_ae_eq ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w).measurableSet] with x hx
      have hdet : IsUnit (symmPart ((aU w).toCoeffField x)).det :=
        isUnit_det_symmPart_of_isEllipticMatrix ((hEllFam w).2 x hx)
      have h2 : (Xf w x).2 = matVecMul ((aU w).toCoeffField x) (Xf w x).1 := by
        simp only [Xf, optimizerField, Prod.fst_sub, Prod.snd_sub]
        rw [matVecMul_sub_vec]
      have hX : Xf w x = ((Xf w x).1, matVecMul ((aU w).toCoeffField x) (Xf w x).1) :=
        Prod.ext rfl h2
      rw [hX, h6a_blockMatrixField_apply (aU w) x,
        h6a_blockEnergyDensity_primal hdet (Xf w x).1]
    rw [hpt]
    show (MeasureTheory.volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)).toReal⁻¹ *
        ∫ x in (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w),
          2 * vecDot (Xf w x).1 (Xf w x).2
      = 2 * ((MeasureTheory.volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)).toReal⁻¹ *
        ∫ x in (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w),
          vecDot (Xf w x).1 (Xf w x).2)
    rw [MeasureTheory.integral_const_mul]
    ring
  -- The representative's difference energy is nonnegative; the difference is a doubled state.
  have hnonneg_f : ∀ w ∈ triadicIndexBox d n,
      0 ≤ volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (fun x => vecDot (Xf w x).1 (Xf w x).2) := by
    intro w hw
    unfold volumeAverage
    refine mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (isOpen_adaptedCellAtCenter_of_isUnit hgrid (t - (n : ℤ)) w).measurableSet] with x hx
    have hslot : (Xf w x).2 = matVecMul ((aU w).toCoeffField x) (Xf w x).1 := by
      simp only [Xf, optimizerField, Prod.fst_sub, Prod.snd_sub]
      rw [matVecMul_sub_vec]
    rw [hslot]
    exact le_trans (mul_nonneg hlam0.le (vecNormSq_nonneg _))
      (((hEllFam w).2 x hx).2.2.1 (Xf w x).1)
  -- The Chapter-2 difference energy at the recentred coefficient.
  have hAve_r : ∀ w ∈ triadicIndexBox d n,
      Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x)))
        = 2 * volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (fun x => vecDot (Xr w x).1 (Xr w x).2) := by
    intro w hw
    rw [hAve_f w hw]
    unfold volumeAverage
    rw [show (∫ x in (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w),
            vecDot (Xf w x).1 (Xf w x).2)
          = ∫ x in (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w),
            vecDot (Xr w x).1 (Xr w x).2 from
        MeasureTheory.integral_congr_ae (by
          filter_upwards [hXae w hw] with x hx
          rw [hx])]
  -- The port's positivity input: the difference energy is nonnegative.
  have hG : ∀ w ∈ triadicIndexBox d n,
      0 ≤ Book.Ch02.average (adaptedDomainAt (respGrid jStar F) hgrid (t - (n : ℤ)) w)
          (fun x => blockVecDot (Xf w x)
            (blockMatVecMul (Book.Ch02.blockMatrixField (aU w) x) (Xf w x))) := by
    intro w hw
    rw [hAve_f w hw]
    exact mul_nonneg (by norm_num) (hnonneg_f w hw)
  have hport := h6a_recentEnergyMap_port_plus (P := P) (γ := γ) (jStar := jStar) (F := F)
    (t := t) (hgrid := hgrid) (a := a) (n := n) (aU := aU) (u := zFam) (v := vFam)
    (hEll := hEllFam) (hm := hm) (hEmean := hEmean) (hEhat := hEhat) (hM0 := hM0)
    (hbdd := hbdd) (hcoarse := hcoarseFam) (hG := hG)
  -- The cell average is a.e. invariant under the representative.
  have hcellAvg : ∀ w ∈ triadicIndexBox d n,
      cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Xf w)
        = cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (Xr w) := by
    intro w hw
    exact cellAverage_congr_ae (subset_refl _) (hXae w hw)
  intro w hw
  have h := hport w hw
  rw [hcellAvg w hw, hAve_r w hw] at h
  exact h

end

end Homogenization.HighContrast.Multiscale
