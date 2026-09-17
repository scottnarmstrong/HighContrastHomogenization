import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportMaxBridge
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCanRead
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportTsumMeas
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm

/-!
# Measurability of the weak-quantity integrand of the response estimate

The weak quantity `W^\pm` of `e.response.weak.estimate` is the sample expectation of the square of
the scale-average seminorm `besovSeminorm` of the recentred, canonically-metric-scaled cell averages
of the doubled optimizer state `X_t^\pm`.  This file records that this integrand is
`AEStronglyMeasurable` in the coefficient sample.

The doubled optimizer state of an arbitrary response maximizer is determined almost everywhere on
the response cell by the Chapter-2 canonical maximizer, by a.e. gradient uniqueness for response
maximizers (AK.HC (2.9)); the canonical choice depends measurably on the sample by the Galerkin
selection construction; and the scale-average seminorm is a countable sum of finite sums of
measurable terms.  The family is summed only over the triadic index box, so its entries outside the
box may be replaced by a constant before applying the sum-measurability result.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The integrand `a ↦ [M_0^{1/2} (X_t^\pm(a) - Y)]^2` of the weak quantity
`e.response.weak.estimate` is almost-everywhere strongly measurable in the coefficient sample, for
an arbitrary family of response maximizers `u`.  The cell averages entering the doubled optimizer
state are the canonically selected ones up to a null set, and the canonical selection is measurable
in the sample. -/
theorem aestronglyMeasurable_besovSeminorm_sq_of_maximizer {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (c : CoeffSpace d → CoeffField d)
    (hc : c = respCoeffMinus F ∨ c = respCoeffPlus F)
    (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a)) :
    AEStronglyMeasurable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  -- The canonical optimizer state is a.e. a function of the coefficient's a.e. class.
  have hstate_aeeq : ∀ {A B : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t)},
      Book.Ch02.CoeffOn.AEEq A B → ∀ p r : Vec d,
      canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p r
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) B p r := by
    intro A B hAB p r
    have hgrad : (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) A)
          p r).toSolution.toH1.grad
        =ᵐ[volumeMeasureOn ((adaptedDomain (respGrid jStar F) hq t) : Set (Vec d))]
        (Book.Ch02.canonicalMaximizer
          (Book.Ch02.responseExistenceTheory (adaptedDomain (respGrid jStar F) hq t) B)
          p r).toSolution.toH1.grad := by
      simpa only [Book.Ch02.Solution.SameGradientAE, Book.Ch02.Solution.toH1_ofAEEq] using
        (Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq hAB p r)
    filter_upwards [hgrad, hAB] with x hgradx hcoeffx
    simp only [canonicalOptimizerBlockState]
    rw [hgradx, hcoeffx]
  rcases hc with rfl | rfl
  · -- the minus recentring
    have hcell_eq : ∀ (a : CoeffSpace d) (V : Set (Vec d)),
        V ⊆ (adaptedDomain (respGrid jStar F) hq t : Set (Vec d)) →
        cellAverage V (optimizerField (respCoeffMinus F a) (u a))
          = cellAverage V (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q') := by
      intro a V hVU
      obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
        exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
      let A : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t) :=
        coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll
      have hAB : Book.Ch02.CoeffOn.AEEq A
          (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) := by
        filter_upwards [hbf.symm] with x hx
        simpa only [canonicalRespCoeffMinusOn_toFun] using! hx
      calc cellAverage V (optimizerField (respCoeffMinus F a) (u a))
          = cellAverage V (optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p q')) :=
            cellAverage_optimizerField_eq_canonical (U := adaptedDomain (respGrid jStar F) hq t)
              hVU hlam hle hEll hbf p q' (u a) (hu a)
        _ = cellAverage V
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p q') := by
            apply congrArg (cellAverage V)
            funext x
            rfl
        _ = cellAverage V (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q') :=
            cellAverage_congr_ae hVU (hstate_aeeq hAB p q')
    have hcoord : ∀ (n : ℕ) (w : Fin d → ℤ), w ∈ triadicIndexBox d n → ∀ i : Fin d,
        Measurable (fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (u a))).1 i) ∧
        Measurable (fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (u a))).2 i) := by
      intro n w hw i
      have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w
          ⊆ (adaptedDomain (respGrid jStar F) hq t : Set (Vec d)) :=
        adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
      have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
        (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
      constructor
      · have h1 : (fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (u a))).1 i)
            = fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q')).1 i := by
          funext a
          rw [hcell_eq a _ hVU]
        rw [h1]
        simpa only [toFullBlockVec, cellAverage] using
          (measurable_cellAverage_canonicalRespCoeffMinus (respGrid jStar F) hq t F p q'
            (Sum.inl i) hVmeas hVU)
      · have h1 : (fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (u a))).2 i)
            = fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q')).2 i := by
          funext a
          rw [hcell_eq a _ hVU]
        rw [h1]
        simpa only [toFullBlockVec, cellAverage] using
          (measurable_cellAverage_canonicalRespCoeffMinus (respGrid jStar F) hq t F p q'
            (Sum.inr i) hVmeas hVU)
    set avg : CoeffSpace d → ℕ → (Fin d → ℤ) → BlockVec d :=
      (fun a n w => if w ∈ triadicIndexBox d n
        then blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffMinus F a) (u a)) - Y)
        else 0) with havg
    have havg1 : ∀ n w i, Measurable fun a : CoeffSpace d => (avg a n w).1 i := by
      intro n w i
      by_cases hw : w ∈ triadicIndexBox d n
      · have hsplit : (fun a : CoeffSpace d => (avg a n w).1 i)
            = fun a : CoeffSpace d => (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a) (u a)) - Y)).1 i := by
          funext a
          simp only [havg, if_pos hw]
        rw [hsplit]
        have hW : Measurable fun a : CoeffSpace d =>
            cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (u a)) :=
          Measurable.prod
            (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).1))
            (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).2))
        have hZ : Measurable fun a : CoeffSpace d =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffMinus F a) (u a)) - Y) :=
          (blockMatContinuousLinearMap (blockSqrt (respM0 F))).continuous.measurable.comp
            (hW.sub measurable_const)
        exact (measurable_pi_apply i).comp hZ.fst
      · have hsplit : (fun a : CoeffSpace d => (avg a n w).1 i) = fun _ => (0 : ℝ) := by
          funext a
          simp only [havg, if_neg hw]
          rfl
        rw [hsplit]
        exact measurable_const
    have havg2 : ∀ n w i, Measurable fun a : CoeffSpace d => (avg a n w).2 i := by
      intro n w i
      by_cases hw : w ∈ triadicIndexBox d n
      · have hsplit : (fun a : CoeffSpace d => (avg a n w).2 i)
            = fun a : CoeffSpace d => (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a) (u a)) - Y)).2 i := by
          funext a
          simp only [havg, if_pos hw]
        rw [hsplit]
        have hW : Measurable fun a : CoeffSpace d =>
            cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (u a)) :=
          Measurable.prod
            (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).1))
            (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).2))
        have hZ : Measurable fun a : CoeffSpace d =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffMinus F a) (u a)) - Y) :=
          (blockMatContinuousLinearMap (blockSqrt (respM0 F))).continuous.measurable.comp
            (hW.sub measurable_const)
        exact (measurable_pi_apply i).comp hZ.snd
      · have hsplit : (fun a : CoeffSpace d => (avg a n w).2 i) = fun _ => (0 : ℝ) := by
          funext a
          simp only [havg, if_neg hw]
          rfl
        rw [hsplit]
        exact measurable_const
    refine Measurable.aestronglyMeasurable ?_
    have hgoal : (fun a : CoeffSpace d => besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField (respCoeffMinus F a) (u a)) - Y)) ^ 2)
        = fun a : CoeffSpace d => besovSeminorm t (avg a) ^ 2 := by
      funext a
      exact congrArg (fun x : ℝ => x ^ 2)
        (besovSeminorm_congr (fun n w hw => by simp only [havg, if_pos hw]))
    rw [hgoal]
    have hbase := measurable_besovSeminorm t havg1 havg2
    simpa only [pow_two] using! hbase.mul hbase
  · -- the plus recentring
    have hcell_eq : ∀ (a : CoeffSpace d) (V : Set (Vec d)),
        V ⊆ (adaptedDomain (respGrid jStar F) hq t : Set (Vec d)) →
        cellAverage V (optimizerField (respCoeffPlus F a) (u a))
          = cellAverage V (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q') := by
      intro a V hVU
      obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ :=
        exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
      let A : Book.Ch02.CoeffOn (adaptedDomain (respGrid jStar F) hq t) :=
        coeffOnOfIsEllipticFieldOn (U := adaptedDomain (respGrid jStar F) hq t) hlam hle hEll
      have hAB : Book.Ch02.CoeffOn.AEEq A
          (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) := by
        filter_upwards [hbf.symm] with x hx
        simpa only [canonicalRespCoeffPlusOn_toFun] using! hx
      calc cellAverage V (optimizerField (respCoeffPlus F a) (u a))
          = cellAverage V (optimizerField f (canonicalAHarmonicFunctionOfCoeffOn A p q')) :=
            cellAverage_optimizerField_eq_canonical (U := adaptedDomain (respGrid jStar F) hq t)
              hVU hlam hle hEll hbf p q' (u a) (hu a)
        _ = cellAverage V
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t) A p q') := by
            apply congrArg (cellAverage V)
            funext x
            rfl
        _ = cellAverage V (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q') :=
            cellAverage_congr_ae hVU (hstate_aeeq hAB p q')
    have hcoord : ∀ (n : ℕ) (w : Fin d → ℤ), w ∈ triadicIndexBox d n → ∀ i : Fin d,
        Measurable (fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (u a))).1 i) ∧
        Measurable (fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (u a))).2 i) := by
      intro n w hw i
      have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w
          ⊆ (adaptedDomain (respGrid jStar F) hq t : Set (Vec d)) :=
        adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
      have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
        (isOpen_adaptedCellAtCenter_of_isUnit hq _ w).measurableSet
      constructor
      · have h1 : (fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (u a))).1 i)
            = fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q')).1 i := by
          funext a
          rw [hcell_eq a _ hVU]
        rw [h1]
        simpa only [toFullBlockVec, cellAverage] using
          (measurable_cellAverage_canonicalRespCoeffPlus (respGrid jStar F) hq t F p q'
            (Sum.inl i) hVmeas hVU)
      · have h1 : (fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (u a))).2 i)
            = fun a : CoeffSpace d =>
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
                (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q')).2 i := by
          funext a
          rw [hcell_eq a _ hVU]
        rw [h1]
        simpa only [toFullBlockVec, cellAverage] using
          (measurable_cellAverage_canonicalRespCoeffPlus (respGrid jStar F) hq t F p q'
            (Sum.inr i) hVmeas hVU)
    set avg : CoeffSpace d → ℕ → (Fin d → ℤ) → BlockVec d :=
      (fun a n w => if w ∈ triadicIndexBox d n
        then blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (optimizerField (respCoeffPlus F a) (u a)) - Y)
        else 0) with havg
    have havg1 : ∀ n w i, Measurable fun a : CoeffSpace d => (avg a n w).1 i := by
      intro n w i
      by_cases hw : w ∈ triadicIndexBox d n
      · have hsplit : (fun a : CoeffSpace d => (avg a n w).1 i)
            = fun a : CoeffSpace d => (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a) (u a)) - Y)).1 i := by
          funext a
          simp only [havg, if_pos hw]
        rw [hsplit]
        have hW : Measurable fun a : CoeffSpace d =>
            cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (u a)) :=
          Measurable.prod
            (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).1))
            (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).2))
        have hZ : Measurable fun a : CoeffSpace d =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffPlus F a) (u a)) - Y) :=
          (blockMatContinuousLinearMap (blockSqrt (respM0 F))).continuous.measurable.comp
            (hW.sub measurable_const)
        exact (measurable_pi_apply i).comp hZ.fst
      · have hsplit : (fun a : CoeffSpace d => (avg a n w).1 i) = fun _ => (0 : ℝ) := by
          funext a
          simp only [havg, if_neg hw]
          rfl
        rw [hsplit]
        exact measurable_const
    have havg2 : ∀ n w i, Measurable fun a : CoeffSpace d => (avg a n w).2 i := by
      intro n w i
      by_cases hw : w ∈ triadicIndexBox d n
      · have hsplit : (fun a : CoeffSpace d => (avg a n w).2 i)
            = fun a : CoeffSpace d => (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a) (u a)) - Y)).2 i := by
          funext a
          simp only [havg, if_pos hw]
        rw [hsplit]
        have hW : Measurable fun a : CoeffSpace d =>
            cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (u a)) :=
          Measurable.prod
            (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).1))
            (measurable_pi_iff.mpr (fun i => (hcoord n w hw i).2))
        have hZ : Measurable fun a : CoeffSpace d =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffPlus F a) (u a)) - Y) :=
          (blockMatContinuousLinearMap (blockSqrt (respM0 F))).continuous.measurable.comp
            (hW.sub measurable_const)
        exact (measurable_pi_apply i).comp hZ.snd
      · have hsplit : (fun a : CoeffSpace d => (avg a n w).2 i) = fun _ => (0 : ℝ) := by
          funext a
          simp only [havg, if_neg hw]
          rfl
        rw [hsplit]
        exact measurable_const
    refine Measurable.aestronglyMeasurable ?_
    have hgoal : (fun a : CoeffSpace d => besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField (respCoeffPlus F a) (u a)) - Y)) ^ 2)
        = fun a : CoeffSpace d => besovSeminorm t (avg a) ^ 2 := by
      funext a
      exact congrArg (fun x : ℝ => x ^ 2)
        (besovSeminorm_congr (fun n w hw => by simp only [havg, if_pos hw]))
    rw [hgoal]
    have hbase := measurable_besovSeminorm t havg1 havg2
    simpa only [pow_two] using! hbase.mul hbase

end

end Homogenization.HighContrast.Multiscale
