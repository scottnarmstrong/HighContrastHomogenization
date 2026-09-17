import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCellMeanInt
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# Sample integrability of the terminal optimizer cell mean on an aligned subcell

The doubled optimizer cell mean of the TERMINAL maximizer, read on an aligned subcell of the
terminal cell, is not a functional of the pathwise coarse block, so its `P`-integrability cannot be
read off `HasIntegrableCoarseBlock`.  It follows instead from the Fenchel probe of AK Lemma A.1,
read at a single basis direction: the probe `Y = (0, δ_i)` bounds the `i`-th gradient coordinate of
the difference between the terminal mean and the subcell maximizer mean by
`√(σ_{*,V}^{-1})_{ii} √(2 D_V)`, and the probe `Y = (δ_i, 0)` bounds the `i`-th flux coordinate by
`√(𝐛_{V,ii}) √(2 D_V)`.  Both envelopes are integrable — the first factor by the entrywise
integrability of the block, the second by the integrability of the subcell deficit — and the
terminal mean is measurable in the sample through the canonical selection, so the difference, and
with the subcell mean also the terminal mean, is integrable.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The terminal optimizer cell mean is integrable on every aligned subcell, minus sign.**  With
the subcell maximizer family `v` and the integrability of the subcell deficits, every coordinate of
the cell mean of the doubled optimizer field of the terminal maximizer family `uM` for
`a_- = a - g` is `P`-integrable on every depth-`H` aligned subcell of the terminal cell. -/
theorem integrable_cellAverage_terminalOptimizer_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hmaxV : ∀ w ∈ triadicIndexBox d H, ∀ a,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) (v w a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hD : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P) :
    (∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (uM a))).1 i) P)
      ∧ (∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (uM a))).2 i) P) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hs : s = t - (H : ℤ) := by rw [ht]; ring
  subst hs
  set p : Vec d := respP (respMean P jStar F t) e with hp
  set r : Vec d := respqMinus P jStar F t e with hr
  have hkey : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (uM a))).1 i) P
        ∧ Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (uM a))).2 i) P := by
    intro w hw i
    have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) :=
      (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (H : ℤ)) w).measurableSet
    have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    have hNs := integrable_cellAverage_subcellOptimizer_respCoeffMinus P jStar hjStar F hm
      (t - (H : ℤ)) w p r (v w) (hmaxV w hw) (hblk w)
    have hent := integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter hq (t - (H : ℤ)) w F
      (hblk w)
    have hDw := (hD w hw).const_mul (2 : ℝ)
    have hmeasM1 : AEStronglyMeasurable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (uM a))).1 i) P :=
      (measurable_cellAverage_optimizerField_respCoeffMinus P jStar hjStar F hm t e
        (Sum.inl i) uM hmax hVmeas hVU).aestronglyMeasurable
    have hmeasM2 : AEStronglyMeasurable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffMinus F a) (uM a))).2 i) P :=
      (measurable_cellAverage_optimizerField_respCoeffMinus P jStar hjStar F hm t e
        (Sum.inr i) uM hmax hVmeas hVU).aestronglyMeasurable
    constructor
    · have hbd : ∀ a : CoeffSpace d,
          |(cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (uM a))).1 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (v w a))).1 i|
          ≤ Real.sqrt ((coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (respCoeffMinus F a)).lowerRight i i)
            * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) p r
                (respCoeffMinus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r
                    (uM a)))) := by
        intro a
        obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
          exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
        have h := abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
          hq t H hEll hae p r (uM a) hw (v w a) (hmaxV w hw a)
          (((0 : Vec d), Pi.single i (1 : ℝ)) : BlockVec d)
        simpa only [vecDot_single_left, vecDot_zero_left, matVecMul_zero, matVecMul_single,
          Real.sqrt_zero, zero_add, add_zero, Pi.sub_apply] using! h
      have hdiff : Integrable (fun a =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (uM a))).1 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (v w a))).1 i) P :=
        integrable_of_abs_le (hmeasM1.sub (hNs.1 i).1)
          (integrable_sqrt_mul_sqrt' (hent (Sum.inr i) (Sum.inr i)) hDw) hbd
      refine (hdiff.add (hNs.1 i)).congr ?_
      filter_upwards with a
      simp only [Pi.add_apply]
      ring
    · have hbd : ∀ a : CoeffSpace d,
          |(cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (uM a))).2 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (v w a))).2 i|
          ≤ Real.sqrt ((coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (respCoeffMinus F a)).upperLeft i i)
            * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) p r
                (respCoeffMinus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a) p r
                    (uM a)))) := by
        intro a
        obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
          exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
        have h := abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
          hq t H hEll hae p r (uM a) hw (v w a) (hmaxV w hw a)
          ((Pi.single i (1 : ℝ), (0 : Vec d)) : BlockVec d)
        simpa only [vecDot_single_left, vecDot_zero_left, matVecMul_zero, matVecMul_single,
          Real.sqrt_zero, zero_add, add_zero, Pi.sub_apply] using! h
      have hdiff : Integrable (fun a =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (uM a))).2 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffMinus F a) (v w a))).2 i) P :=
        integrable_of_abs_le (hmeasM2.sub (hNs.2 i).1)
          (integrable_sqrt_mul_sqrt' (hent (Sum.inl i) (Sum.inl i)) hDw) hbd
      refine (hdiff.add (hNs.2 i)).congr ?_
      filter_upwards with a
      simp only [Pi.add_apply]
      ring
  exact ⟨fun w hw i => (hkey w hw i).1, fun w hw i => (hkey w hw i).2⟩

/-- **The terminal optimizer cell mean is integrable on every aligned subcell, plus sign.**  The
adjoint twin of `integrable_cellAverage_terminalOptimizer_respCoeffMinus`, for the adjoint
recentred coefficient `a_+ = aᵀ + g`, the dual load `q^+` and the terminal maximizer family
`uP`. -/
theorem integrable_cellAverage_terminalOptimizer_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hmaxV : ∀ w ∈ triadicIndexBox d H, ∀ a,
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) (v w a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hD : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P) :
    (∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (uP a))).1 i) P)
      ∧ (∀ w ∈ triadicIndexBox d H, ∀ i : Fin d, Integrable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (uP a))).2 i) P) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hs : s = t - (H : ℤ) := by rw [ht]; ring
  subst hs
  set p : Vec d := respP (respMean P jStar F t) e with hp
  set r : Vec d := respqPlus P jStar F t e with hr
  have hkey : ∀ w ∈ triadicIndexBox d H, ∀ i : Fin d,
      Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (uP a))).1 i) P
        ∧ Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (uP a))).2 i) P := by
    intro w hw i
    have hVmeas : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) :=
      (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (H : ℤ)) w).measurableSet
    have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t H hw
    have hNs := integrable_cellAverage_subcellOptimizer_respCoeffPlus P jStar hjStar F hm
      (t - (H : ℤ)) w p r (v w) (hmaxV w hw) (hblk w)
    have hent := integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter hq (t - (H : ℤ)) w F
      (hblk w)
    have hDw := (hD w hw).const_mul (2 : ℝ)
    have hmeasM1 : AEStronglyMeasurable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (uP a))).1 i) P :=
      (measurable_cellAverage_optimizerField_respCoeffPlus P jStar hjStar F hm t e
        (Sum.inl i) uP hmax hVmeas hVU).aestronglyMeasurable
    have hmeasM2 : AEStronglyMeasurable (fun a =>
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
          (optimizerField (respCoeffPlus F a) (uP a))).2 i) P :=
      (measurable_cellAverage_optimizerField_respCoeffPlus P jStar hjStar F hm t e
        (Sum.inr i) uP hmax hVmeas hVU).aestronglyMeasurable
    constructor
    · have hbd : ∀ a : CoeffSpace d,
          |(cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (uP a))).1 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (v w a))).1 i|
          ≤ Real.sqrt ((coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (respCoeffPlus F a)).lowerRight i i)
            * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) p r
                (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r
                    (uP a)))) := by
        intro a
        obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
          exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
        have h := abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
          hq t H hEll hae p r (uP a) hw (v w a) (hmaxV w hw a)
          (((0 : Vec d), Pi.single i (1 : ℝ)) : BlockVec d)
        simpa only [vecDot_single_left, vecDot_zero_left, matVecMul_zero, matVecMul_single,
          Real.sqrt_zero, zero_add, add_zero, Pi.sub_apply] using! h
      have hdiff : Integrable (fun a =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (uP a))).1 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (v w a))).1 i) P :=
        integrable_of_abs_le (hmeasM1.sub (hNs.1 i).1)
          (integrable_sqrt_mul_sqrt' (hent (Sum.inr i) (Sum.inr i)) hDw) hbd
      refine (hdiff.add (hNs.1 i)).congr ?_
      filter_upwards with a
      simp only [Pi.add_apply]
      ring
    · have hbd : ∀ a : CoeffSpace d,
          |(cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (uP a))).2 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (v w a))).2 i|
          ≤ Real.sqrt ((coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (respCoeffPlus F a)).upperLeft i i)
            * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w) p r
                (respCoeffPlus F a)
              - volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
                  (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a) p r
                    (uP a)))) := by
        intro a
        obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
          exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
        have h := abs_dualPairing_diff_cellAverage_adaptedCellAtCenter_le (q := respGrid jStar F)
          hq t H hEll hae p r (uP a) hw (v w a) (hmaxV w hw a)
          ((Pi.single i (1 : ℝ), (0 : Vec d)) : BlockVec d)
        simpa only [vecDot_single_left, vecDot_zero_left, matVecMul_zero, matVecMul_single,
          Real.sqrt_zero, zero_add, add_zero, Pi.sub_apply] using! h
      have hdiff : Integrable (fun a =>
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (uP a))).2 i
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (H : ℤ)) w)
              (optimizerField (respCoeffPlus F a) (v w a))).2 i) P :=
        integrable_of_abs_le (hmeasM2.sub (hNs.2 i).1)
          (integrable_sqrt_mul_sqrt' (hent (Sum.inl i) (Sum.inl i)) hDw) hbd
      refine (hdiff.add (hNs.2 i)).congr ?_
      filter_upwards with a
      simp only [Pi.add_apply]
      ring
  exact ⟨fun w hw i => (hkey w hw i).1, fun w hw i => (hkey w hw i).2⟩

end

end Homogenization.HighContrast.Multiscale
