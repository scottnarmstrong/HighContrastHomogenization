import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscRem
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscPathCar
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsOscLimDom
import HCPoly.Entry.Multiscale.ResponseInputs.HC2a_ReferenceCubePullback
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65a

/-!
# The descendant remainder of the cutoff-mean row vanishes along every sample

The passage to the limit in the oscillation half of the cutoff-mean row of `p.response.transfer`
needs only that the depth-`(H+N)` remainder tends to zero along every sample.  It does: the
remainder is at most `(32 d² Θ 3^{-H}) 3^{-N}` times the terminal-cell average of the modulus of
the crossed pairing, and that average is a finite constant of the sample — finite by the pathwise
ellipticity of the coefficient, with no bound uniform in the sample and no integrability in the
law.  This module records the resulting vanishing for both signs, which is the `hrem0` hypothesis
of the dominated descendant limit.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Filter

open scoped Topology

noncomputable section

/-- **The descendant remainder vanishes along every sample, minus sign.**  For the terminal
optimizer family of the recentred coefficient `a_- = a - g` and a deterministic dual variable `Y`,
the difference between the `(φ-1)`-weighted terminal cell average of the crossed pairing and its
depth-`(H+N)` cell part tends to zero as `N → ∞`, for every sample. -/
theorem tendsto_zero_descendantRemainder_respCoeffMinus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (H : ℕ) {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (Y : BlockVec d) (a : CoeffSpace d) :
    Tendsto (fun N : ℕ =>
        volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            (vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
              + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
          - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                  (fun x => φ x - 1)) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                  (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
                    + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2))
      atTop (𝓝 0) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hzero : (0 : Fin d → ℤ) ∈ triadicIndexBox d 0 := by
    rw [mem_triadicIndexBox_iff]
    intro i
    simp
  have hcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0 = respCell jStar F t := by
    rw [respCell]
    simpa using b130_adaptedCellAtCenter_zero (respGrid jStar F) t
  refine tendsto_zero_of_abs_le_geometric
    (fun N a' =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          (vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2))
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
                  + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2))
    (fun a' => (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
      * volumeAverage (respCell jStar F t)
          (fun x => |vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2|)) ?_ a
  intro N a'
  obtain ⟨hfU, habsU⟩ := integrableOn_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar
    hjStar F hm t 0 a' (uM a') Y hzero
  rw [hcell] at hfU habsU
  have hat := fun w (hw : w ∈ triadicIndexBox d (H + N)) =>
    integrableOn_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t (H + N)
      a' (uM a') Y hw
  have hmain := abs_volumeAverage_sub_one_mul_sub_avsum_shift_le (qq := respGrid jStar F) hq t H N
    hφ (f := fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
      + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2)
    habsU hfU (fun w hw => (hat w hw).1) (fun w hw => (hat w hw).2)
  calc |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          (vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2))
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
                  + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2)|
      ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(N : ℝ))
          * volumeAverage (respCell jStar F t)
              (fun x => |vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
                + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2|) := hmain
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * volumeAverage (respCell jStar F t)
              (fun x => |vecDot Y.2 (optimizerField (respCoeffMinus F a') (uM a') x).1
                + vecDot Y.1 (optimizerField (respCoeffMinus F a') (uM a') x).2|)
        * (3 : ℝ) ^ (-(N : ℝ)) := by ring

/-- **The descendant remainder vanishes along every sample, plus sign.**  For the terminal
optimizer family of the recentred coefficient `a_- = a - g` and a deterministic dual variable `Y`,
the difference between the `(φ-1)`-weighted terminal cell average of the crossed pairing and its
depth-`(H+N)` cell part tends to zero as `N → ∞`, for every sample. -/
theorem tendsto_zero_descendantRemainder_respCoeffPlus {d : ℕ} [NeZero d]
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (H : ℕ) {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (Y : BlockVec d) (a : CoeffSpace d) :
    Tendsto (fun N : ℕ =>
        volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
            (vecDot Y.2 (optimizerField (respCoeffPlus F a) (uM a) x).1
              + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uM a) x).2))
          - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
              (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                  (fun x => φ x - 1)) *
                volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                  (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uM a) x).1
                    + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uM a) x).2))
      atTop (𝓝 0) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hzero : (0 : Fin d → ℤ) ∈ triadicIndexBox d 0 := by
    rw [mem_triadicIndexBox_iff]
    intro i
    simp
  have hcell : adaptedCellAtCenter (respGrid jStar F) (t - ((0 : ℕ) : ℤ)) 0 = respCell jStar F t := by
    rw [respCell]
    simpa using b130_adaptedCellAtCenter_zero (respGrid jStar F) t
  refine tendsto_zero_of_abs_le_geometric
    (fun N a' =>
      volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          (vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2))
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
                  + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2))
    (fun a' => (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
      * volumeAverage (respCell jStar F t)
          (fun x => |vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2|)) ?_ a
  intro N a'
  obtain ⟨hfU, habsU⟩ := integrableOn_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar
    hjStar F hm t 0 a' (uM a') Y hzero
  rw [hcell] at hfU habsU
  have hat := fun w (hw : w ∈ triadicIndexBox d (H + N)) =>
    integrableOn_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t (H + N)
      a' (uM a') Y hw
  have hmain := abs_volumeAverage_sub_one_mul_sub_avsum_shift_le (qq := respGrid jStar F) hq t H N
    hφ (f := fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
      + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2)
    habsU hfU (fun w hw => (hat w hw).1) (fun w hw => (hat w hw).2)
  calc |volumeAverage (respCell jStar F t) (fun x => (φ x - 1) *
          (vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
            + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2))
        - ((triadicIndexBox d (H + N)).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d (H + N),
            (volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - ((H + N : ℕ) : ℤ)) w)
                (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
                  + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2)|
      ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(N : ℝ))
          * volumeAverage (respCell jStar F t)
              (fun x => |vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
                + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2|) := hmain
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * volumeAverage (respCell jStar F t)
              (fun x => |vecDot Y.2 (optimizerField (respCoeffPlus F a') (uM a') x).1
                + vecDot Y.1 (optimizerField (respCoeffPlus F a') (uM a') x).2|)
        * (3 : ℝ) ^ (-(N : ℝ)) := by ring

end

end Homogenization.HighContrast.Multiscale
