import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCrossMeas
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsOscCellEnergy
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsHeadMeas
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEntBridge
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffPartitionAverage
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscHbdCar
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscEnergyCar
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscNonneg
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscPathCar
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCarrierInputs

/-!
# The cell average of the crossed pairing is integrable in the sample

The descendant sum of the oscillation half of `p.response.transfer` reads the cell average of the
crossed pairing `⟨Y₂, ∇u⟩ + ⟨Y₁, a ∇u⟩` of the terminal optimizer on every aligned cell of every
generation below the terminal one.  That readout is measurable in the sample by
`HC3_RowsCrossMeas`, and the Fenchel probe of `HC3_DirectOscHbdCar` dominates its modulus by the
two-term head of the cell times the square root of twice the doubled cell energy.  Young's
inequality turns that product into the sum of the squared head and the cell energy, both of which
are `P`-integrable — the first from the entrywise integrability of the pathwise coarse block on
that cell, the second from the integrability of the terminal response.  So the readout is
`P`-integrable on every cell of every generation.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Young's inequality in the shape the Fenchel probe leaves behind: a nonnegative head times the
square root of twice a doubled nonnegative energy is at most the squared head plus the energy. -/
private theorem mul_sqrt_two_mul_two_mul_le {G D : ℝ} (hD : 0 ≤ D) :
    G * Real.sqrt (2 * (2 * D)) ≤ G ^ 2 + D := by
  have h4 : (2 : ℝ) * (2 * D) = 2 ^ 2 * D := by ring
  have hsqrt : Real.sqrt (2 * (2 * D)) = 2 * Real.sqrt D := by
    rw [h4, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2) D,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  have hsq : 0 ≤ (G - Real.sqrt D) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt hD] at hsq
  rw [hsqrt]
  nlinarith [hsq]

/-- **The annealed cell energy of the terminal optimizer on an aligned cell of any generation,
minus sign.**  `HC3_RowsEnergyInt` makes the readout `P`-integrable on the cells of one fixed
generation aligned with a scale `s` under `t = s + H`; every generation `t - m` is that statement
at `s := t - m` and `H := m`. -/
theorem integrable_volumeAverage_energy_depth_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (m : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d m) :
    Integrable (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P := by
  have ht' : t = (t - (m : ℤ)) + (m : ℤ) := by ring
  exact integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm
    m (t - (m : ℤ)) t ht' e uM hmax hJt
    (fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F
      hm m (t - (m : ℤ)) t ht' e uM hmax w hw).aestronglyMeasurable) W hW

/-- **The annealed cell energy of the terminal optimizer on an aligned cell of any generation,
plus sign.**  The adjoint twin of `integrable_volumeAverage_energy_depth_respCoeffMinus`. -/
theorem integrable_volumeAverage_energy_depth_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (m : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d m) :
    Integrable (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P := by
  have ht' : t = (t - (m : ℤ)) + (m : ℤ) := by ring
  exact integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm
    m (t - (m : ℤ)) t ht' e uP hmax hJt
    (fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F
      hm m (t - (m : ℤ)) t ht' e uP hmax w hw).aestronglyMeasurable) W hW

/-- **The cell average of the crossed pairing is `P`-integrable, minus sign.**  On every aligned
cell of every generation below the terminal one, the cell average of the scalar crossed pairing of
the deterministic dual variable with the terminal optimizer state is `P`-integrable. -/
theorem integrable_volumeAverage_cross_optimizerField_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hblk : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w))
    (Y : BlockVec d) (m : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d m) :
    Integrable (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (fun x => vecDot Y.2 (optimizerField (respCoeffMinus F a) (uM a) x).1
        + vecDot Y.1 (optimizerField (respCoeffMinus F a) (uM a) x).2)) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq _ W).measurableSet
  have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W ⊆ respCell jStar F t :=
    adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hmeas := measurable_volumeAverage_cross_optimizerField_respCoeffMinus P jStar hjStar F hm
    t e uM hmax hV hVU Y
  -- the squared two-term head of the cell
  have hUL0 : ∀ a : CoeffSpace d, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1) := fun a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm
      (t - (m : ℤ)) a Y W).1
  have hLR0 : ∀ a : CoeffSpace d, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffMinus F a)).lowerRight Y.2) := fun a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm
      (t - (m : ℤ)) a Y W).2
  have hheadsq : Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) (respCoeffMinus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffMinus F a)).lowerRight Y.2))) ^ 2) P :=
    integrable_sq_sqrt_add_sqrt_coarseBlockMatrix Y
      (integrable_vecDot_coarseBlockMatrix_upperLeft Y
        (integrable_coarseBlockMatrix_upperLeft_respCoeffMinus P jStar hjStar F hm
          (t - (m : ℤ)) W (hblk (t - (m : ℤ)) W)))
      (integrable_vecDot_coarseBlockMatrix_lowerRight Y
        (integrable_coarseBlockMatrix_lowerRight_respCoeffMinus P jStar hjStar F hm
          (t - (m : ℤ)) W (hblk (t - (m : ℤ)) W)))
      hUL0 hLR0
  have hE := integrable_volumeAverage_energy_depth_respCoeffMinus P jStar hjStar F hm t e uM
    hmax hJt m W hW
  refine Integrable.mono' (hheadsq.add hE) hmeas.aestronglyMeasurable ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  have hbd := abs_volumeAverage_cross_optimizerField_respCoeffMinus_adaptedCellAtCenter_le jStar hjStar
    F hm t m a (uM a) Y hW
    (fun i => (h6a_integrableOn_optimizerField_respCoeffMinus_box (respGrid jStar F) hq t F a
      (uM a) m W hW i).1)
    (fun i => (h6a_integrableOn_optimizerField_respCoeffMinus_box (respGrid jStar F) hq t F a
      (uM a) m W hW i).2)
    ((integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uM a) hW).1 Y.2)
    ((integrableOn_vecDot_optimizerField_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uM a) hW).2 Y.1)
  have hDnn := zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffMinus_adaptedCellAtCenter
    jStar hjStar F hm t m a (uM a) hW
  have hyoung := mul_sqrt_two_mul_two_mul_le (G := Real.sqrt (vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffMinus F a)).upperLeft Y.1))
    + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (respCoeffMinus F a)).lowerRight Y.2))) hDnn
  simp only [Pi.add_apply]
  linarith only [hbd, hyoung]

/-- **The cell average of the crossed pairing is `P`-integrable, plus sign.**  The adjoint twin of
`integrable_volumeAverage_cross_optimizerField_respCoeffMinus`. -/
theorem integrable_volumeAverage_cross_optimizerField_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef)
    (t : ℤ) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hblk : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w))
    (Y : BlockVec d) (m : ℕ) (W : Fin d → ℤ) (hW : W ∈ triadicIndexBox d m) :
    Integrable (fun a => volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
      (fun x => vecDot Y.2 (optimizerField (respCoeffPlus F a) (uP a) x).1
        + vecDot Y.1 (optimizerField (respCoeffPlus F a) (uP a) x).2)) P := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hV : MeasurableSet (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq _ W).measurableSet
  have hVU : adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W ⊆ respCell jStar F t :=
    adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t m hW
  have hmeas := measurable_volumeAverage_cross_optimizerField_respCoeffPlus P jStar hjStar F hm
    t e uP hmax hV hVU Y
  have hUL0 : ∀ a : CoeffSpace d, 0 ≤ vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1) := fun a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm
      (t - (m : ℤ)) a Y W).1
  have hLR0 : ∀ a : CoeffSpace d, 0 ≤ vecDot Y.2 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffPlus F a)).lowerRight Y.2) := fun a =>
    (zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm
      (t - (m : ℤ)) a Y W).2
  have hheadsq : Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W) (respCoeffPlus F a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
              (respCoeffPlus F a)).lowerRight Y.2))) ^ 2) P :=
    integrable_sq_sqrt_add_sqrt_coarseBlockMatrix Y
      (integrable_vecDot_coarseBlockMatrix_upperLeft Y
        (integrable_coarseBlockMatrix_upperLeft_respCoeffPlus P jStar hjStar F hm
          (t - (m : ℤ)) W (hblk (t - (m : ℤ)) W)))
      (integrable_vecDot_coarseBlockMatrix_lowerRight Y
        (integrable_coarseBlockMatrix_lowerRight_respCoeffPlus P jStar hjStar F hm
          (t - (m : ℤ)) W (hblk (t - (m : ℤ)) W)))
      hUL0 hLR0
  have hE := integrable_volumeAverage_energy_depth_respCoeffPlus P jStar hjStar F hm t e uP
    hmax hJt m W hW
  refine Integrable.mono' (hheadsq.add hE) hmeas.aestronglyMeasurable ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  have hbd := abs_volumeAverage_cross_optimizerField_respCoeffPlus_adaptedCellAtCenter_le jStar hjStar
    F hm t m a (uP a) Y hW
    (fun i => (h6a_integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hq t F a
      (uP a) m W hW i).1)
    (fun i => (h6a_integrableOn_optimizerField_respCoeffPlus_box (respGrid jStar F) hq t F a
      (uP a) m W hW i).2)
    ((integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uP a) hW).1 Y.2)
    ((integrableOn_vecDot_optimizerField_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm t m a
      (uP a) hW).2 Y.1)
  have hDnn := zero_le_volumeAverage_scalarVariationEnergyIntegrand_respCoeffPlus_adaptedCellAtCenter
    jStar hjStar F hm t m a (uP a) hW
  have hyoung := mul_sqrt_two_mul_two_mul_le (G := Real.sqrt (vecDot Y.1 (matVecMul
      (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
        (respCoeffPlus F a)).upperLeft Y.1))
    + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) W)
          (respCoeffPlus F a)).lowerRight Y.2))) hDnn
  simp only [Pi.add_apply]
  linarith only [hbd, hyoung]

end

end Homogenization.HighContrast.Multiscale
