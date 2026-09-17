import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCellHalfCar
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCellTermInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsEnergyInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsDeficitInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsSubcellMeas
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsRespAvgSplit
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscNonneg

/-!
# The cell half of the cutoff-mean row with no sample-side residue

`HC3_RowsCellHalfCar` proves the cell half of the cutoff-mean row of `p.response.transfer` on the
response carriers, but carries eighteen sample-side integrability premises: the subcell responses
and response-integrand averages, the quadratic readouts of the pathwise coarse block, the three
flat averages entering the annealed Cauchy--Schwarz step, and the coordinates of the two optimizer
cell means.  All of them follow from the annealed data the row already carries — the coarse block
is integrable on every aligned cell and the terminal responses at the two scales are integrable —
together with the measurable canonical selection of the optimizer state.

This module discharges them and restates the cell half with those premises removed, and with the
subcell maximizer family constructed internally rather than supplied.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cell half of the cutoff-mean row on the carriers with no sample-side residue, minus
sign.**  Under the annealed data of the row — stationarity, the invertible grid, the coarse block
on every aligned subcell of the coarse scale, and the integrability of the two terminal responses —
the modulus of the crossed pairing of the cell part `Ncell` against `Y^-` is at most
`√(L_s^-) √(2 tau^-)`.  No sample-side integrability is assumed. -/
theorem abs_vecDot_cellPart_respYMinus_le_clean {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F)
      (respYMinus P jStar F t e)))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (Ncell : BlockVec d)
    (hNcell : Ncell = ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).1 i) ∂P),
      (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffMinus F a) (uM a) x).2 i) ∂P))) :
    |vecDot Ncell.1 (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsMinus P jStar F s t e)
        * Real.sqrt (2 * respTauMinus P jStar F s t e) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  -- the canonical subcell maximizer family
  let v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e))).toAHarmonicFunctionMeanZero.toAHarmonicFunction
  have hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (respCoeffMinus F a) (v w a) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffMinus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e))).isResponseMaximizer
  -- the subcell energies and deficits
  have hmeasEae : ∀ w ∈ triadicIndexBox d H, AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm
      H s t ht e uM hmax w hw).aestronglyMeasurable
  have hE : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))) P :=
    integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffMinus P jStar hjStar F hm H s t ht e
      uM hmax hJt hmeasEae
  have hDdef : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P :=
    integrable_subcellDeficit_respCoeffMinus P jStar hjStar F hm H s t ht hjs e uM hmax hblk hJt
      hmeasEae
  -- the two optimizer cell means
  have hNs : ∀ w ∈ triadicIndexBox d H,
      (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (v w a))).1 i) P)
        ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffMinus F a) (v w a))).2 i) P) :=
    fun w _ => integrable_cellAverage_subcellOptimizer_respCoeffMinus P jStar hjStar F hm s w
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (v w) (hv w) (hblk w)
  have hM := integrable_cellAverage_terminalOptimizer_respCoeffMinus P jStar hjStar F hm H s t ht
    e uM hmax v (fun w _ a => hv w a) hblk hDdef
  -- the subcell response-integrand averages and the subcell responses
  have hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P := by
    intro w hw
    have h1 : Integrable (fun a => -(1 / 2 : ℝ) *
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a))
      + ((∑ i : Fin d, (-(respP (respMean P jStar F t) e)) i *
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a))).2 i)
        + ∑ i : Fin d, (respqMinus P jStar F t e) i *
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a))).1 i)) P :=
      ((hE w hw).const_mul _).add
        ((integrable_finsetSum _ fun i _ => (hM.2 w hw i).const_mul _).add
          (integrable_finsetSum _ fun i _ => (hM.1 w hw i).const_mul _))
    refine h1.congr ?_
    filter_upwards with a
    rw [volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffMinus_eq P jStar hjStar F hm
      H s t ht e uM a w hw]
    simp only [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, vecDot,
      Pi.neg_apply]
  have hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P := by
    intro w hw
    refine ((hDdef w hw).add (hRint w hw)).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply]
    ring
  -- the quadratic readouts of the pathwise coarse block
  have hULLR : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      0 ≤ vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
          (respYMinus P jStar F t e).1)
        ∧ 0 ≤ vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
          (respYMinus P jStar F t e).2) :=
    fun w a => zero_le_vecDot_coarseBlockMatrix_respCoeffMinus_adaptedCellAtCenter jStar hjStar F hm s a
      (respYMinus P jStar F t e) w
  have hent : ∀ w : Fin d → ℤ, ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)) α β) P :=
    fun w => integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter hq s w F (hblk w)
  have hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
        (respYMinus P jStar F t e).1)) P :=
    fun w _ => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).upperLeft) (respYMinus P jStar F t e).1
      (fun i k => hent w (Sum.inl i) (Sum.inl k))
  have hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
        (respYMinus P jStar F t e).2)) P :=
    fun w _ => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffMinus F a)).lowerRight) (respYMinus P jStar F t e).2
      (fun i k => hent w (Sum.inr i) (Sum.inr k))
  have hcross : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
            (respYMinus P jStar F t e).1))
        * Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
            (respYMinus P jStar F t e).2))) P :=
    fun w hw => integrable_sqrt_mul_sqrt_gen (fun a => (hULLR w a).1) (fun a => (hULLR w a).2)
      (hqUL w hw) (hqLR w hw)
  have hsq : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
          + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2))) ^ 2) P :=
    fun w hw => integrable_sq_sqrt_add_sqrt_gen (fun a => (hULLR w a).1) (fun a => (hULLR w a).2)
      (hqUL w hw) (hqLR w hw)
  have hFint := integrable_avsum (P := P) (triadicIndexBox d H)
    (fun w a => (Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
              (respYMinus P jStar F t e).1))
          + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
              (respYMinus P jStar F t e).2))) ^ 2) hsq
  have hDint := integrable_avsum (P := P) (triadicIndexBox d H)
    (fun w a => 2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))))
    (fun w hw => (hDdef w hw).const_mul 2)
  have hMidint := integrable_sqrt_mul_sqrt' hFint hDint
  have hPint := integrable_avsum (P := P) (triadicIndexBox d H)
    (fun w a => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)) *
      (Real.sqrt ((Real.sqrt (vecDot (respYMinus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).upperLeft
                  (respYMinus P jStar F t e).1))
              + Real.sqrt (vecDot (respYMinus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffMinus F a)).lowerRight
                  (respYMinus P jStar F t e).2))) ^ 2)
        * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                  (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))))))
    (fun w hw => (integrable_sqrt_mul_sqrt' (hsq w hw) ((hDdef w hw).const_mul 2)).const_mul _)
  have hpair : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a)))
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (v w a)))).1
          (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1
            ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a)))
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (v w a)))).2) P := by
    intro w hw
    have h1 : Integrable (fun a => ∑ i : Fin d,
        ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (optimizerField (respCoeffMinus F a) (uM a))).1 i
          - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (optimizerField (respCoeffMinus F a) (v w a))).1 i)
          * (respYMinus P jStar F t e).2 i) P :=
      integrable_finsetSum _ fun i _ => ((hM.1 w hw i).sub ((hNs w hw).1 i)).mul_const _
    have h2 : Integrable (fun a => ∑ i : Fin d, (respYMinus P jStar F t e).1 i *
        ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (optimizerField (respCoeffMinus F a) (uM a))).2 i
          - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (optimizerField (respCoeffMinus F a) (v w a))).2 i)) P :=
      integrable_finsetSum _ fun i _ => ((hM.2 w hw i).sub ((hNs w hw).2 i)).const_mul _
    refine (h1.add h2).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply, vecDot, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  have hPint' := integrable_avsum (P := P) (triadicIndexBox d H)
    (fun w a => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)) *
      (vecDot ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a)))
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (v w a)))).1
          (respYMinus P jStar F t e).2
        + vecDot (respYMinus P jStar F t e).1
            ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (uM a)))
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffMinus F a) (v w a)))).2))
    (fun w hw => (hpair w hw).const_mul _)
  have hmeasBlk : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s) (respCoeffMinus F a)) α β) P :=
    aestronglyMeasurable_blockMatEntry_respCoeffMinus_adaptedCell P hq s F
  have hrespint : ∀ a : CoeffSpace d, IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (respCell jStar F t) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq
        t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hvf : IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
          (aHarmonicFunctionOfAEEqCoeff hae (uM a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (aHarmonicFunctionOfAEEqCoeff hae (uM a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      (aHarmonicFunctionOfAEEqCoeff hae (uM a)) hvf
  exact abs_vecDot_cellPart_respYMinus_le P hstat jStar hjStar F hm H s t ht hjs e φ hφ uM hmax
    v (fun w _ a => hv w a) hsum hblk hrespint hJint hRint hJt hJs
    (fun w _ a => (hULLR w a).1) (fun w _ a => (hULLR w a).2)
    (fun w _ i j => hent w (Sum.inl i) (Sum.inl j))
    (fun w _ i j => hent w (Sum.inr i) (Sum.inr j))
    hqUL hqLR hcross hsq hFint hDint hMidint hPint hPint' hmeasBlk
    (fun w hw i => hM.1 w hw i) (fun w hw i => hM.2 w hw i)
    (fun w hw i => (hNs w hw).1 i) (fun w hw i => (hNs w hw).2 i) Ncell hNcell

/-- **The cell half of the cutoff-mean row on the carriers with no sample-side residue, plus
sign.**  The adjoint twin of `abs_vecDot_cellPart_respYMinus_le_clean`, for the adjoint recentred
coefficient `a_+ = aᵀ + g`, the dual load `q^+`, the dual variable `Y^+` and the terminal maximizer
family `uP`. -/
theorem abs_vecDot_cellPart_respYPlus_le_clean {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef)
    (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hsum : Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F)
      (respYPlus P jStar F t e)))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (Ncell : BlockVec d)
    (hNcell : Ncell = ((fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).1 i) ∂P),
      (fun i => ∫ a, ((triadicIndexBox d H).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d H,
          (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1))
            * volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (fun x => (optimizerField (respCoeffPlus F a) (uP a) x).2 i) ∂P))) :
    |vecDot Ncell.1 (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1 Ncell.2|
      ≤ Real.sqrt (respLsPlus P jStar F s t e)
        * Real.sqrt (2 * respTauPlus P jStar F s t e) := by
  classical
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  -- the canonical subcell maximizer family
  let v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e))).toAHarmonicFunctionMeanZero.toAHarmonicFunction
  have hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (respCoeffPlus F a) (v w a) :=
    fun w a => (Classical.choice
      (nonempty_scalarCanonicalMaximizer_respCoeffPlus_adaptedCellAtCenter (respGrid jStar F) hq s w F a
        (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e))).isResponseMaximizer
  -- the subcell energies and deficits
  have hmeasEae : ∀ w ∈ triadicIndexBox d H, AEStronglyMeasurable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    fun w hw => (measurable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm
      H s t ht e uP hmax w hw).aestronglyMeasurable
  have hE : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))) P :=
    integrable_volumeAverage_energy_adaptedCellAtCenter_respCoeffPlus P jStar hjStar F hm H s t ht e
      uP hmax hJt hmeasEae
  have hDdef : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P :=
    integrable_subcellDeficit_respCoeffPlus P jStar hjStar F hm H s t ht hjs e uP hmax hblk hJt
      hmeasEae
  -- the two optimizer cell means
  have hNs : ∀ w ∈ triadicIndexBox d H,
      (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (v w a))).1 i) P)
        ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (optimizerField (respCoeffPlus F a) (v w a))).2 i) P) :=
    fun w _ => integrable_cellAverage_subcellOptimizer_respCoeffPlus P jStar hjStar F hm s w
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (v w) (hv w) (hblk w)
  have hM := integrable_cellAverage_terminalOptimizer_respCoeffPlus P jStar hjStar F hm H s t ht
    e uP hmax v (fun w _ a => hv w a) hblk hDdef
  -- the subcell response-integrand averages and the subcell responses
  have hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P := by
    intro w hw
    have h1 : Integrable (fun a => -(1 / 2 : ℝ) *
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a))
      + ((∑ i : Fin d, (-(respP (respMean P jStar F t) e)) i *
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a))).2 i)
        + ∑ i : Fin d, (respqPlus P jStar F t e) i *
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a))).1 i)) P :=
      ((hE w hw).const_mul _).add
        ((integrable_finsetSum _ fun i _ => (hM.2 w hw i).const_mul _).add
          (integrable_finsetSum _ fun i _ => (hM.1 w hw i).const_mul _))
    refine h1.congr ?_
    filter_upwards with a
    rw [volumeAverage_scalarResponseIntegrand_adaptedCellAtCenter_respCoeffPlus_eq P jStar hjStar F hm
      H s t ht e uP a w hw]
    simp only [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, vecDot,
      Pi.neg_apply]
  have hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P := by
    intro w hw
    refine ((hDdef w hw).add (hRint w hw)).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply]
    ring
  -- the quadratic readouts of the pathwise coarse block
  have hULLR : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      0 ≤ vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
          (respYPlus P jStar F t e).1)
        ∧ 0 ≤ vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
          (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
          (respYPlus P jStar F t e).2) :=
    fun w a => zero_le_vecDot_coarseBlockMatrix_respCoeffPlus_adaptedCellAtCenter jStar hjStar F hm s a
      (respYPlus P jStar F t e) w
  have hent : ∀ w : Fin d → ℤ, ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)) α β) P :=
    fun w => integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter hq s w F (hblk w)
  have hqUL : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
        (respYPlus P jStar F t e).1)) P :=
    fun w _ => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).upperLeft) (respYPlus P jStar F t e).1
      (fun i k => hent w (Sum.inl i) (Sum.inl k))
  have hqLR : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
        (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
        (respYPlus P jStar F t e).2)) P :=
    fun w _ => integrable_vecDot_matVecMul
      (fun a => (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) s w)
        (respCoeffPlus F a)).lowerRight) (respYPlus P jStar F t e).2
      (fun i k => hent w (Sum.inr i) (Sum.inr k))
  have hcross : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
            (respYPlus P jStar F t e).1))
        * Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
            (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
            (respYPlus P jStar F t e).2))) P :=
    fun w hw => integrable_sqrt_mul_sqrt_gen (fun a => (hULLR w a).1) (fun a => (hULLR w a).2)
      (hqUL w hw) (hqLR w hw)
  have hsq : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
          + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2))) ^ 2) P :=
    fun w hw => integrable_sq_sqrt_add_sqrt_gen (fun a => (hULLR w a).1) (fun a => (hULLR w a).2)
      (hqUL w hw) (hqLR w hw)
  have hFint := integrable_avsum (P := P) (triadicIndexBox d H)
    (fun w a => (Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
              (respYPlus P jStar F t e).1))
          + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
              (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
              (respYPlus P jStar F t e).2))) ^ 2) hsq
  have hDint := integrable_avsum (P := P) (triadicIndexBox d H)
    (fun w a => 2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
        - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))))
    (fun w hw => (hDdef w hw).const_mul 2)
  have hMidint := integrable_sqrt_mul_sqrt' hFint hDint
  have hPint := integrable_avsum (P := P) (triadicIndexBox d H)
    (fun w a => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)) *
      (Real.sqrt ((Real.sqrt (vecDot (respYPlus P jStar F t e).1 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).upperLeft
                  (respYPlus P jStar F t e).1))
              + Real.sqrt (vecDot (respYPlus P jStar F t e).2 (matVecMul (coarseBlockMatrix
                  (adaptedCellAtCenter (respGrid jStar F) s w) (respCoeffPlus F a)).lowerRight
                  (respYPlus P jStar F t e).2))) ^ 2)
        * Real.sqrt (2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w)
              (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)
            - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
                (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                  (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))))))
    (fun w hw => (integrable_sqrt_mul_sqrt' (hsq w hw) ((hDdef w hw).const_mul 2)).const_mul _)
  have hpair : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      vecDot ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a)))
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (v w a)))).1
          (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1
            ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a)))
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (v w a)))).2) P := by
    intro w hw
    have h1 : Integrable (fun a => ∑ i : Fin d,
        ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (optimizerField (respCoeffPlus F a) (uP a))).1 i
          - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (optimizerField (respCoeffPlus F a) (v w a))).1 i)
          * (respYPlus P jStar F t e).2 i) P :=
      integrable_finsetSum _ fun i _ => ((hM.1 w hw i).sub ((hNs w hw).1 i)).mul_const _
    have h2 : Integrable (fun a => ∑ i : Fin d, (respYPlus P jStar F t e).1 i *
        ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (optimizerField (respCoeffPlus F a) (uP a))).2 i
          - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
            (optimizerField (respCoeffPlus F a) (v w a))).2 i)) P :=
      integrable_finsetSum _ fun i _ => ((hM.2 w hw i).sub ((hNs w hw).2 i)).const_mul _
    refine (h1.add h2).congr ?_
    filter_upwards with a
    simp only [Pi.add_apply, vecDot, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  have hPint' := integrable_avsum (P := P) (triadicIndexBox d H)
    (fun w a => (volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w) (fun x => φ x - 1)) *
      (vecDot ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a)))
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (v w a)))).1
          (respYPlus P jStar F t e).2
        + vecDot (respYPlus P jStar F t e).1
            ((cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (uP a)))
            - (cellAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (optimizerField (respCoeffPlus F a) (v w a)))).2))
    (fun w hw => (hpair w hw).const_mul _)
  have hmeasBlk : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => blockMatEntry
      (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) s) (respCoeffPlus F a)) α β) P :=
    aestronglyMeasurable_blockMatEntry_respCoeffPlus_adaptedCell P hq s F
  have hrespint : ∀ a : CoeffSpace d, IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (respCell jStar F t) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
    have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
      (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq
        t).isFiniteMeasure_restrict_volume
    have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    have hvf : IntegrableOn
        (scalarResponseIntegrand (respCell jStar F t) f
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
          (aHarmonicFunctionOfAEEqCoeff hae (uP a))) (respCell jStar F t) :=
      hdata.response (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (aHarmonicFunctionOfAEEqCoeff hae (uP a))
    exact integrableOn_scalarResponseIntegrand_aHarmonicFunctionOfAEEqCoeff (subset_refl _)
      hae.symm (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
      (aHarmonicFunctionOfAEEqCoeff hae (uP a)) hvf
  exact abs_vecDot_cellPart_respYPlus_le P hstat jStar hjStar F hm H s t ht hjs e φ hφ uP hmax
    v (fun w _ a => hv w a) hsum hblk hrespint hJint hRint hJt hJs
    (fun w _ a => (hULLR w a).1) (fun w _ a => (hULLR w a).2)
    (fun w _ i j => hent w (Sum.inl i) (Sum.inl j))
    (fun w _ i j => hent w (Sum.inr i) (Sum.inr j))
    hqUL hqLR hcross hsq hFint hDint hMidint hPint hPint' hmeasBlk
    (fun w hw i => hM.1 w hw i) (fun w hw i => hM.2 w hw i)
    (fun w hw i => (hNs w hw).1 i) (fun w hw i => (hNs w hw).2 i) Ncell hNcell

end

end Homogenization.HighContrast.Multiscale
