import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsThreeClean
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsShape

/-!
# The two analytic rows behind the cutoff estimate

The cutoff estimate of `e.response.cutoff.estimate` bounds the centred response `Jtilde^±(e)` by
the sum of its three error rows and the expected absolute cutoff pairing.  The integrated cutoff
decomposition already exhibits those three rows; what the printed proof still supplies are the two
bounds on the energy defect and on the centred cutoff mean.  This module names them as the
predicates `CutoffEnergyDefectRowMinus` and `CutoffMeanRowMinus` (and their `Plus` twins) and shows
that the printed right-hand side of the estimate follows from them together with the decomposition,
by linear arithmetic on the half-weighted pairing row.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The first error row of the estimate, as a named obligation. -/
def CutoffEnergyDefectRowMinus (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) :
    Prop :=
  |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
      - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
    ≤ C * (respTauMinus P jStar F s t e
        + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
        + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e)

/-- The second and third error rows of the estimate, as a named obligation. -/
def CutoffMeanRowMinus (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t)) :
    Prop :=
  (1 / 2 : ℝ) * |vecDot
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
        (respYMinus P jStar F t e).2
      + vecDot (respYMinus P jStar F t e).1
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)|
    ≤ C * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
      + C * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))

/-- The three-row decomposition of `e.response.cutoff.estimate` and the two bounds on its error
rows assemble into the printed right-hand side: if the cutoff energy defect obeys its bound and the
centred cutoff mean obeys its two-row bound, then `|Jtilde^-(e)|` is bounded by the two rows, the
half-weighted cutoff pairing, and the expected absolute cutoff pairing carried at coefficient one. -/
theorem abs_respCenteredJMinus_le_cutoffRows_of_obligations {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (φ : Vec d → ℝ)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hq : IsUnit (respGrid jStar F))
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hA : Integrable (fun a => (1 / 2 : ℝ) *
      hc3CutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
        (respCoeffMinus F a) (uM a)) P)
    (hW : Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hM1 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1 i) P)
    (hM2 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2 i) P)
    (hcut : IsResponseCutoff (respGrid jStar F) t φ)
    (hφint : IntegrableOn φ (respCell jStar F t))
    (hEcell : ∀ a, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
        (optimizerField (respCoeffMinus F a) (uM a) x).2) (respCell jStar F t))
    (h1cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).1 i) (respCell jStar F t))
    (h2cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i) (respCell jStar F t))
    (C : ℝ) (H : ℕ) (s : ℤ)
    (hrow1 : CutoffEnergyDefectRowMinus C P jStar F H s t e φ uM)
    (hrow2 : CutoffMeanRowMinus C P jStar F H s t e φ uM) :
    |respCenteredJMinus P jStar F t e|
      ≤ C * (respTauMinus P jStar F s t e
            + Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e)
        + C * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
        + C * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))
        + (∫ a, |hc3CutoffPairingOnCellAux (respCell jStar F t) φ
            (respYMinus P jStar F t e) (respCoeffMinus F a) (uM a)| ∂P) := by
  have hthree := abs_respCenteredJMinus_le_three_rows_of_cutoff P jStar F t e φ uM
    hq hblk hJ hA hW hM1 hM2 hcut hφint hEcell h1cell h2cell
  unfold CutoffEnergyDefectRowMinus at hrow1
  unfold CutoffMeanRowMinus at hrow2
  exact le_cutoffRows_of_two_rows hthree
    (integral_nonneg (fun a => abs_nonneg _)) hrow1 hrow2

/-- The first error row of the adjoint estimate, as a named obligation. -/
def CutoffEnergyDefectRowPlus (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) :
    Prop :=
  |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
      - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
    ≤ C * (respTauPlus P jStar F s t e
        + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
        + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e)

/-- The second and third error rows of the adjoint estimate, as a named obligation. -/
def CutoffMeanRowPlus (C : ℝ) (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t)) :
    Prop :=
  (1 / 2 : ℝ) * |vecDot
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
        (respYPlus P jStar F t e).2
      + vecDot (respYPlus P jStar F t e).1
        ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
          (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)|
    ≤ C * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
      + C * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))

/-- The three-row decomposition of `e.response.cutoff.estimate` and the two bounds on its adjoint
error rows assemble into the printed right-hand side: if the adjoint cutoff energy defect obeys its
bound and the adjoint centred cutoff mean obeys its two-row bound, then `|Jtilde^+(e)|` is bounded
by the two rows, the half-weighted cutoff pairing, and the expected absolute cutoff pairing carried
at coefficient one. -/
theorem abs_respCenteredJPlus_le_cutoffRows_of_obligations {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (φ : Vec d → ℝ)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hq : IsUnit (respGrid jStar F))
    (hblk : HasIntegrableCoarseBlock P (respCell jStar F t))
    (hJ : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hA : Integrable (fun a => (1 / 2 : ℝ) *
      hc3CutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
        (respCoeffPlus F a) (uP a)) P)
    (hW : Integrable (fun a =>
      cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hM1 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1 i) P)
    (hM2 : ∀ i, Integrable (fun a =>
      (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2 i) P)
    (hcut : IsResponseCutoff (respGrid jStar F) t φ)
    (hφint : IntegrableOn φ (respCell jStar F t))
    (hEcell : ∀ a, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
        (optimizerField (respCoeffPlus F a) (uP a) x).2) (respCell jStar F t))
    (h1cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).1 i) (respCell jStar F t))
    (h2cell : ∀ (a : CoeffSpace d) (i : Fin d), IntegrableOn
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i) (respCell jStar F t))
    (C : ℝ) (H : ℕ) (s : ℤ)
    (hrow1 : CutoffEnergyDefectRowPlus C P jStar F H s t e φ uP)
    (hrow2 : CutoffMeanRowPlus C P jStar F H s t e φ uP) :
    |respCenteredJPlus P jStar F t e|
      ≤ C * (respTauPlus P jStar F s t e
            + Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e)
        + C * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
        + C * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))
        + (∫ a, |hc3CutoffPairingOnCellAux (respCell jStar F t) φ
            (respYPlus P jStar F t e) (respCoeffPlus F a) (uP a)| ∂P) := by
  have hthree := abs_respCenteredJPlus_le_three_rows_of_cutoff P jStar F t e φ uP
    hq hblk hJ hA hW hM1 hM2 hcut hφint hEcell h1cell h2cell
  unfold CutoffEnergyDefectRowPlus at hrow1
  unfold CutoffMeanRowPlus at hrow2
  exact le_cutoffRows_of_two_rows hthree
    (integral_nonneg (fun a => abs_nonneg _)) hrow1 hrow2

end

end Homogenization.HighContrast.Multiscale
