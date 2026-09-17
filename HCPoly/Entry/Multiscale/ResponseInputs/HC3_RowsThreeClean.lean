import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsThree
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsPathwiseId

/-!
# The centred response against its three cutoff rows, with the pathwise identity discharged

The centred responses `Jtilde^±(e)` of `e.response.cutoff.estimate` are bounded by the three cutoff
rows of the printed variational calculation once the cutoff pairing is decomposed pathwise into the
cutoff half-energy, the two cutoff-mean pairings and half the self-pairing of the annealed mean.
For a cutoff of the response class — in particular one of cell average one — that decomposition is
not an extra assumption: it follows from the integrability of the cutoff-weighted optimizer state
against the cell.  These two statements therefore replace the pathwise identity of
`HC3_RowsThree` by the membership of the cutoff and the indicated cell integrabilities.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The centred response against its three cutoff rows** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)), minus carriers, with the pathwise identity discharged from cutoff
membership.  The cutoff `φ` is a response cutoff on the cell `U_t` — so in particular it has cell
average one — and the cutoff-weighted optimizer state is integrable against that cell.  Under these
hypotheses the half-pairing `(1/2) * hc3CutoffPairingOnCellAux` is pathwise the affine combination
of the cutoff half-energy, the two cutoff-mean coordinates and half the self-pairing of the
annealed mean `Y^-`, so `|Jtilde^-(e)|` is bounded by the sum of the expected absolute cutoff
pairing, the absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED cutoff-mean
row `(1/2) |<E[M₁] - Y₁^-, Y₂^-> + <Y₁^-, E[M₂] - Y₂^->|`. -/
theorem abs_respCenteredJMinus_le_three_rows_of_cutoff {d : ℕ} [NeZero d]
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
      (fun x => φ x * (optimizerField (respCoeffMinus F a) (uM a) x).2 i) (respCell jStar F t)) :
    |respCenteredJMinus P jStar F t e|
      ≤ (1 / 2 : ℝ) * (∫ a, |hc3CutoffPairingOnCellAux (respCell jStar F t) φ
            (respYMinus P jStar F t e) (respCoeffMinus F a) (uM a)| ∂P)
        + |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
            - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
                (respqMinus P jStar F t e) (respCoeffMinus F a)) ∂P|
        + (1 / 2 : ℝ) * |vecDot
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffMinus F a) (uM a)).1 i ∂P) - (respYMinus P jStar F t e).1)
              (respYMinus P jStar F t e).2
            + vecDot (respYMinus P jStar F t e).1
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffMinus F a) (uM a)).2 i ∂P) - (respYMinus P jStar F t e).2)| := by
  exact abs_respCenteredJMinus_le_three_rows P jStar F t e φ uM hq hblk hJ hA hW hM1 hM2
    (fun a => cutoff_halfPairing_eq_sub_aux (respCell jStar F t) φ (respYMinus P jStar F t e)
      (uM a) hcut.2.2.2.1 hφint (hEcell a) (h1cell a) (h2cell a))

/-- **The centred response against its three cutoff rows** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)), plus carriers, with the pathwise identity discharged from cutoff
membership.  The cutoff `φ` is a response cutoff on the cell `U_t` — so in particular it has cell
average one — and the cutoff-weighted optimizer state is integrable against that cell.  Under these
hypotheses the half-pairing `(1/2) * hc3CutoffPairingOnCellAux` is pathwise the affine combination
of the cutoff half-energy, the two cutoff-mean coordinates and half the self-pairing of the
annealed mean `Y^+`, so `|Jtilde^+(e)|` is bounded by the sum of the expected absolute cutoff
pairing, the absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED cutoff-mean
row `(1/2) |<E[M₁] - Y₁^+, Y₂^+> + <Y₁^+, E[M₂] - Y₂^+>|`. -/
theorem abs_respCenteredJPlus_le_three_rows_of_cutoff {d : ℕ} [NeZero d]
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
      (fun x => φ x * (optimizerField (respCoeffPlus F a) (uP a) x).2 i) (respCell jStar F t)) :
    |respCenteredJPlus P jStar F t e|
      ≤ (1 / 2 : ℝ) * (∫ a, |hc3CutoffPairingOnCellAux (respCell jStar F t) φ
            (respYPlus P jStar F t e) (respCoeffPlus F a) (uP a)| ∂P)
        + |∫ a, (cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
            - respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
                (respqPlus P jStar F t e) (respCoeffPlus F a)) ∂P|
        + (1 / 2 : ℝ) * |vecDot
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffPlus F a) (uP a)).1 i ∂P) - (respYPlus P jStar F t e).1)
              (respYPlus P jStar F t e).2
            + vecDot (respYPlus P jStar F t e).1
              ((fun i => ∫ a, (cutoffStateMeanAux (respCell jStar F t) φ
                (respCoeffPlus F a) (uP a)).2 i ∂P) - (respYPlus P jStar F t e).2)| := by
  exact abs_respCenteredJPlus_le_three_rows P jStar F t e φ uP hq hblk hJ hA hW hM1 hM2
    (fun a => cutoff_halfPairing_eq_sub_aux (respCell jStar F t) φ (respYPlus P jStar F t e)
      (uP a) hcut.2.2.2.1 hφint (hEcell a) (h1cell a) (h2cell a))

end

end Homogenization.HighContrast.Multiscale
