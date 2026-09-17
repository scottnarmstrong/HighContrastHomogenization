import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRowsSplitCentred
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRowsCentredEnergy
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRowsPairHalf

/-!
# The centred response against its three cutoff rows (AK.HC (3.45)-(3.54))

The centred responses `Jtilde^±(e)` of `e.response.cutoff.estimate` are the annealed energies at
the recentred loads minus half the pairing of the two coordinates of the annealed mean `Y^±`.  The
cutoff decomposition of the cutoff pairing exhibits the half-pairing as the cutoff half-energy
minus the two cutoff-mean pairings plus half the self-pairing of `Y^±`, so integrating against the
law and bounding the result reduces the centred response to three rows: the expected absolute
cutoff pairing, the absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED
cutoff-mean row, in which the integrated cutoff means appear only through their difference from the
annealed mean.  These are the `e4`, `e1` and `e2 + e3` of the printed variational calculation.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The centred response against its three cutoff rows** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)), minus carriers.  If the half-pairing
`(1/2) * hc3CutoffPairingOnCellAux` is pathwise the affine combination of the cutoff half-energy,
the two cutoff-mean coordinates and half the self-pairing of the annealed mean `Y^-`, then the
centred response `|Jtilde^-(e)|` is bounded by the sum of the expected absolute cutoff pairing, the
absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED cutoff-mean row
`(1/2) |<E[M₁] - Y₁^-, Y₂^-> + <Y₁^-, E[M₂] - Y₂^->|`. -/
theorem abs_respCenteredJMinus_le_three_rows {d : ℕ} [NeZero d]
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
    (hid : ∀ a, (1 / 2 : ℝ) *
        hc3CutoffPairingOnCellAux (respCell jStar F t) φ (respYMinus P jStar F t e)
          (respCoeffMinus F a) (uM a)
      = cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)
        - (1 / 2 : ℝ) * vecDot
            (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1
            (respYMinus P jStar F t e).2
        - (1 / 2 : ℝ) * vecDot (respYMinus P jStar F t e).1
            (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2
        + (1 / 2 : ℝ) * vecDot (respYMinus P jStar F t e).1 (respYMinus P jStar F t e).2) :
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
  rw [respCenteredJMinus_eq_respEJMinus_sub P jStar F t e hq hblk]
  have hmain := abs_integral_sub_half_vecDot_le_centred P
    (respYMinus P jStar F t e).1 (respYMinus P jStar F t e).2
    (fun a => (1 / 2 : ℝ) * hc3CutoffPairingOnCellAux (respCell jStar F t) φ
      (respYMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a))
    (fun a => (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).1)
    (fun a => (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffMinus F a) (uM a)).2)
    (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a))
    hJ hA hW hM1 hM2 hid
  have hpair := abs_integral_half_hc3CutoffPairingOnCellAux_le P (respCell jStar F t) φ
    (respYMinus P jStar F t e) (respCoeffMinus F) uM
  simp only [respEJMinus] at hmain ⊢
  linarith only [hmain, hpair]

/-- **The centred response against its three cutoff rows** (`e.response.cutoff.estimate`,
AK.HC (3.45)-(3.54)), plus carriers.  If the half-pairing
`(1/2) * hc3CutoffPairingOnCellAux` is pathwise the affine combination of the cutoff half-energy,
the two cutoff-mean coordinates and half the self-pairing of the annealed mean `Y^+`, then the
centred response `|Jtilde^+(e)|` is bounded by the sum of the expected absolute cutoff pairing, the
absolute cutoff energy defect `E[cutoffHalfEnergy - J]`, and the CENTRED cutoff-mean row
`(1/2) |<E[M₁] - Y₁^+, Y₂^+> + <Y₁^+, E[M₂] - Y₂^+>|`. -/
theorem abs_respCenteredJPlus_le_three_rows {d : ℕ} [NeZero d]
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
    (hid : ∀ a, (1 / 2 : ℝ) *
        hc3CutoffPairingOnCellAux (respCell jStar F t) φ (respYPlus P jStar F t e)
          (respCoeffPlus F a) (uP a)
      = cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)
        - (1 / 2 : ℝ) * vecDot
            (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1
            (respYPlus P jStar F t e).2
        - (1 / 2 : ℝ) * vecDot (respYPlus P jStar F t e).1
            (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2
        + (1 / 2 : ℝ) * vecDot (respYPlus P jStar F t e).1 (respYPlus P jStar F t e).2) :
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
  rw [respCenteredJPlus_eq_respEJPlus_sub P jStar F t e hq hblk]
  have hmain := abs_integral_sub_half_vecDot_le_centred P
    (respYPlus P jStar F t e).1 (respYPlus P jStar F t e).2
    (fun a => (1 / 2 : ℝ) * hc3CutoffPairingOnCellAux (respCell jStar F t) φ
      (respYPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (fun a => cutoffHalfEnergyAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a))
    (fun a => (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).1)
    (fun a => (cutoffStateMeanAux (respCell jStar F t) φ (respCoeffPlus F a) (uP a)).2)
    (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a))
    hJ hA hW hM1 hM2 hid
  have hpair := abs_integral_half_hc3CutoffPairingOnCellAux_le P (respCell jStar F t) φ
    (respYPlus P jStar F t e) (respCoeffPlus F) uP
  simp only [respEJPlus] at hmain ⊢
  linarith only [hmain, hpair]

end

end Homogenization.HighContrast.Multiscale
