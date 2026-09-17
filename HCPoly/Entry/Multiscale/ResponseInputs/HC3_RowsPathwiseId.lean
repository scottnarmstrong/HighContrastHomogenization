import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# The pathwise cutoff decomposition identity on a bare cell

Expanding the two recentred differences inside the cutoff pairing of `e.response.cutoff.estimate`,
distributing the cutoff over the four pieces, and using the unit cell average of the cutoff
exhibits half the pairing as the cutoff-weighted half-energy minus the two cutoff-mean pairings
plus half the self-pairing of the inserted mean.  This is the pathwise identity on which the
integrated three-row decomposition rests, and it needs no ellipticity, no boundedness of the cell
and no positivity of the cutoff, only the indicated integrabilities.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The pathwise cutoff decomposition identity.**  On the bare cell `U`, half the cutoff pairing
of the optimizer state `X = (∇v, b ∇v)` at the inserted mean `Y` equals the cutoff-weighted
half-energy `cutoffHalfEnergyAux` minus half the pairing of the cutoff mean of the first coordinate
with `Y.2`, minus half the pairing of `Y.1` with the cutoff mean of the second coordinate, plus half
the self-pairing of `Y`.  This is the identity consumed by the integrated decomposition of
`e.response.cutoff.estimate`; the cell and the coefficient are arbitrary and the only hypotheses
are the integrabilities of the cutoff, the sample functions and the coordinates of the optimizer
state. -/
theorem cutoff_halfPairing_eq_sub_aux {d : ℕ} [NeZero d] (U : Set (Vec d)) (φ : Vec d → ℝ)
    (Y : BlockVec d) {b : CoeffField d} (v : AHarmonicFunction b U)
    (hmean : volumeAverage U φ = 1)
    (hφ : IntegrableOn φ U)
    (hE : IntegrableOn
      (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2) U)
    (h1 : ∀ i : Fin d, IntegrableOn (fun x => φ x * (optimizerField b v x).1 i) U)
    (h2 : ∀ i : Fin d, IntegrableOn (fun x => φ x * (optimizerField b v x).2 i) U) :
    (1 / 2 : ℝ) * hc3CutoffPairingOnCellAux U φ Y b v
      = cutoffHalfEnergyAux U φ b v
        - (1 / 2 : ℝ) * vecDot (cutoffStateMeanAux U φ b v).1 Y.2
        - (1 / 2 : ℝ) * vecDot Y.1 (cutoffStateMeanAux U φ b v).2
        + (1 / 2 : ℝ) * vecDot Y.1 Y.2 := by
  classical
  have hpB : (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
      = fun x => vecDot (fun i => φ x * (optimizerField b v x).1 i) Y.2 := by
    funext x
    simp only [vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hpC : (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)
      = fun x => vecDot Y.1 (fun i => φ x * (optimizerField b v x).2 i) := by
    funext x
    simp only [vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hB : IntegrableOn (fun x => φ x * vecDot (optimizerField b v x).1 Y.2) U := by
    rw [hpB]
    have h : Integrable
        (fun x => ∑ i, (φ x * (optimizerField b v x).1 i) * Y.2 i)
        (volume.restrict U) :=
      MeasureTheory.integrable_finsetSum (μ := volume.restrict U) Finset.univ
        (f := fun i x => (φ x * (optimizerField b v x).1 i) * Y.2 i)
        (fun i _ => (h1 i).integrable.mul_const (Y.2 i))
    simpa only [IntegrableOn, vecDot] using h
  have hC : IntegrableOn (fun x => φ x * vecDot Y.1 (optimizerField b v x).2) U := by
    rw [hpC]
    have h : Integrable
        (fun x => ∑ i, Y.1 i * (φ x * (optimizerField b v x).2 i))
        (volume.restrict U) :=
      MeasureTheory.integrable_finsetSum (μ := volume.restrict U) Finset.univ
        (f := fun i x => Y.1 i * (φ x * (optimizerField b v x).2 i))
        (fun i _ => (h2 i).integrable.const_mul (Y.1 i))
    simpa only [IntegrableOn, vecDot] using h
  have hD : IntegrableOn (fun x => φ x * vecDot Y.1 Y.2) U :=
    hφ.integrable.mul_const (vecDot Y.1 Y.2)
  have hAB : IntegrableOn
      ((fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
        - (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)) U :=
    hE.integrable.sub hB.integrable
  have hABC : IntegrableOn
      ((fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
        - (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
        - (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)) U :=
    hAB.integrable.sub hC.integrable
  have hpt : ∀ x : Vec d,
      φ x * vecDot ((optimizerField b v x).1 - Y.1) ((optimizerField b v x).2 - Y.2)
        = φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2
          - φ x * vecDot (optimizerField b v x).1 Y.2
          - φ x * vecDot Y.1 (optimizerField b v x).2
          + φ x * vecDot Y.1 Y.2 := by
    intro x
    have hvec : vecDot ((optimizerField b v x).1 - Y.1) ((optimizerField b v x).2 - Y.2)
        = vecDot (optimizerField b v x).1 (optimizerField b v x).2
          - vecDot (optimizerField b v x).1 Y.2
          - vecDot Y.1 (optimizerField b v x).2
          + vecDot Y.1 Y.2 := by
      simp only [sub_eq_add_neg, vecDot_add_right, vecDot_add_left, vecDot_neg_left,
        vecDot_neg_right]
      ring
    rw [hvec]
    ring
  have hF2eval : volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
      = vecDot (cutoffStateMeanAux U φ b v).1 Y.2 := by
    rw [hpB,
      volumeAverage_vecDot_right (f := fun x i => φ x * (optimizerField b v x).1 i)
        (v := Y.2) h1]
    rfl
  have hF3eval : volumeAverage U (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)
      = vecDot Y.1 (cutoffStateMeanAux U φ b v).2 := by
    rw [hpC,
      volumeAverage_vecDot_left (v := Y.1) (f := fun x i => φ x * (optimizerField b v x).2 i) h2]
    rfl
  have hF4eval : volumeAverage U (fun x => φ x * vecDot Y.1 Y.2) = vecDot Y.1 Y.2 := by
    have heq : (fun x => φ x * vecDot Y.1 Y.2) = (vecDot Y.1 Y.2) • φ := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, volumeAverage_smul, hmean, mul_one]
  have hsplit :
      volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2
          - φ x * vecDot (optimizerField b v x).1 Y.2
          - φ x * vecDot Y.1 (optimizerField b v x).2
          + φ x * vecDot Y.1 Y.2)
        = volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
          - volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
          - volumeAverage U (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)
          + volumeAverage U (fun x => φ x * vecDot Y.1 Y.2) := by
    rw [show (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2
          - φ x * vecDot (optimizerField b v x).1 Y.2
          - φ x * vecDot Y.1 (optimizerField b v x).2
          + φ x * vecDot Y.1 Y.2)
        = ((fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
            - (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
            - (fun x => φ x * vecDot Y.1 (optimizerField b v x).2))
            + (fun x => φ x * vecDot Y.1 Y.2) from rfl]
    rw [volumeAverage_add hABC hD, volumeAverage_sub hAB hC, volumeAverage_sub hE hB]
  have hmain : hc3CutoffPairingOnCellAux U φ Y b v
      = volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
        - vecDot (cutoffStateMeanAux U φ b v).1 Y.2
        - vecDot Y.1 (cutoffStateMeanAux U φ b v).2
        + vecDot Y.1 Y.2 := by
    calc
      hc3CutoffPairingOnCellAux U φ Y b v
          = volumeAverage U (fun x =>
              φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2
                - φ x * vecDot (optimizerField b v x).1 Y.2
                - φ x * vecDot Y.1 (optimizerField b v x).2
                + φ x * vecDot Y.1 Y.2) := by
            unfold hc3CutoffPairingOnCellAux
            apply congrArg (volumeAverage U)
            funext x
            exact hpt x
      _ = volumeAverage U (fun x =>
              φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
            - volumeAverage U (fun x => φ x * vecDot (optimizerField b v x).1 Y.2)
            - volumeAverage U (fun x => φ x * vecDot Y.1 (optimizerField b v x).2)
            + volumeAverage U (fun x => φ x * vecDot Y.1 Y.2) := hsplit
      _ = volumeAverage U (fun x =>
              φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)
            - vecDot (cutoffStateMeanAux U φ b v).1 Y.2
            - vecDot Y.1 (cutoffStateMeanAux U φ b v).2
            + vecDot Y.1 Y.2 := by
            rw [hF2eval, hF3eval, hF4eval]
  rw [hmain]
  simp only [cutoffHalfEnergyAux]
  ring

end

end Homogenization.HighContrast.Multiscale
