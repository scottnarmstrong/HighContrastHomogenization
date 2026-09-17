import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# The cutoff pairing row against the absolute pairing (AK.HC (3.45)-(3.54))

The half-pairing `(1 / 2) * hc3CutoffPairingOnCellAux` is the cutoff pairing row of the centred
decomposition of `e.response.cutoff.estimate`.  Its expectation is bounded by one half of the
expected absolute pairing, and a fortiori by the whole expected absolute pairing, which is the
last summand carried by the cutoff estimate.

Neither bound needs integrability: when the pairing is not integrable the Bochner integral takes
the junk value zero, so the inequalities read `0 ≤ 0` and `0 ≤` a nonnegative integral.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff pairing row `(1 / 2) * hc3CutoffPairingOnCellAux` is bounded in absolute value by
half of the expected absolute pairing.  No integrability of the pairing is assumed: both sides are
read through the Bochner integral. -/
theorem abs_integral_half_hc3CutoffPairingOnCellAux_le {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (U : Set (Vec d)) (φ : Vec d → ℝ) (Y : BlockVec d)
    (c : CoeffSpace d → CoeffField d) (v : (a : CoeffSpace d) → AHarmonicFunction (c a) U) :
    |∫ a, (1 / 2 : ℝ) * hc3CutoffPairingOnCellAux U φ Y (c a) (v a) ∂P|
      ≤ (1 / 2 : ℝ) * ∫ a, |hc3CutoffPairingOnCellAux U φ Y (c a) (v a)| ∂P := by
  rw [integral_const_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)

end

end Homogenization.HighContrast.Multiscale
