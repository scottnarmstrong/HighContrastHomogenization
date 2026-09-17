import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# The integrated centred cutoff decomposition (AK.HC (3.45)-(3.54))

The cutoff pairing `hc3CutoffPairingOnCellAux U φ Y b v` tests the optimizer state
`X = (∇v, b ∇v)` against the annealed mean `Y` of AK.HC (2.32), weighted by the cutoff `φ`.
Its pathwise expansion exhibits the half-pairing as the cutoff-weighted half-energy
`cutoffHalfEnergyAux` minus the two mean pairings plus half the self-pairing of `Y`.

Integrating that expansion against the law `P` and applying the triangle inequality exhibits the
centred response as the sum of the absolute cutoff pairing, the absolute energy defect
`cutoffHalfEnergyAux - J`, and the two integrated cutoff-mean terms.  This is the first step of the
variational calculation of `e.response.cutoff.estimate` (AK.HC (3.45)-(3.54)), taken before the
products are separated by Young's inequality.

The statement is the integrated form of `cutoff_halfPairing_eq_sub`.  The cell `U` and the
coefficient `b` are arbitrary: no ellipticity of `b`, no boundedness of `U`, and no positivity
of `φ` enter, only the integrabilities of the sample functions and of the coordinates of the
optimizer state.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff pairing term on the cell `U`: the cutoff-weighted recentred pairing
`(φ (X₁ - Y₁) · (X₂ - Y₂))_U` of the optimizer state `X = (∇v, b ∇v)` at the annealed mean `Y`
of AK.HC (2.32).  This is the local spelling of the pairing consumed by the cutoff estimate of
AK.HC (3.45)-(3.54). -/
def hc3CutoffPairingOnCellAux {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) (Y : BlockVec d)
    (b : CoeffField d) (v : AHarmonicFunction b U) : ℝ :=
  volumeAverage U fun x =>
    φ x * vecDot ((optimizerField b v x).1 - Y.1) ((optimizerField b v x).2 - Y.2)

/-- The cutoff-weighted mean of the doubled optimizer state `X = (∇v, b ∇v)` on the cell `U`:
the pair whose coordinates are the cutoff averages of the coordinates of `X`.  Its two
components are the mean pairings appearing in the centred decomposition of AK.HC (3.45)-(3.54). -/
def cutoffStateMeanAux {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) (b : CoeffField d)
    (v : AHarmonicFunction b U) : BlockVec d :=
  (fun i => volumeAverage U fun x => φ x * (optimizerField b v x).1 i,
   fun i => volumeAverage U fun x => φ x * (optimizerField b v x).2 i)

/-- The cutoff-weighted half-energy of the optimizer state `X = (∇v, b ∇v)`: one half of the
cutoff average of `φ (X₁ · X₂)`.  This is the energy term subtracted from the response on the
right-hand side of the centred decomposition of AK.HC (3.45)-(3.54). -/
def cutoffHalfEnergyAux {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) (b : CoeffField d)
    (v : AHarmonicFunction b U) : ℝ :=
  (1 / 2 : ℝ) * volumeAverage U
    (fun x => φ x * vecDot (optimizerField b v x).1 (optimizerField b v x).2)

end

end Homogenization.HighContrast.Multiscale
