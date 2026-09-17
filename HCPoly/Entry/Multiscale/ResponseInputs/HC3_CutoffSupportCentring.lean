import HCPoly.Entry.Multiscale.ResponseInputs.HC2a_ReferenceCubePullback

/-!
# Centring one factor in a normalized cube average

`cubeAverage Q f` is the average of `f` over the cube `Q`, normalized by the volume of `Q`.
Subtracting a constant from one factor of a product changes the average of the product by that
constant times the average of the other factor.  Consequently, if the other factor has zero
average, the centred and uncentred products have the same average.

This is the algebraic step used in the cutoff argument `e.response.cutoff.estimate`, where the
negative-Besov duality bound is stated for a centred potential while the integration by parts
produces the uncentred one; the difference is a constant multiple of the average of the pairing,
which vanishes because the field paired against is divergence free.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Centring one factor of a normalized cube average.  For a cube `Q` and a constant `c`, the
average of `(f - c) * g` over `Q` equals the average of `f * g` minus `c` times the average of
`g`, whenever `f * g` and `g` are integrable on `cubeSet Q`. -/
theorem cubeAverage_sub_const_mul {d : ℕ} (Q : TriadicCube d) (c : ℝ) {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun y => f y * g y) (cubeSet Q))
    (hg : MeasureTheory.IntegrableOn g (cubeSet Q)) :
    cubeAverage Q (fun y => (f y - c) * g y)
      = cubeAverage Q (fun y => f y * g y) - c * cubeAverage Q g := by
  have hcg : MeasureTheory.IntegrableOn (fun y => c * g y) (cubeSet Q) := hg.const_mul c
  have hdiff : (fun y => (f y - c) * g y) = fun y => f y * g y - c * g y := by
    funext y
    ring
  rw [hdiff, cubeAverage, cubeAverage, cubeAverage]
  rw [MeasureTheory.integral_sub hf hcg, MeasureTheory.integral_const_mul]
  ring

/-- The centred and uncentred pairings agree when the paired field has zero average.  If
`cubeAverage Q g = 0`, then the average over `Q` of `(f - cubeAverage Q f) * g` equals the
average of `f * g`, whenever `f * g` and `g` are integrable on `cubeSet Q`. -/
theorem cubeAverage_centered_mul_of_average_eq_zero {d : ℕ} (Q : TriadicCube d)
    {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn (fun y => f y * g y) (cubeSet Q))
    (hg : MeasureTheory.IntegrableOn g (cubeSet Q))
    (hzero : cubeAverage Q g = 0) :
    cubeAverage Q (fun y => (f y - cubeAverage Q f) * g y)
      = cubeAverage Q (fun y => f y * g y) := by
  rw [cubeAverage_sub_const_mul Q (cubeAverage Q f) hf hg, hzero]
  ring

end

end Homogenization.HighContrast.Multiscale
