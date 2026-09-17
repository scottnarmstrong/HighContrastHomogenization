import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constant arithmetic of the pathwise cutoff bound

The negative-Besov duality bound of the cutoff argument yields, on a reference cube, the product
of two coefficient bounds and two pulled-back seminorm bounds.  This file assembles those factors
into the single shape consumed by the annealed estimate: a dimensional constant times the scale
weight `3 ^ (-t)` times the square of the scale-average seminorm.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- The product of the two coefficient bounds and the two pulled-back seminorm bounds of the
pathwise cutoff estimate is bounded by the dimensional constant `K * L * 3 * d ^ 2` times the
scale weight `3 ^ (-t)` and the squared scale-average seminorm `A ^ 2`.  The coefficient bounds
are `gradCoeff ≤ K * 3 ^ (-t)` and `fluxCoeff ≤ L`, the seminorm bounds are `scaledGrad ≤ G * A`
and `scaledFlux ≤ f * A`, and the two Frobenius factors satisfy `G * f ≤ 3 * d ^ 2`; all
quantities are nonnegative.  This is the form in which the pathwise cutoff bound
`e.response.cutoff.estimate` feeds the annealed one. -/
theorem mul_le_const_mul_rpow_mul_sq {d : ℕ} (t : ℤ) {gradCoeff fluxCoeff scaledGrad scaledFlux
    G f A K L : ℝ}
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hf : 0 ≤ f) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hgc : 0 ≤ gradCoeff) (hfc : 0 ≤ fluxCoeff)
    (hsg : 0 ≤ scaledGrad) (hsf : 0 ≤ scaledFlux)
    (hgradCoeff : gradCoeff ≤ K * (3 : ℝ) ^ (-(t : ℝ)))
    (hfluxCoeff : fluxCoeff ≤ L)
    (hscaledGrad : scaledGrad ≤ G * A) (hscaledFlux : scaledFlux ≤ f * A)
    (hGf : G * f ≤ 3 * (d : ℝ) ^ 2) :
    (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) ≤
      (K * L * (3 * (d : ℝ) ^ 2)) * ((3 : ℝ) ^ (-(t : ℝ)) * A ^ 2) := by
  have _ := hgc
  have _ := hf
  have hr : (0 : ℝ) < (3 : ℝ) ^ (-(t : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hr0 : 0 ≤ (3 : ℝ) ^ (-(t : ℝ)) := le_of_lt hr
  have hKr : 0 ≤ K * (3 : ℝ) ^ (-(t : ℝ)) := mul_nonneg hK hr0
  have hGA : 0 ≤ G * A := mul_nonneg hG hA
  have h1 : gradCoeff * fluxCoeff ≤ (K * (3 : ℝ) ^ (-(t : ℝ))) * L :=
    mul_le_mul hgradCoeff hfluxCoeff hfc hKr
  have h2 : scaledGrad * scaledFlux ≤ (G * A) * (f * A) :=
    mul_le_mul hscaledGrad hscaledFlux hsf hGA
  have h3 : ((K * (3 : ℝ) ^ (-(t : ℝ))) * L) * ((G * A) * (f * A)) ≤
      (K * L * (3 * (d : ℝ) ^ 2)) * ((3 : ℝ) ^ (-(t : ℝ)) * A ^ 2) := by
    calc
      ((K * (3 : ℝ) ^ (-(t : ℝ))) * L) * ((G * A) * (f * A))
          = (K * L) * ((3 : ℝ) ^ (-(t : ℝ)) * ((G * f) * A ^ 2)) := by
            ring
      _ ≤ (K * L) * ((3 : ℝ) ^ (-(t : ℝ)) * ((3 * (d : ℝ) ^ 2) * A ^ 2)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hGf (sq_nonneg A)) hr0
            · exact mul_nonneg hK hL
      _ = (K * L * (3 * (d : ℝ) ^ 2)) * ((3 : ℝ) ^ (-(t : ℝ)) * A ^ 2) := by
            ring
  exact le_trans (mul_le_mul h1 h2 (mul_nonneg hsg hsf) (mul_nonneg hKr hL)) h3

end

end Homogenization.HighContrast.Multiscale
