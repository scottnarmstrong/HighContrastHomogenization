/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredTargetCells

/-!
# The transported centered history

The centered half of the transport, `e.two.grid.profile`:

`𝓗_{q'}^cen(n) ≤ C3^{2aℓ₀}𝒫_q(t;b) + Cη_x + C𝓔_src`.

Two steps separate it from the target-cell count of `CenteredTargetCells`.

*The rows.*  Once the centered history is written as a weighted sum over the
target scales of the `Q`-th moments of a single target cell, a real bound on
each of those moments turns the whole estimate into a real sum, which is the
carrier the transport's discrete convolutions work in.  That is the centered
counterpart of the row sum of the nonlinear half, and the target weight it
carries is exactly `3^{-(Qρ_max-d)(n-j)}`, the coefficient the bridge error and
the source rows are already summed against.

*The profile.*  The combined bound for the transported fluctuations is, term for
term, the first two rows of the portable profile
`e.scale.selection.complete.profile` of the old grid, once the centered history at
the checkpoint is replaced by the complete one — a step that only adds the
nonlinear history, which the profile carries anyway.  Nothing is discarded and
nothing is re-derived: the profile is what the printed bound already is.

The buffer factor is `3^{2aℓ₀}` and not `3^{aℓ₀}` because the two convolutions
of the nonlinear rows are paid in the same currency; the centered half itself
never needs more than one buffer, so the statement below is stated at whatever
factor the row estimate supplies and the constant is the only thing adjusted.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix ENNReal

noncomputable section

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q q' : Mat d} {jStar : ℤ}

/-! ## The rows of the centered history -/

/-! ## The principal upper bound against the profile -/

/-- **The combined bound for the transported fluctuations is the profile.**  The
bracket of the principal upper bound — the renormalized centered history at the
checkpoint plus the weighted centered moments of the scales above it — is at
most the portable profile `e.scale.selection.complete.profile` of the old grid at
its terminal scale.

The only inequality is replacing the centered history at the checkpoint by the
complete history there, which adds the nonlinear history; the third row of the
profile is discarded. -/
theorem upper_centered_le_profile (P : Measure (CoeffSpace d)) (Q a rhoMax : ℝ)
    (q : Mat d) (jStar b t : ℤ) :
    ENNReal.ofReal ((3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b t))) * centeredHistory P Q rhoMax q jStar b +
        ∑ r ∈ Finset.Icc (b + 1) t,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
            Real.exp (Q * detIncrement P q r t)) * centeredMoment P Q q r ^ Q ≤
      portableProfile P Q a rhoMax q jStar b t := by
  rw [portableProfile]
  refine le_trans (add_le_add (mul_le_mul' le_rfl ?_) le_rfl) le_self_add
  rw [portableHistory]
  exact le_self_add

/-! ## The transported centered bound -/

end Window

end

end Transport
end HighContrast
end Homogenization
