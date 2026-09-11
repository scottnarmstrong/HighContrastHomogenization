/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredFillingRows
import HCPoly.Provider.Transport.CenteredAncestor
import HCPoly.Provider.Transport.AncestorCounting
import HCPoly.Provider.Transport.AncestorStationarity
import HCPoly.Provider.Transport.DiscreteConvolution
import HCPoly.Provider.Transport.NonlinearRow
import HCPoly.Provider.Transport.CenteredUpper

/-!
# The two rows of the transported centered history, in the carriers they are consumed in

The principal upper bound of the transported centered history binds its fresh
row as a *real* number and its inherited rows as a weighted sum against the
centered history at the checkpoint.  Both estimates live in the extended
reals; this file carries them across.

*The fresh row.*  The contribution of the fluctuations at the new scales is fed
by `Transport.centered_filling_rows_le`, whose right side is a product of an
`ENNReal.ofReal` with a finite sum of `ENNReal.ofReal`s against the centered
moments `v_r^q`.  On the range of a coupled window those moments are finite, so
the whole right side is the image of a single real number, and the mixed norm is
finite with the printed real bound on its real value.  Nothing is estimated
here: the finiteness clause of `p.two.grid.transport` is what makes
the passage exact.

*The inherited rows.*  The ancestor composition — the codimension-one row inside
one scale-`b` ancestor, the stationarity comparison
`E[X_B^Q] ≤ 𝓗_q^{cen}(b)`, and the count of relevant ancestors — is assembled
into `e.two.grid.old.history.factor` over the ancestors of one target
cell, in both the unrestricted and the row-restricted range.  The passage from
these first-power weights to the `Q`-th-power target coefficient the principal
upper bound binds is `Transport.inherited_coefficient_le`, and the sum over the target
scales is the same bare geometric series the bridge error uses, because
`Qρ_max - d = Qg + a > 0`.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The fresh row as a real number -/

/-- **The centered rows of the filling, collapsed onto one real number.**  On a
range whose centered moments are finite, the right side of
`Transport.centered_filling_rows_le` is the image of a real number under
`ENNReal.ofReal`.  This is the form the fresh row of the transported
fluctuations is stated in, and it also exhibits the finiteness of the mixed norm
on the left. -/
theorem centered_filling_rows_le_ofReal {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hPs : HCPoly.Frozen.IsStationaryLaw P)
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {Q : ℝ} (hQ : 2 ≤ Q) {l : ℤ} {q : Mat d}
    (hq : IsRoundedGrid l q) {t : ℤ} {R : Finset ℤ} {Z : ℤ → Finset (Fin d → ℤ)}
    {c : ℤ → ℝ} (hc : ∀ r ∈ R, 0 ≤ c r) (hl : ∀ r ∈ R, l ≤ r)
    (hint : ∀ r ∈ R, HasFiniteAdaptedMean P q r)
    (hEr : ∀ r ∈ R, Book.Ch02.BlockPosDef (adaptedMean P q r))
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    (hmean : ∀ r ∈ R, BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q r))
    (hfin : ∀ r ∈ R, centeredMoment P Q q r ≠ ⊤) :
    lqSchattenSize P Q (fun a => ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
        c r • toFullBlockMat (blockSub (coarseBlock (adaptedCellAt q r w) a)
          (adaptedMean P q r)))) (adaptedMean P q t) ≤
      ENNReal.ofReal (2 * (d : ℝ) *
          ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
            Real.sqrt ((3 : ℝ) ^ d)) *
        ∑ r ∈ R, Real.sqrt (∑ _w ∈ Z r, c r ^ 2) *
            ((2 * d : ℝ) ^ Q⁻¹ * Real.exp (detIncrement P q r t)) *
          (centeredMoment P Q q r).toReal) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  have hC0 : (0 : ℝ) ≤ 2 * (d : ℝ) *
      ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt Q) *
        Real.sqrt ((3 : ℝ) ^ d)) := by
    have hconst : (0 : ℝ) ≤ IndependentSums.rosenthalBennettIntegralConst := by
      simp only [IndependentSums.rosenthalBennettIntegralConst]
      positivity
    have hterm : (0 : ℝ) ≤ 4 * IndependentSums.rosenthalBennettIntegralConst *
        Real.sqrt Q := mul_nonneg (by linarith only [hconst]) (Real.sqrt_nonneg _)
    have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact mul_nonneg (by linarith only [hdR])
      (mul_nonneg (by linarith only [hQ0, hterm]) (Real.sqrt_nonneg _))
  have hw0 : ∀ r : ℤ, (0 : ℝ) ≤ Real.sqrt (∑ _w ∈ Z r, c r ^ 2) *
      ((2 * d : ℝ) ^ Q⁻¹ * Real.exp (detIncrement P q r t)) := fun r =>
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _))
  have hrow : ∀ r ∈ R,
      ENNReal.ofReal (Real.sqrt (∑ _w ∈ Z r, c r ^ 2) *
          ((2 * d : ℝ) ^ Q⁻¹ * Real.exp (detIncrement P q r t))) *
        centeredMoment P Q q r =
      ENNReal.ofReal (Real.sqrt (∑ _w ∈ Z r, c r ^ 2) *
          ((2 * d : ℝ) ^ Q⁻¹ * Real.exp (detIncrement P q r t)) *
        (centeredMoment P Q q r).toReal) := by
    intro r hr
    rw [ENNReal.ofReal_mul (hw0 r), ENNReal.ofReal_toReal (hfin r hr)]
  refine le_trans (centered_filling_rows_le hPs hP hQ hq hc hl hint hEr hEt hmean hfin)
    (le_of_eq ?_)
  rw [Finset.sum_congr rfl hrow, ← ENNReal.ofReal_sum_of_nonneg fun r _ =>
      mul_nonneg (hw0 r) ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul hC0]

/-! ## The inherited rows over the ancestors of one target cell -/

/-! ## The inherited rows against the target coefficient -/

end

end Transport
end HighContrast
end Homogenization
