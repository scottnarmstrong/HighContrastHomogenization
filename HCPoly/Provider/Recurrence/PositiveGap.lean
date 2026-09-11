/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.GainArith
import HCPoly.Provider.Recurrence.SchattenEntries
import HCPoly.Provider.Recurrence.SchattenSandwich

/-!
# The positive-gap estimate

The fixed-grid recurrence gains from one scale to the next because the child
response is dominated by its parent average in the Loewner order, and the gap
between the two is measured by the determinant increment alone.  The estimate
that converts that order relation into a bound on the centered moment is
`l.fixed.geometry.positive.gap`, and its displayed chain is proved here.

The data are a positive block `D` — the excess of the averaged response over the
response itself, normalized — caught below `Ĝ = P + Y`, where `P` is the
relative mean and `Y` its fluctuation.  Four displays carry the estimate.

*The trace-power display.*  Positivity gives `tr(D^Q) ≤ |Ĝ|^{Q-1} tr D`, which
is the opening estimate of the reference proof and is already available; the
step taken here is the second half, `|Ĝ|^{Q-1} ≤ C(Q)(|P|^{Q-1} + |Y|^{Q-1})`,
which is the scalar two-point power-mean inequality applied to `Ĝ = P + Y`.  The
spectral size of the fluctuation is read through the Schatten size, which
dominates it, so the bound is stated in the norm the conclusion is written in.

*The trace comparison.*  Folding `tr D ≤ m^{1-1/Q}|D|_{S_Q}` into the second
summand produces the pointwise inequality whose expectation is the printed
`x^Q ≤ C|P|^{Q-1}b + Cy^{Q-1}x`: the first summand keeps the trace, whose mean
is the gap `b`, and the second is already linear in the Schatten size.

*The triangle inequality.*  The conclusion is assembled from
`F̂ - I = Y - (D - B)` and `|B|_{S_Q} ≤ tr B = b`.  The Schatten size is
subadditive only up to the dimensional factor `(2m)^{1/Q}` by the argument
available here — a block is caught between `∓|H|_{S_Q}I`, three such sandwiches
add, and a block caught between `∓tI` has Schatten size at most `(2m)^{1/Q}t`.
The reference constant `C_gap(m,Q)` depends on `m`, so the loss is invisible
downstream.

*The absorption.*  Young's inequality turns the quadratic display into the
linear one, and the constant is exhibited: from `x^Q ≤ Cp^{Q-1}b + Cy^{Q-1}x`
and `f ≤ K(y + x + b)` one gets `f ≤ K(1 + (2C)^{1/Q} + (2C)^{1/(Q-1)})` times
`y + p^{1-1/Q}b^{1/Q} + b`.  At the two extremes the determinant transport
supplies — spectral size `e^Δ` and gap `e^Δ - 1` — the last two summands are the
gain function `Φ_Q(Δ)`, which is the form the recurrence's terminal step reads.
-/

namespace Homogenization
namespace HighContrast
namespace Recurrence

open scoped MatrixOrder Matrix

noncomputable section

/-! ## The scalar power-mean inequality -/

/-- **The second half of the trace-power display of `l.fixed.geometry.positive.gap`**, as a
statement about real numbers: the `s`-th power of a sum is at most `2^{s-1}`
times the sum of the `s`-th powers, for `s ≥ 1`.  This is the convexity of the
power on the nonnegative axis. -/
theorem rpow_add_le_two_rpow_mul_add {a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 1 ≤ s) :
    (a + b) ^ s ≤ (2 : ℝ) ^ (s - 1) * (a ^ s + b ^ s) := by
  lift a to NNReal using ha
  lift b to NNReal using hb
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hs

/-! ## The gap is nonnegative -/

section Block

variable {d : ℕ}

/-- **The nonnegativity of the trace gap** of `l.fixed.geometry.positive.gap`: a doubled
block above the identity has trace at least `2d`, so `b = tr(P - I) ≥ 0`.  The
difference is positive semidefinite and the trace of such a block is
nonnegative. -/
theorem two_mul_le_blockTrace_of_one_le {Pm : BlockMat d}
    (h : (1 : FullBlockMat d) ≤ toFullBlockMat Pm) : 2 * (d : ℝ) ≤ blockTrace Pm := by
  have hPS : (toFullBlockMat Pm - 1).PosSemidef := Matrix.le_iff.mp h
  have htr := hPS.trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_one] at htr
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * d := by
    simp [BlockCoord, Fintype.card_sum, two_mul]
  rw [hcard] at htr
  rw [blockTrace]
  linarith only [htr]

/-! ## The trace-power display -/

/-- **The trace-power display of `l.fixed.geometry.positive.gap`.**  A positive block `D`
below `Ĝ = P + Y`, with the relative mean `P` of spectral size at most `p`,
satisfies `tr(D^Q) ≤ C(Q)(|P|^{Q-1} + |Y|^{Q-1}) tr D`.  The first inequality of
the printed chain is the trace-power estimate at the Loewner bound
`Ĝ ≤ (p + |Y|_{S_Q})I`, the fluctuation being caught below its own Schatten
size; the second is the scalar power-mean inequality. -/
theorem schattenNorm_rpow_le_mul_blockTrace {D Gh Pm Y : BlockMat d}
    (hD : IsSymmetricBlockMat D) (hDpos : (toFullBlockMat D).PosSemidef)
    (hY : IsSymmetricBlockMat Y) {p Q : ℝ} (hQ : 2 ≤ Q) (hp : 0 ≤ p)
    (hsplit : toFullBlockMat Gh = toFullBlockMat Pm + toFullBlockMat Y)
    (hPm : toFullBlockMat Pm ≤ p • (1 : FullBlockMat d))
    (hDG : toFullBlockMat D ≤ toFullBlockMat Gh) :
    schattenNorm Q D ^ Q ≤
      (2 : ℝ) ^ (Q - 2) * (p ^ (Q - 1) + schattenNorm Q Y ^ (Q - 1)) * blockTrace D := by
  have hQ0 : (0 : ℝ) < Q := by linarith only [hQ]
  have hQ1 : (1 : ℝ) ≤ Q := by linarith only [hQ]
  have hs0 : 0 ≤ schattenNorm Q Y := zero_le_schattenNorm hY Q
  have hYle : toFullBlockMat Y ≤ schattenNorm Q Y • (1 : FullBlockMat d) :=
    Matrix.le_iff.mpr (posSemidef_schattenNorm_smul_one_sub_add hY hQ0).1
  have hDle : toFullBlockMat D ≤ (p + schattenNorm Q Y) • (1 : FullBlockMat d) := by
    refine le_trans hDG ?_
    rw [hsplit, add_smul]
    exact add_le_add hPm hYle
  have htr : (0 : ℝ) ≤ blockTrace D := hDpos.trace_nonneg
  have hscal : (p + schattenNorm Q Y) ^ (Q - 1) ≤
      (2 : ℝ) ^ (Q - 2) * (p ^ (Q - 1) + schattenNorm Q Y ^ (Q - 1)) := by
    have hmean := rpow_add_le_two_rpow_mul_add hp hs0 (by linarith only [hQ] : (1 : ℝ) ≤ Q - 1)
    rwa [show Q - 1 - 1 = Q - 2 by ring] at hmean
  calc schattenNorm Q D ^ Q ≤ (p + schattenNorm Q Y) ^ (Q - 1) * blockTrace D :=
        schattenNorm_rpow_le_of_le_smul_one hD hDpos hDle hQ1
    _ ≤ (2 : ℝ) ^ (Q - 2) * (p ^ (Q - 1) + schattenNorm Q Y ^ (Q - 1)) * blockTrace D :=
        mul_le_mul_of_nonneg_right hscal htr

/-- **The trace-power display with the trace comparison folded in.**  Replacing
`tr D` by `m^{1-1/Q}|D|_{S_Q}` in the fluctuation summand — and only there —
leaves an inequality whose first summand still carries the trace, whose mean is
the gap `b`, and whose second summand is linear in the Schatten size.  This is
the pointwise form of the printed `x^Q ≤ C|P|^{Q-1}b + Cy^{Q-1}x`. -/
theorem schattenNorm_rpow_le_add_mul_schattenNorm {D Gh Pm Y : BlockMat d} (hd : 0 < d)
    (hD : IsSymmetricBlockMat D) (hDpos : (toFullBlockMat D).PosSemidef)
    (hY : IsSymmetricBlockMat Y) {p Q : ℝ} (hQ : 2 ≤ Q) (hp : 0 ≤ p)
    (hsplit : toFullBlockMat Gh = toFullBlockMat Pm + toFullBlockMat Y)
    (hPm : toFullBlockMat Pm ≤ p • (1 : FullBlockMat d))
    (hDG : toFullBlockMat D ≤ toFullBlockMat Gh) :
    schattenNorm Q D ^ Q ≤
      (2 : ℝ) ^ (Q - 2) * p ^ (Q - 1) * blockTrace D +
        (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) *
          (schattenNorm Q Y ^ (Q - 1) * schattenNorm Q D) := by
  have hQ1 : (1 : ℝ) ≤ Q := by linarith only [hQ]
  have hcoef : (0 : ℝ) ≤ (2 : ℝ) ^ (Q - 2) * schattenNorm Q Y ^ (Q - 1) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (zero_le_schattenNorm hY Q) _)
  have htrace := blockTrace_le_card_rpow_mul_schattenNorm hd hDpos hQ1
  calc schattenNorm Q D ^ Q
      ≤ (2 : ℝ) ^ (Q - 2) * (p ^ (Q - 1) + schattenNorm Q Y ^ (Q - 1)) * blockTrace D :=
        schattenNorm_rpow_le_mul_blockTrace hD hDpos hY hQ hp hsplit hPm hDG
    _ = (2 : ℝ) ^ (Q - 2) * p ^ (Q - 1) * blockTrace D +
          (2 : ℝ) ^ (Q - 2) * schattenNorm Q Y ^ (Q - 1) * blockTrace D := by ring
    _ ≤ (2 : ℝ) ^ (Q - 2) * p ^ (Q - 1) * blockTrace D +
          (2 : ℝ) ^ (Q - 2) * schattenNorm Q Y ^ (Q - 1) *
            ((2 * d : ℝ) ^ (1 - Q⁻¹) * schattenNorm Q D) := by
        have hstep := mul_le_mul_of_nonneg_left htrace hcoef
        linarith only [hstep]
    _ = (2 : ℝ) ^ (Q - 2) * p ^ (Q - 1) * blockTrace D +
          (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) *
            (schattenNorm Q Y ^ (Q - 1) * schattenNorm Q D) := by ring

/-! ## The triangle inequality of the closing step -/

/-- **The closing identity of `l.fixed.geometry.positive.gap`, estimated.**  From
`F̂ - I = Y - (D - B)` the Schatten size of the left side is at most the sum of
the three Schatten sizes, up to the dimensional factor `(2m)^{1/Q}`: each block
is caught between `∓|·|_{S_Q}I`, the three sandwiches add, and a block caught
between `∓tI` has Schatten size at most `(2m)^{1/Q}t`. -/
theorem schattenNorm_le_mul_add_add {H Y D B : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hY : IsSymmetricBlockMat Y) (hD : IsSymmetricBlockMat D) (hB : IsSymmetricBlockMat B)
    {Q : ℝ} (hQ : 0 < Q)
    (heq : toFullBlockMat H =
      toFullBlockMat Y - (toFullBlockMat D - toFullBlockMat B)) :
    schattenNorm Q H ≤
      (2 * d : ℝ) ^ Q⁻¹ * (schattenNorm Q Y + schattenNorm Q D + schattenNorm Q B) := by
  obtain ⟨hYs, hYa⟩ := posSemidef_schattenNorm_smul_one_sub_add hY hQ
  obtain ⟨hDs, hDa⟩ := posSemidef_schattenNorm_smul_one_sub_add hD hQ
  obtain ⟨hBs, hBa⟩ := posSemidef_schattenNorm_smul_one_sub_add hB hQ
  have hY0 : (0 : ℝ) ≤ schattenNorm Q Y := zero_le_schattenNorm hY Q
  have hD0 : (0 : ℝ) ≤ schattenNorm Q D := zero_le_schattenNorm hD Q
  have hB0 : (0 : ℝ) ≤ schattenNorm Q B := zero_le_schattenNorm hB Q
  refine schattenNorm_le_of_posSemidef hH hQ (by linarith only [hY0, hD0, hB0]) ?_ ?_
  · have hsum := (hYs.add hDa).add hBs
    have halg : schattenNorm Q Y • (1 : FullBlockMat d) - toFullBlockMat Y +
          (schattenNorm Q D • (1 : FullBlockMat d) + toFullBlockMat D) +
          (schattenNorm Q B • (1 : FullBlockMat d) - toFullBlockMat B) =
        (schattenNorm Q Y + schattenNorm Q D + schattenNorm Q B) •
            (1 : FullBlockMat d) - toFullBlockMat H := by
      rw [heq, add_smul, add_smul]
      abel
    rwa [halg] at hsum
  · have hsum := (hYa.add hDs).add hBa
    have halg : schattenNorm Q Y • (1 : FullBlockMat d) + toFullBlockMat Y +
          (schattenNorm Q D • (1 : FullBlockMat d) - toFullBlockMat D) +
          (schattenNorm Q B • (1 : FullBlockMat d) + toFullBlockMat B) =
        (schattenNorm Q Y + schattenNorm Q D + schattenNorm Q B) •
            (1 : FullBlockMat d) + toFullBlockMat H := by
      rw [heq, add_smul, add_smul]
      abel
    rwa [halg] at hsum

/-- **The closing step of `l.fixed.geometry.positive.gap` in the form the conclusion is
written in.**  The third Schatten size is the one of the mean gap `B = P - I`,
and there `|B|_{S_Q} ≤ tr B = b` because `B` is positive; so the closing
estimate reads directly in the gap. -/
theorem schattenNorm_le_mul_add_blockTrace {H Y D B : BlockMat d} (hH : IsSymmetricBlockMat H)
    (hY : IsSymmetricBlockMat Y) (hD : IsSymmetricBlockMat D) (hB : IsSymmetricBlockMat B)
    (hBpos : (toFullBlockMat B).PosSemidef) {Q : ℝ} (hQ : 1 ≤ Q)
    (heq : toFullBlockMat H =
      toFullBlockMat Y - (toFullBlockMat D - toFullBlockMat B)) :
    schattenNorm Q H ≤
      (2 * d : ℝ) ^ Q⁻¹ * (schattenNorm Q Y + schattenNorm Q D + blockTrace B) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hfactor : (0 : ℝ) ≤ (2 * d : ℝ) ^ Q⁻¹ :=
    Real.rpow_nonneg (by positivity) _
  refine le_trans (schattenNorm_le_mul_add_add hH hY hD hB hQ0 heq) ?_
  exact mul_le_mul_of_nonneg_left
    (by linarith only [schattenNorm_le_blockTrace hB hBpos hQ]) hfactor

end Block

/-! ## The absorption and the conclusion -/

/-- The dichotomy bound of the absorption step, isolated from its witnesses: a
sum whose middle term is dominated by a combination of the two others is
dominated by the sum with the combination's coefficients. -/
private theorem add_le_mul_add {κ₁ κ₂ x y g b : ℝ} (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂)
    (hy : 0 ≤ y) (hg : 0 ≤ g) (hb : 0 ≤ b) (h : x ≤ κ₁ * g + κ₂ * y) :
    y + x + b ≤ (1 + κ₁ + κ₂) * (y + g + b) := by
  have hexp : (1 + κ₁ + κ₂) * (y + g + b) =
      y + (κ₁ * g + κ₂ * y) + b + (κ₁ * y + κ₂ * g + g + κ₁ * b + κ₂ * b) := by ring
  rw [hexp]
  have h1 : (0 : ℝ) ≤ κ₁ * y := mul_nonneg hκ₁ hy
  have h2 : (0 : ℝ) ≤ κ₂ * g := mul_nonneg hκ₂ hg
  have h3 : (0 : ℝ) ≤ κ₁ * b := mul_nonneg hκ₁ hb
  have h4 : (0 : ℝ) ≤ κ₂ * b := mul_nonneg hκ₂ hb
  linarith only [h, h1, h2, h3, h4, hg]

/-- **The conclusion of `l.fixed.geometry.positive.gap`, with its constant exhibited.**  The
quadratic display `x^Q ≤ Cp^{Q-1}b + Cy^{Q-1}x` and the closing estimate
`f ≤ K(y + x + b)` combine into the printed bound
`f ≤ C_gap(y + |P|^{1-1/Q}b^{1/Q} + b)` with the explicit witness
`C_gap = K(1 + (2C)^{1/Q} + (2C)^{1/(Q-1)})`: Young's inequality replaces `x` by
the two other terms, and the three resulting coefficients are each at most that
witness. -/
theorem le_gap_bound {Q C K f x y p b : ℝ} (hQ : 2 ≤ Q) (hC : 0 < C) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) (hb : 0 ≤ b)
    (habsorb : x ^ Q ≤ C * p ^ (Q - 1) * b + C * y ^ (Q - 1) * x)
    (htri : f ≤ K * (y + x + b)) :
    f ≤ K * (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) *
      (y + p ^ (1 - Q⁻¹) * b ^ Q⁻¹ + b) := by
  have h2C : (0 : ℝ) < 2 * C := by linarith only [hC]
  have hκ₁ : (0 : ℝ) ≤ (2 * C) ^ Q⁻¹ := Real.rpow_nonneg h2C.le _
  have hκ₂ : (0 : ℝ) ≤ (2 * C) ^ (Q - 1)⁻¹ := Real.rpow_nonneg h2C.le _
  have hg0 : (0 : ℝ) ≤ p ^ (1 - Q⁻¹) * b ^ Q⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hp _) (Real.rpow_nonneg hb _)
  have hyoung := le_rpow_add_of_rpow_le hQ hC hx hy hp hb habsorb
  have hchain := add_le_mul_add hκ₁ hκ₂ hy hg0 hb hyoung
  calc f ≤ K * (y + x + b) := htri
    _ ≤ K * ((1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) *
          (y + p ^ (1 - Q⁻¹) * b ^ Q⁻¹ + b)) := mul_le_mul_of_nonneg_left hchain hK
    _ = K * (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) *
          (y + p ^ (1 - Q⁻¹) * b ^ Q⁻¹ + b) := by rw [mul_assoc]

/-- **The positive-gap estimate at the two extremes of the determinant
transport.**  When the relative mean has spectral size at most `e^Δ` and trace
gap at most `e^Δ - 1` — which is what the determinant transport supplies at
consecutive scales — the last two summands of the positive-gap conclusion are
the gain function `Φ_Q(Δ)`.  This is the form the terminal step of
`p.fixed.geometry.parent.child.recurrence` consumes. -/
theorem le_gap_bound_gainPhi {Q C K f x y p b Δ : ℝ} (hQ : 2 ≤ Q) (hC : 0 < C) (hK : 0 ≤ K)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 0 ≤ p) (hb : 0 ≤ b) (hΔ : 0 ≤ Δ)
    (hpΔ : p ≤ Real.exp Δ) (hbΔ : b ≤ Real.exp Δ - 1)
    (habsorb : x ^ Q ≤ C * p ^ (Q - 1) * b + C * y ^ (Q - 1) * x)
    (htri : f ≤ K * (y + x + b)) :
    f ≤ K * (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) * (y + gainPhi Q Δ) := by
  have h2C : (0 : ℝ) < 2 * C := by linarith only [hC]
  have hκ₁ : (0 : ℝ) ≤ (2 * C) ^ Q⁻¹ := Real.rpow_nonneg h2C.le _
  have hκ₂ : (0 : ℝ) ≤ (2 * C) ^ (Q - 1)⁻¹ := Real.rpow_nonneg h2C.le _
  have hCg : (0 : ℝ) ≤ K * (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹) :=
    mul_nonneg hK (by linarith only [hκ₁, hκ₂])
  have hphi := rpow_mul_rpow_add_le_gainPhi (by linarith only [hQ] : (1 : ℝ) ≤ Q) hΔ hp hpΔ hb hbΔ
  refine le_trans (le_gap_bound hQ hC hK hx hy hp hb habsorb htri) ?_
  exact mul_le_mul_of_nonneg_left (by linarith only [hphi]) hCg

end

end Recurrence
end HighContrast
end Homogenization
