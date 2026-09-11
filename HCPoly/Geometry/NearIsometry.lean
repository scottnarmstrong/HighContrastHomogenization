/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.DeterminantLoss

/-!
# Near-isometric comparison of canonical geometries

This file proves `e.global.selection.metric.comparison`: if two positive doubled blocks
satisfy the near-isometry hypothesis `(1-ζ)E ≤ F ≤ (1+ζ)E` of
`e.two.grid.near` with `0 ≤ ζ < 1`, then the imbalances
and the canonical metrics of the two are comparable,

    𝔡(F) ≤ (1+ζ)^3 (1-ζ)^{-1} 𝔡(E),
    d_pr([m(E)],[m(F)]) ≤ ½ log ((1+ζ)/(1-ζ)).

The proof is the printed one.  Sharp order reversal turns the hypothesis into
`(1+ζ)^{-1} E^♯ ≤ F^♯ ≤ (1-ζ)^{-1} E^♯`; joint monotonicity and homogeneity of
the geometric mean then give the comparison of the canonical metric blocks, from
which the projective bound follows by taking lower-right principal blocks and
inverting.  For the imbalance the chain is

    F ≤ (1+ζ) E ≤ (1+ζ) 𝔡(E)^{1/2} M(E)
      ≤ (1+ζ) ((1+ζ)/(1-ζ))^{1/2} 𝔡(E)^{1/2} M(F),

whose scalar is then squared.  The step `E ≤ 𝔡(E)^{1/2} M(E)` is used here in
its unconditional form, straight from the definition of `𝔡`: unlike the balance
chain, it needs no comparison between `E` and `E^♯`.

Both shared steps — the squaring and the principal-block inversion — are taken
from the determinant-loss comparison, which is where they are proved.
-/

namespace Homogenization
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Square-root and contrast arithmetic

As in the determinant-loss comparison, every square root is consumed by an
abstract-real helper before any linear-arithmetic step runs. -/

private theorem sq_mul_sqrt_mul_sqrt {c a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (c * Real.sqrt a * Real.sqrt b) ^ 2 = c ^ 2 * (a * b) := by
  rw [mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  ring

private theorem mul_inv_eq_inv_div {z : ℝ} (hm : (0:ℝ) < 1 - z) (hp : (0:ℝ) < 1 + z) :
    (1 - z) * (1 + z)⁻¹ = ((1 + z) / (1 - z))⁻¹ := by
  have hm' : (1 : ℝ) - z ≠ 0 := ne_of_gt hm
  have hp' : (1 : ℝ) + z ≠ 0 := ne_of_gt hp
  field_simp

private theorem contrast_cube {z a : ℝ} (hm : (0:ℝ) < 1 - z) :
    (1 + z) ^ 2 * (a * ((1 + z) / (1 - z))) = ((1 + z) ^ 3 / (1 - z)) * a := by
  have hm' : (1 : ℝ) - z ≠ 0 := ne_of_gt hm
  field_simp

/-! ## The comparison -/

/-- **Near-isometric canonical comparison**.  The first clause is the imbalance
under a near-isometric comparison and the second is
`e.global.selection.metric.comparison`. -/
theorem canonNearIsometry (hd : 2 ≤ d) {E F : FullBlockMat d} (hE : E.PosDef) (hF : F.PosDef)
    {ζ : ℝ} (hζ₀ : 0 ≤ ζ) (hζ₁ : ζ < 1) (hlow : (1 - ζ) • E ≤ F) (hhigh : F ≤ (1 + ζ) • E) :
    canonImbalance F ≤ ((1 + ζ) ^ 3 / (1 - ζ)) * canonImbalance E ∧
      projDist (canonMetric E) (canonMetric F) ≤
        (1 / 2) * Real.log ((1 + ζ) / (1 - ζ)) := by
  have hdpos : 0 < d := lt_of_lt_of_le two_pos hd
  have hm : (0:ℝ) < 1 - ζ := by linarith only [hζ₁]
  have hp : (0:ℝ) < 1 + ζ := by linarith only [hζ₀]
  have hu : (0:ℝ) < (1 + ζ) / (1 - ζ) := div_pos hp hm
  have hs : 0 < Real.sqrt ((1 + ζ) / (1 - ζ)) := Real.sqrt_pos.mpr hu
  have hSE : (fullBlockSharp E).PosDef := posDef_fullBlockSharp hE
  have hSF : (fullBlockSharp F).PosDef := posDef_fullBlockSharp hF
  -- sharp order reversal
  have hsharpUp : fullBlockSharp F ≤ (1 - ζ)⁻¹ • fullBlockSharp E := by
    have h := fullBlockSharp_le_fullBlockSharp (posDef_smul hE hm) hF hlow
    rwa [fullBlockSharp_smul hE hm] at h
  have hsharpLow : (1 + ζ)⁻¹ • fullBlockSharp E ≤ fullBlockSharp F := by
    have h := fullBlockSharp_le_fullBlockSharp hF (posDef_smul hE hp) hhigh
    rwa [fullBlockSharp_smul hE hp] at h
  -- monotonicity and homogeneity of the mean
  have hmeanUp : canonBlock F ≤ Real.sqrt ((1 + ζ) / (1 - ζ)) • canonBlock E := by
    have hmono := matGeomMean_mono hF (posDef_smul hE hp) hSF
      (posDef_smul hSE (inv_pos.mpr hm)) hhigh hsharpUp
    rw [matGeomMean_smul hE hSE hp (inv_pos.mpr hm), ← div_eq_mul_inv] at hmono
    exact hmono
  have hmeanLow : (Real.sqrt ((1 + ζ) / (1 - ζ)))⁻¹ • canonBlock E ≤ canonBlock F := by
    have hmono := matGeomMean_mono (posDef_smul hE hm) hF
      (posDef_smul hSE (inv_pos.mpr hp)) hSF hlow hsharpLow
    rw [matGeomMean_smul hE hSE hm (inv_pos.mpr hp), mul_inv_eq_inv_div hm hp,
      Real.sqrt_inv] at hmono
    exact hmono
  -- the two forms of the sandwich
  have hhigh' : canonBlock E ≤ Real.sqrt ((1 + ζ) / (1 - ζ)) • canonBlock F :=
    le_smul_of_smul_inv_le hs hmeanLow
  have hlow' : (Real.sqrt ((1 + ζ) / (1 - ζ)))⁻¹ • canonBlock F ≤ canonBlock E :=
    smul_inv_le_of_le_smul hs hmeanUp
  refine ⟨?_, projDist_canonMetric_le hdpos hE hF hu hlow' hhigh'⟩
  -- the imbalance chain
  have hc₁ : (0:ℝ) ≤ (1 + ζ) * Real.sqrt (canonImbalance E) :=
    mul_nonneg hp.le (Real.sqrt_nonneg _)
  have hc₂ : (0:ℝ) ≤ (1 + ζ) * Real.sqrt (canonImbalance E) *
      Real.sqrt ((1 + ζ) / (1 - ζ)) := mul_nonneg hc₁ (Real.sqrt_nonneg _)
  have hchain : F ≤ ((1 + ζ) * Real.sqrt (canonImbalance E) *
      Real.sqrt ((1 + ζ) / (1 - ζ))) • canonBlock F := by
    calc F ≤ (1 + ζ) • E := hhigh
      _ ≤ (1 + ζ) • (Real.sqrt (canonImbalance E) • canonBlock E) :=
          smul_le_smul_of_le hp.le (le_sqrt_canonImbalance_smul hE)
      _ = ((1 + ζ) * Real.sqrt (canonImbalance E)) • canonBlock E := smul_smul _ _ _
      _ ≤ ((1 + ζ) * Real.sqrt (canonImbalance E)) •
            (Real.sqrt ((1 + ζ) / (1 - ζ)) • canonBlock F) :=
          smul_le_smul_of_le hc₁ hhigh'
      _ = ((1 + ζ) * Real.sqrt (canonImbalance E) *
            Real.sqrt ((1 + ζ) / (1 - ζ))) • canonBlock F := smul_smul _ _ _
  have hsq := canonImbalance_le_sq hF hc₂ hchain
  rwa [sq_mul_sqrt_mul_sqrt (canonImbalance_nonneg E) hu.le, contrast_cube hm] at hsq

end

end HighContrast
end Homogenization
