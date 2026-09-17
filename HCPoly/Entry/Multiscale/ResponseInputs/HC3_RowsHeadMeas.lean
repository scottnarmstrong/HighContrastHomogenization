import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsBlockPSD
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsBlockIntegral

/-!
# The side conditions of the two-term head on the carriers

The cell half of the cutoff-mean row of `p.response.transfer` carries, for each coarse cell, the
two-term head `√(P · b P) + √(Q · (S_*)^{-1} Q)` built from the two diagonal blocks of that cell's
pathwise coarse block.  This module discharges the side conditions the head needs on the carriers:
the nonnegativity of its two quadratic forms, their integrability from the entrywise integrability
of the coarse block, and the integrability of the cross term and of the square of the head.  The
last two are consequences of the arithmetic--geometric mean inequality and the nonnegativity of the
two summands: `√α √β ≤ (α + β)/2` and `(√α + √β)^2 ≤ 2(α + β)`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Nonnegativity of the two diagonal coarse-block forms -/

/-! ## Integrability of the two diagonal coarse-block forms -/

/-- **The upper-left diagonal coarse-block form is integrable from its entries.**  If every entry
of the upper-left block of `𝐀(V; b a)` is `P`-integrable, then so is the quadratic form
`Y.1 · (𝐀(V; b a).upperLeft Y.1)`: it is a finite sum of products of entries with the constants
`Y.1 i`, `Y.1 j`.  This is the upper-left integrability input of the two-term head of
`p.response.transfer`. -/
theorem integrable_vecDot_coarseBlockMatrix_upperLeft {d : ℕ} {P : Measure (CoeffSpace d)}
    {V : Set (Vec d)} {b : CoeffSpace d → CoeffField d} (Y : BlockVec d)
    (hint : ∀ i j : Fin d,
      Integrable (fun a => (coarseBlockMatrix V (b a)).upperLeft i j) P) :
    Integrable (fun a =>
      vecDot Y.1 (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y.1)) P := by
  have hterm : ∀ i j : Fin d, Integrable (fun a =>
      Y.1 i * ((coarseBlockMatrix V (b a)).upperLeft i j * Y.1 j)) P :=
    fun i j => ((hint i j).mul_const (Y.1 j)).const_mul (Y.1 i)
  have hsum : Integrable (fun a => ∑ i : Fin d, ∑ j : Fin d,
      Y.1 i * ((coarseBlockMatrix V (b a)).upperLeft i j * Y.1 j)) P :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hterm i j
  refine hsum.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [vecDot, matVecMul, Finset.mul_sum]

/-- **The lower-right diagonal coarse-block form is integrable from its entries.**  The
lower-right twin of `integrable_vecDot_coarseBlockMatrix_upperLeft`: entrywise integrability of
the lower-right block makes the form `Y.2 · (𝐀(V; b a).lowerRight Y.2)` `P`-integrable, the second
integrability input of the two-term head of `p.response.transfer`. -/
theorem integrable_vecDot_coarseBlockMatrix_lowerRight {d : ℕ} {P : Measure (CoeffSpace d)}
    {V : Set (Vec d)} {b : CoeffSpace d → CoeffField d} (Y : BlockVec d)
    (hint : ∀ i j : Fin d,
      Integrable (fun a => (coarseBlockMatrix V (b a)).lowerRight i j) P) :
    Integrable (fun a =>
      vecDot Y.2 (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y.2)) P := by
  have hterm : ∀ i j : Fin d, Integrable (fun a =>
      Y.2 i * ((coarseBlockMatrix V (b a)).lowerRight i j * Y.2 j)) P :=
    fun i j => ((hint i j).mul_const (Y.2 j)).const_mul (Y.2 i)
  have hsum : Integrable (fun a => ∑ i : Fin d, ∑ j : Fin d,
      Y.2 i * ((coarseBlockMatrix V (b a)).lowerRight i j * Y.2 j)) P :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => hterm i j
  refine hsum.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [vecDot, matVecMul, Finset.mul_sum]

/-! ## Integrability of the cross term and of the square of the head -/

/-- The arithmetic--geometric mean inequality for two square roots. -/
private theorem two_mul_sqrt_mul_sqrt_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt x * Real.sqrt y ≤ x + y := by
  have hsq : 0 ≤ (Real.sqrt x - Real.sqrt y) ^ 2 := sq_nonneg _
  rw [sub_sq, Real.sq_sqrt hx, Real.sq_sqrt hy] at hsq
  linarith

/-- **Integrability of the square of the head `(√α + √β)^2` for nonnegative integrable `α`, `β`.**
From `√α √β ≤ (α + β)/2` one gets `(√α + √β)^2 ≤ 2(α + β)`, an integrable domination, with
measurability supplied by continuity of `Real.sqrt`.  This is the squared-head integrability of
the two-term head of `p.response.transfer`. -/
theorem integrable_sq_sqrt_add_sqrt {d : ℕ} {P : Measure (CoeffSpace d)}
    {α β : CoeffSpace d → ℝ} (hα : Integrable α P) (hβ : Integrable β P)
    (hαnn : ∀ a, 0 ≤ α a) (hβnn : ∀ a, 0 ≤ β a) :
    Integrable (fun a => (Real.sqrt (α a) + Real.sqrt (β a)) ^ 2) P := by
  have hsqrtα : AEStronglyMeasurable (fun a => Real.sqrt (α a)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hα.aestronglyMeasurable
  have hsqrtβ : AEStronglyMeasurable (fun a => Real.sqrt (β a)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hβ.aestronglyMeasurable
  refine Integrable.mono' ((hα.add hβ).const_mul 2) ((hsqrtα.add hsqrtβ).pow 2) ?_
  filter_upwards with a
  simp only [Pi.add_apply]
  have hnn : 0 ≤ (Real.sqrt (α a) + Real.sqrt (β a)) ^ 2 := sq_nonneg _
  rw [Real.norm_of_nonneg hnn]
  have h2 := two_mul_sqrt_mul_sqrt_le (hαnn a) (hβnn a)
  have hexp : (Real.sqrt (α a) + Real.sqrt (β a)) ^ 2
      = α a + β a + 2 * (Real.sqrt (α a) * Real.sqrt (β a)) := by
    rw [add_sq, Real.sq_sqrt (hαnn a), Real.sq_sqrt (hβnn a)]
    ring
  rw [hexp]
  linarith

/-- **Integrability of the square of the two-term head on the carriers.**  The square of the head
`√(Y.1 · 𝐀(V; b a).upperLeft Y.1) + √(Y.2 · 𝐀(V; b a).lowerRight Y.2)` is `P`-integrable
whenever its two diagonal coarse-block forms are nonnegative and integrable.  This is the
squared-head side condition of `p.response.transfer`. -/
theorem integrable_sq_sqrt_add_sqrt_coarseBlockMatrix {d : ℕ} {P : Measure (CoeffSpace d)}
    {V : Set (Vec d)} {b : CoeffSpace d → CoeffField d} (Y : BlockVec d)
    (hUL : Integrable (fun a =>
      vecDot Y.1 (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y.1)) P)
    (hLR : Integrable (fun a =>
      vecDot Y.2 (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y.2)) P)
    (hULnn : ∀ a, 0 ≤
      vecDot Y.1 (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y.1))
    (hLRnn : ∀ a, 0 ≤
      vecDot Y.2 (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y.2)) :
    Integrable (fun a =>
      (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y.1))
        + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y.2))) ^ 2) P :=
  integrable_sq_sqrt_add_sqrt hUL hLR hULnn hLRnn

end

end Homogenization.HighContrast.Multiscale
