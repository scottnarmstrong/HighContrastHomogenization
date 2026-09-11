/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.DriftAccount
import HCPoly.Provider.ShortHop.Normalization

/-!
# The fixed-grid determinant drift

`e.fixed.geometry.drift.advance` propagates the weighted determinant
drift `D_{q,j_*}` from an intermediate scale to a later one: the old part of the
sum is discounted by the geometric weight and inflated by the determinant loss,
and the new part costs at most `2d` times the excess of that loss over one.

The proof is the printed one and needs no square root.  Write `E_j` for the
annealed blocks, `G_j = E_{j-1} - E_j` for the increments of the mean order and
`r^d = det(E_u)/det(E_v)` for the loss.  The Loewner sandwich produced by a
determinant loss turns the mean order `E_v ≼ E_u` into
`E_u ≼ r^dE_v`, and inversion turns that into `E_v^{-1} ≼ r^dE_u^{-1}`.  Since
the trace against a positive semidefinite matrix is monotone, the terms with
`j ≤ u` are then bounded by `r^d3^{-ρ_dr(v-u)}` times the corresponding terms of
`D_{q,j_*}(u)`, the geometric weights factoring exactly.  For the terms with
`j > u` the weights are discarded — each is at most one and each trace is
nonnegative — and the increments telescope to `E_u - E_v`, whose trace against
`E_v^{-1}` is `tr(E_v^{-1}E_u) - 2d`; the comparison `E_u ≼ r^dE_v` bounds the
first summand by `2dr^d`.  The printed appeal to `E_v^{-1/2}E_uE_v^{-1/2} ≼ r^dI`
is exactly this last step, read without the square root.

The two degenerate cases the reference text lists are automatic here: at `u = v`
the loss is one and the second sum is empty, and at `u = j_*` the first sum is
empty.

The lemma is proved for an arbitrary family of doubled blocks indexed by the
scale, since nothing about the annealed means is used beyond positivity and the
mean order, and is then read at the annealed means.  The two readings the short
test needs — at the intermediate scale and at the terminal scale — close the
last two hypotheses of `shortHop_conclusion`.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## Telescoping over an integer interval -/

/-- A backward difference telescopes over `Finset.Icc (u+1) v`. -/
private theorem sum_Icc_sub_pred {M : Type*} [AddCommGroup M] (f : ℤ → M) {u v : ℤ}
    (huv : u ≤ v) : ∑ j ∈ Finset.Icc (u + 1) v, (f (j - 1) - f j) = f u - f v := by
  induction v, huv using Int.le_induction with
  | base =>
    have hempty : Finset.Icc (u + 1) u = (∅ : Finset ℤ) := by
      ext x
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and, not_le]
      omega
    rw [hempty, Finset.sum_empty, sub_self]
  | succ w hw ih =>
    have hins : Finset.Icc (u + 1) (w + 1) = insert (w + 1) (Finset.Icc (u + 1) w) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (w + 1) ∉ Finset.Icc (u + 1) w := by
      simp only [Finset.mem_Icc, not_and, not_le]
      omega
    rw [hins, Finset.sum_insert hnot, ih, add_sub_cancel_right]
    abel

/-! ## The number of doubled coordinates -/

/-- The doubled block coordinates number `2d`. -/
private theorem natCast_card_blockCoord (d : ℕ) :
    (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
  simp only [BlockCoord, Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
  ring

/-! ## The drift propagation for an arbitrary family of doubled blocks -/

/-- **The fixed-grid determinant drift, in the abstract.**  For a family of
positive definite doubled blocks satisfying the mean order, the weighted drift at
`v` is bounded by the discounted and inflated drift at `u` plus `2d` times the
excess of the determinant loss over one. -/
theorem weighted_drift_propagation {E : ℤ → FullBlockMat d} {rhoDr : ℝ} (hrho : 0 ≤ rhoDr)
    {jStar u v : ℤ} (hju : jStar ≤ u) (huv : u ≤ v)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ v → (E j).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ v → E t ≤ E s) :
    ∑ j ∈ Finset.Icc (jStar + 1) v,
        (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (j : ℝ))) *
          Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j)) ≤
      (E u).det / (E v).det * (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) *
          (∑ j ∈ Finset.Icc (jStar + 1) u,
            (3 : ℝ) ^ (-rhoDr * ((u : ℝ) - (j : ℝ))) *
              Matrix.trace ((E u)⁻¹ * (E (j - 1) - E j))) +
        2 * (d : ℝ) * ((E u).det / (E v).det - 1) := by
  have hEu : (E u).PosDef := hpos u hju huv
  have hEv : (E v).PosDef := hpos v (hju.trans huv) le_rfl
  have hvu : E v ≤ E u := hmono u v hju huv le_rfl
  have hrd : (0 : ℝ) < (E u).det / (E v).det := div_pos hEu.det_pos hEv.det_pos
  -- the two comparisons of the change of normalization under a determinant loss
  have hupper : E u ≤ ((E u).det / (E v).det) • E v := le_det_div_smul hEu hEv hvu
  have hinv : (E v)⁻¹ ≤ ((E u).det / (E v).det) • (E u)⁻¹ := by
    refine le_smul_of_smul_inv_le hrd ?_
    have h := inv_le_inv_of_le hEu (posDef_smul hEv hrd) hupper
    rwa [inv_smul_of_isUnit hrd.ne' (isUnit_det_of_posDef hEv)] at h
  -- every increment of the mean order is positive semidefinite
  have hG : ∀ j : ℤ, jStar + 1 ≤ j → j ≤ v → (E (j - 1) - E j).PosSemidef := fun j hj1 hjv =>
    Matrix.le_iff.mp (hmono (j - 1) j (by omega) (by omega) hjv)
  -- the split of the index range at the intermediate scale
  have hsplit : Finset.Icc (jStar + 1) v =
      Finset.Icc (jStar + 1) u ∪ Finset.Icc (u + 1) v := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc (jStar + 1) u) (Finset.Icc (u + 1) v) := by
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    simp only [Finset.mem_Icc] at hx hy
    omega
  -- the old part of the drift
  have hearly : ∑ j ∈ Finset.Icc (jStar + 1) u,
        (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (j : ℝ))) *
          Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j)) ≤
      (E u).det / (E v).det * (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) *
        (∑ j ∈ Finset.Icc (jStar + 1) u,
          (3 : ℝ) ^ (-rhoDr * ((u : ℝ) - (j : ℝ))) *
            Matrix.trace ((E u)⁻¹ * (E (j - 1) - E j))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hGj := hG j hj.1 (hj.2.trans huv)
    have htr : Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j)) ≤
        (E u).det / (E v).det * Matrix.trace ((E u)⁻¹ * (E (j - 1) - E j)) := by
      have hstep := PortableHistory.trace_mul_le_trace_mul hGj hinv
      rw [Matrix.trace_mul_comm (E (j - 1) - E j) ((E v)⁻¹),
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        Matrix.trace_mul_comm (E (j - 1) - E j) ((E u)⁻¹)] at hstep
      exact hstep
    have hweight : (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (j : ℝ))) =
        (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) *
          (3 : ℝ) ^ (-rhoDr * ((u : ℝ) - (j : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring_nf
    have hw1 : (0 : ℝ) < (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) := by positivity
    have hw2 : (0 : ℝ) < (3 : ℝ) ^ (-rhoDr * ((u : ℝ) - (j : ℝ))) := by positivity
    rw [hweight]
    have hmul := mul_le_mul_of_nonneg_left htr (mul_pos hw1 hw2).le
    calc (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) *
            (3 : ℝ) ^ (-rhoDr * ((u : ℝ) - (j : ℝ))) *
            Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j))
        ≤ (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) *
            (3 : ℝ) ^ (-rhoDr * ((u : ℝ) - (j : ℝ))) *
            ((E u).det / (E v).det * Matrix.trace ((E u)⁻¹ * (E (j - 1) - E j))) := by
          linarith only [hmul]
      _ = (E u).det / (E v).det * (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) *
            ((3 : ℝ) ^ (-rhoDr * ((u : ℝ) - (j : ℝ))) *
              Matrix.trace ((E u)⁻¹ * (E (j - 1) - E j))) := by ring
  -- the new part of the drift
  have hlate : ∑ j ∈ Finset.Icc (u + 1) v,
        (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (j : ℝ))) *
          Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j)) ≤
      2 * (d : ℝ) * ((E u).det / (E v).det - 1) := by
    -- discard the weights
    have hdrop : ∑ j ∈ Finset.Icc (u + 1) v,
          (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (j : ℝ))) *
            Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j)) ≤
        ∑ j ∈ Finset.Icc (u + 1) v, Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mem_Icc] at hj
      have hGj := hG j (by omega) hj.2
      have htr0 : 0 ≤ Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j)) :=
        PortableHistory.trace_mul_nonneg hEv.inv.posSemidef hGj
      have hprod : 0 ≤ rhoDr * ((v : ℝ) - (j : ℝ)) := by
        refine mul_nonneg hrho ?_
        have : (j : ℝ) ≤ (v : ℝ) := by exact_mod_cast hj.2
        linarith only [this]
      have hle1 : (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (j : ℝ))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith only [hprod])
      have := mul_le_mul_of_nonneg_right hle1 htr0
      linarith only [this]
    -- telescope
    have htel : ∑ j ∈ Finset.Icc (u + 1) v, Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j)) =
        Matrix.trace ((E v)⁻¹ * (E u - E v)) := by
      rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_Icc_sub_pred E huv]
    -- the trace of the telescoped increment
    have hEvinv : (E v)⁻¹ * E v = 1 :=
      Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hEv)
    have hone : Matrix.trace ((E v)⁻¹ * E v) = 2 * (d : ℝ) := by
      rw [hEvinv, Matrix.trace_one, natCast_card_blockCoord]
    have hsplit2 : Matrix.trace ((E v)⁻¹ * (E u - E v)) =
        Matrix.trace ((E v)⁻¹ * E u) - 2 * (d : ℝ) := by
      rw [Matrix.mul_sub, Matrix.trace_sub, hone]
    have hbound : Matrix.trace ((E v)⁻¹ * E u) ≤ (E u).det / (E v).det * (2 * (d : ℝ)) := by
      have hstep := PortableHistory.trace_mul_le_trace_mul hEv.inv.posSemidef hupper
      rwa [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hone] at hstep
    rw [htel, hsplit2] at hdrop
    calc ∑ j ∈ Finset.Icc (u + 1) v,
            (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (j : ℝ))) *
              Matrix.trace ((E v)⁻¹ * (E (j - 1) - E j))
        ≤ Matrix.trace ((E v)⁻¹ * E u) - 2 * (d : ℝ) := hdrop
      _ ≤ 2 * (d : ℝ) * ((E u).det / (E v).det - 1) := by linarith only [hbound]
  rw [hsplit, Finset.sum_union hdisj]
  linarith only [hearly, hlate]

/-! ## The drift propagation at the annealed means -/

/-- **The fixed-grid determinant drift** (`e.fixed.geometry.drift.advance`),
with the determinant quotient in place of `e^{dσ_q(u,v)}`. -/
theorem linearDrift_propagation {P : Measure (CoeffSpace d)} {rhoDr : ℝ} (hrho : 0 ≤ rhoDr)
    {q : Mat d} {jStar u v : ℤ} (hju : jStar ≤ u) (huv : u ≤ v)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ v → (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ v →
      toFullBlockMat (adaptedMean P q t) ≤ toFullBlockMat (adaptedMean P q s)) :
    linearDrift P rhoDr q jStar v ≤
      (toFullBlockMat (adaptedMean P q u)).det / (toFullBlockMat (adaptedMean P q v)).det *
          (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) * linearDrift P rhoDr q jStar u +
        2 * (d : ℝ) *
          ((toFullBlockMat (adaptedMean P q u)).det /
            (toFullBlockMat (adaptedMean P q v)).det - 1) := by
  have hrewrite : ∀ T : ℤ, linearDrift P rhoDr q jStar T =
      ∑ j ∈ Finset.Icc (jStar + 1) T,
        (3 : ℝ) ^ (-rhoDr * ((T : ℝ) - (j : ℝ))) *
          Matrix.trace ((toFullBlockMat (adaptedMean P q T))⁻¹ *
            (toFullBlockMat (adaptedMean P q (j - 1)) -
              toFullBlockMat (adaptedMean P q j))) := by
    intro T
    simp only [linearDrift, blockTrace, toFullBlockMat_ofFullBlockMat,
      Recurrence.toFullBlockMat_blockSub]
  rw [hrewrite u, hrewrite v]
  exact weighted_drift_propagation (E := fun j => toFullBlockMat (adaptedMean P q j))
    hrho hju huv hpos hmono

/-! ## The printed form of the loss -/

/-- The exponentiated determinant loss is the quotient of the determinants. -/
theorem exp_detLoss_eq_det_div (hd : d ≠ 0) {P : Measure (CoeffSpace d)} {q : Mat d}
    {u v : ℤ} (hu : (toFullBlockMat (adaptedMean P q u)).PosDef)
    (hv : (toFullBlockMat (adaptedMean P q v)).PosDef) :
    Real.exp ((d : ℝ) * detLoss P q u v) =
      (toFullBlockMat (adaptedMean P q u)).det /
        (toFullBlockMat (adaptedMean P q v)).det := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hlogu : Real.log (adaptedDetRoot P q u) =
      (d : ℝ)⁻¹ * Real.log (toFullBlockMat (adaptedMean P q u)).det := by
    rw [adaptedDetRoot, detRoot, Real.log_rpow hu.det_pos, mul_comm]
  have hlogv : Real.log (adaptedDetRoot P q v) =
      (d : ℝ)⁻¹ * Real.log (toFullBlockMat (adaptedMean P q v)).det := by
    rw [adaptedDetRoot, detRoot, Real.log_rpow hv.det_pos, mul_comm]
  have hprod : (d : ℝ) * detLoss P q u v =
      Real.log (toFullBlockMat (adaptedMean P q u)).det -
        Real.log (toFullBlockMat (adaptedMean P q v)).det := by
    rw [detLoss, hlogu, hlogv, mul_sub, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ hdR, one_mul, one_mul]
  rw [hprod, ← Real.log_div hu.det_pos.ne' hv.det_pos.ne',
    Real.exp_log (div_pos hu.det_pos hv.det_pos)]

/-- **The fixed-grid determinant drift in the printed form**
(`e.fixed.geometry.drift.advance`). -/
theorem linearDrift_propagation_exp (hd : d ≠ 0) {P : Measure (CoeffSpace d)} {rhoDr : ℝ}
    (hrho : 0 ≤ rhoDr) {q : Mat d} {jStar u v : ℤ} (hju : jStar ≤ u) (huv : u ≤ v)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ v → (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ v →
      toFullBlockMat (adaptedMean P q t) ≤ toFullBlockMat (adaptedMean P q s)) :
    linearDrift P rhoDr q jStar v ≤
      Real.exp ((d : ℝ) * detLoss P q u v) * (3 : ℝ) ^ (-rhoDr * ((v : ℝ) - (u : ℝ))) *
          linearDrift P rhoDr q jStar u +
        2 * (d : ℝ) * (Real.exp ((d : ℝ) * detLoss P q u v) - 1) := by
  rw [exp_detLoss_eq_det_div hd (hpos u hju huv) (hpos v (hju.trans huv) le_rfl)]
  exact linearDrift_propagation hrho hju huv hpos hmono

end

end ShortHop
end HighContrast
end Homogenization
