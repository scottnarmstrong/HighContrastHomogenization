/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRecentAverageLp
import HCPoly.Provider.PortableHistory.Checkpoint
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Summing the recent averaged-defect profile

The one-scale `L²` estimate is summed over the finite recent window.  The
self-scale gain vanishes, so the nonlinear coefficient starts at scale one.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- A nonterminal relative-mean gain is controlled by its summand in the
terminal nonlinear history after taking the `1/(2Q)`-th power. -/
theorem ofReal_frakH_halfRoot_le_nonlinearHistory_halfRoot [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {jStar t : ℤ} {H j : ℕ}
    {Q alpha : ℝ} (hQ : 1 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ)) (hj : j ∈ Finset.Icc 1 H) :
    ENNReal.ofReal
        (frakH Q (relMean P q (t - (j : ℤ)) t) ^ (1 / (2 * Q))) ≤
      ENNReal.ofReal
          ((3 : ℝ) ^ (alpha * ((j : ℝ) - 1) / (2 * Q))) *
        nonlinearHistory P Q alpha q jStar t ^ (1 / (2 * Q)) := by
  have hbase := ofReal_frakH_root_le_nonlinearHistory_root
    (a := alpha) hQ hP hgrid hlj hfin hstart hj
  have hjbounds := Finset.mem_Icc.mp hj
  have hjH : (j : ℤ) ≤ (H : ℤ) := by exact_mod_cast hjbounds.2
  have hklo : jStar ≤ t - (j : ℤ) :=
    hstart.trans (sub_le_sub_left hjH t)
  have hkhi : t - (j : ℤ) ≤ t := sub_le_self t (Int.natCast_nonneg j)
  have hfrak0 : 0 ≤ frakH Q (relMean P q (t - (j : ℤ)) t) :=
    PortableHistory.frakH_relMean_nonneg (by linarith only [hQ])
      hP hgrid hlj hfin hklo hkhi le_rfl
  have hhalf0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hpow := ENNReal.rpow_le_rpow hbase hhalf0
  rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf0] at hpow
  have hQne : Q ≠ 0 := by linarith only [hQ]
  have hexp : Q⁻¹ * (1 / 2 : ℝ) = 1 / (2 * Q) := by
    field_simp [hQne]
  let c : ℝ := (3 : ℝ) ^ (alpha * ((j : ℝ) - 1) / Q)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hleft :
      ENNReal.ofReal
          (frakH Q (relMean P q (t - (j : ℤ)) t) ^ Q⁻¹) ^
            (1 / 2 : ℝ) =
        ENNReal.ofReal
          (frakH Q (relMean P q (t - (j : ℤ)) t) ^ (1 / (2 * Q))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hfrak0 _) hhalf0]
    apply congrArg ENNReal.ofReal
    rw [← Real.rpow_mul hfrak0, hexp]
  have hcoeff : ENNReal.ofReal c ^ (1 / 2 : ℝ) =
      ENNReal.ofReal
        ((3 : ℝ) ^ (alpha * ((j : ℝ) - 1) / (2 * Q))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc0 hhalf0]
    apply congrArg ENNReal.ofReal
    dsimp only [c]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    field_simp [hQne]
  calc
    ENNReal.ofReal
        (frakH Q (relMean P q (t - (j : ℤ)) t) ^ (1 / (2 * Q))) =
        ENNReal.ofReal
          (frakH Q (relMean P q (t - (j : ℤ)) t) ^ Q⁻¹) ^
            (1 / 2 : ℝ) := hleft.symm
    _ ≤ ENNReal.ofReal c ^ (1 / 2 : ℝ) *
        (nonlinearHistory P Q alpha q jStar t ^ Q⁻¹) ^
          (1 / 2 : ℝ) := hpow
    _ = ENNReal.ofReal
          ((3 : ℝ) ^ (alpha * ((j : ℝ) - 1) / (2 * Q))) *
        nonlinearHistory P Q alpha q jStar t ^ (1 / (2 * Q)) := by
      rw [hcoeff, ← ENNReal.rpow_mul, hexp]

/-- The exact recent averaged-defect estimate in `L²`. -/
theorem eLpNorm_diagonalWeakAverageSum_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef) {jStar t : ℤ} {H : ℕ}
    {Q alpha s rho : ℝ} (hQ : 1 ≤ Q) (hexponent : s - rho / 2 = alpha)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ)) :
    eLpNorm
        (fun a ↦ diagonalWeakAverageSum q t H s rho
          (adaptedMean P q t) a) 2 P ≤
      ENNReal.ofReal (nonlinearAverageWindowCoefficient H alpha Q) *
        nonlinearHistory P Q alpha q jStar t ^ (1 / (2 * Q)) := by
  let F : ℕ → CoeffSpace d → ℝ := fun j a ↦ Real.sqrt
    (blockSize
      (diagonalWeakAverageDefect q (t - (j : ℤ)) t
        (adaptedMean P q t) a)
      (blockIdentity d))
  let w : ℕ → ℝ := fun j ↦ (3 : ℝ) ^ (-alpha * (j : ℝ))
  let c : ℕ → ℝ := fun j ↦
    (3 : ℝ) ^
      (-alpha * (j : ℝ) + alpha * ((j : ℝ) - 1) / (2 * Q))
  let N : ℝ≥0∞ :=
    nonlinearHistory P Q alpha q jStar t ^ (1 / (2 * Q))
  have hw0 : ∀ j, 0 ≤ w j := fun _ ↦ Real.rpow_nonneg (by norm_num) _
  have hc0 : ∀ j, 0 ≤ c j := fun _ ↦ Real.rpow_nonneg (by norm_num) _
  have htermMeas : ∀ j ∈ Finset.range (H + 1),
      AEStronglyMeasurable (fun a ↦ w j * F j a) P := by
    intro j hj
    have hjH : j ≤ H := by
      have := Finset.mem_range.mp hj
      omega
    have hklo : jStar ≤ t - (j : ℤ) := by
      have hjH' : (j : ℤ) ≤ (H : ℤ) := by exact_mod_cast hjH
      exact hstart.trans (sub_le_sub_left hjH' t)
    have hkhi : t - (j : ℤ) ≤ t := sub_le_self t (Int.natCast_nonneg j)
    have hlk : l ≤ t - (j : ℤ) := hlj.trans hklo
    exact ((aemeasurable_sqrt_diagonalWeakAverageDefect hq hP hgrid
      hlk hkhi (hfin _ hklo hkhi) (hfin _ (hklo.trans hkhi) le_rfl)).const_mul
        (w j)).aestronglyMeasurable
  have hterm : ∀ j ∈ Finset.range (H + 1),
      eLpNorm (fun a ↦ w j * F j a) 2 P ≤
        if j = 0 then 0 else ENNReal.ofReal (c j) * N := by
    intro j hj
    have hjH : j ≤ H := by
      have := Finset.mem_range.mp hj
      omega
    have hklo : jStar ≤ t - (j : ℤ) := by
      have hjH' : (j : ℤ) ≤ (H : ℤ) := by exact_mod_cast hjH
      exact hstart.trans (sub_le_sub_left hjH' t)
    have hkhi : t - (j : ℤ) ≤ t := sub_le_self t (Int.natCast_nonneg j)
    have hlk : l ≤ t - (j : ℤ) := hlj.trans hklo
    have hscale : eLpNorm (F j) 2 P ≤
        ENNReal.ofReal
          (frakH Q (relMean P q (t - (j : ℤ)) t) ^ (1 / (2 * Q))) := by
      simpa only [F] using
        eLpNorm_sqrt_diagonalWeakAverageDefect_le_frakH
          hq hP hgrid hlk hkhi hQ
            (hfin _ hklo hkhi) (hfin _ (hklo.trans hkhi) le_rfl)
    have hweighted : eLpNorm (fun a ↦ w j * F j a) 2 P ≤
        ENNReal.ofReal (w j) * eLpNorm (F j) 2 P := by
      apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      filter_upwards [] with a
      rw [norm_mul, Real.norm_of_nonneg (hw0 j)]
    by_cases hj0 : j = 0
    · subst j
      have hjt : jStar ≤ t :=
        hstart.trans (sub_le_self t (Int.natCast_nonneg H))
      have hself : frakH Q (relMean P q t t) = 0 :=
        PortableHistory.frakH_relMean_self Q hP hgrid hlj hfin hjt le_rfl
      have hrootne : (1 / (2 * Q) : ℝ) ≠ 0 := by
        have hQ0 : 0 < Q := by linarith only [hQ]
        positivity
      have hscale0 : eLpNorm (F 0) 2 P ≤ 0 := by
        simpa only [Int.natCast_zero, sub_zero, hself, Real.zero_rpow hrootne,
          ENNReal.ofReal_zero] using hscale
      simpa only [if_pos, mul_zero] using
        hweighted.trans (mul_right_mono hscale0)
    · have hjone : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hjIcc : j ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hjone, hjH⟩
      have hhistory := ofReal_frakH_halfRoot_le_nonlinearHistory_halfRoot
        (alpha := alpha) hQ hP hgrid hlj hfin hstart hjIcc
      calc
        eLpNorm (fun a ↦ w j * F j a) 2 P ≤
            ENNReal.ofReal (w j) * eLpNorm (F j) 2 P := hweighted
        _ ≤ ENNReal.ofReal (w j) * ENNReal.ofReal
            (frakH Q (relMean P q (t - (j : ℤ)) t) ^ (1 / (2 * Q))) :=
          mul_right_mono hscale
        _ ≤ ENNReal.ofReal (w j) *
            (ENNReal.ofReal
                ((3 : ℝ) ^ (alpha * ((j : ℝ) - 1) / (2 * Q))) * N) :=
          mul_right_mono (by simpa only [N] using hhistory)
        _ = ENNReal.ofReal (c j) * N := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (hw0 j)]
          congr 2
          dsimp only [w, c]
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        _ = if j = 0 then 0 else ENNReal.ofReal (c j) * N := by
          rw [if_neg hj0]
  have hrange : Finset.range (H + 1) = insert 0 (Finset.Icc 1 H) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hdrop :
      (∑ j ∈ Finset.range (H + 1),
        if j = 0 then 0 else ENNReal.ofReal (c j) * N) =
      ∑ j ∈ Finset.Icc 1 H, ENNReal.ofReal (c j) * N := by
    rw [hrange, Finset.sum_insert (by simp)]
    simp only [if_pos, zero_add]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [if_neg]
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hj).1
  have hcoefficient :
      (∑ j ∈ Finset.Icc 1 H, ENNReal.ofReal (c j) * N) =
        ENNReal.ofReal (nonlinearAverageWindowCoefficient H alpha Q) * N := by
    calc
      (∑ j ∈ Finset.Icc 1 H, ENNReal.ofReal (c j) * N) =
          (∑ j ∈ Finset.Icc 1 H, ENNReal.ofReal (c j)) * N := by
        rw [Finset.sum_mul]
      _ = ENNReal.ofReal (∑ j ∈ Finset.Icc 1 H, c j) * N := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hc0 j)]
      _ = ENNReal.ofReal (nonlinearAverageWindowCoefficient H alpha Q) * N := by
        congr 2
  change eLpNorm (fun a ↦ ∑ j ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-(s - rho / 2) * (j : ℝ)) * F j a) 2 P ≤
    ENNReal.ofReal (nonlinearAverageWindowCoefficient H alpha Q) * N
  have hfunction :
      (fun a ↦ ∑ j ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-(s - rho / 2) * (j : ℝ)) * F j a) =
      ∑ j ∈ Finset.range (H + 1), fun a ↦ w j * F j a := by
    funext a
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only [w]
    rw [hexponent]
  rw [hfunction]
  calc
    eLpNorm (∑ j ∈ Finset.range (H + 1), fun a ↦ w j * F j a) 2 P ≤
        ∑ j ∈ Finset.range (H + 1),
          eLpNorm (fun a ↦ w j * F j a) 2 P :=
      eLpNorm_sum_le htermMeas (by norm_num)
    _ ≤ ∑ j ∈ Finset.range (H + 1),
        if j = 0 then 0 else ENNReal.ofReal (c j) * N :=
      Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (nonlinearAverageWindowCoefficient H alpha Q) * N := by
      rw [hdrop, hcoefficient]

end

end Homogenization.HighContrast.Response
