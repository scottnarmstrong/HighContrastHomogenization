import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm

/-!
# HC bridge III: the scale-weighted summation of the seminorm (AK.HC (2.130))

The scale-average seminorm of AK.HC (2.130) is a series of per-scale averages.  The preceding
bridge `HC2_WeakSeminorm` bounds it against the constant per-scale majorant `cellMeanSq`.  Here the
per-scale majorant is allowed to grow geometrically, `A * 3 ^ (ρ * n)` with `ρ < 1`, which is the
shape produced by the multiscale coarse-block envelope.  The chain is the same three steps: a
termwise bound against the scale majorant, summability by comparison with a geometric series, and
the resulting bound on `besovSeminorm`.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

variable {d : ℕ}

/-- Termwise bound for the scale-average seminorm against a geometrically growing per-scale
majorant.  If the squared average at depth `n` is at most `A * 3 ^ (ρ * n)` with `ρ < 1`, then the
weighted `n`-th summand of the seminorm of AK.HC (2.130) is at most
`3 ^ (t / 2) * sqrt A * (3 ^ ((ρ - 1) / 2)) ^ n`, i.e. the scale weight and the growing majorant
combine into the geometric ratio `3 ^ ((ρ - 1) / 2) < 1`. -/
theorem besov_term_le_of_scale_bound {d : ℕ} (t : ℤ) (ρ A : ℝ)
    (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (hA : 0 ≤ A)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (h : ∀ n : ℕ, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w) ≤
          A * (3 : ℝ) ^ (ρ * (n : ℝ)))
    (n : ℕ) :
    (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w))
      ≤ (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by
  have _ := hρ
  have _ := hρ0
  have hle := h n
  have hsqrt := Real.sqrt_le_sqrt hle
  have hbase : 0 ≤ (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hsqrt3 : Real.sqrt ((3 : ℝ) ^ (ρ * (n : ℝ))) =
      (3 : ℝ) ^ (ρ * (n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hpow : ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * (3 : ℝ) ^ (ρ * (n : ℝ) / 2) =
      ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-(1 / 2 : ℝ))) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_natCast ((3 : ℝ) ^ ((ρ - 1) / 2)) n,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hEq : (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
        Real.sqrt (A * (3 : ℝ) ^ (ρ * (n : ℝ))) =
      (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by
    rw [Real.sqrt_mul hA, hsqrt3, three_rpow_scale_split t n]
    calc ((3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n) *
          (Real.sqrt A * (3 : ℝ) ^ (ρ * (n : ℝ) / 2))
        = (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A *
            (((3 : ℝ) ^ (-(1 / 2 : ℝ))) ^ n * (3 : ℝ) ^ (ρ * (n : ℝ) / 2)) := by
          ring
      _ = (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A *
            ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by rw [hpow]
  exact (mul_le_mul_of_nonneg_left hsqrt hbase).trans (le_of_eq hEq)

/-- The series defining the scale-average seminorm of AK.HC (2.130) is summable when the squared
per-scale averages grow at most like `A * 3 ^ (ρ * n)` with `ρ < 1`, since each summand is then
dominated by a geometric multiple of `3 ^ ((ρ - 1) / 2) < 1`. -/
theorem summable_besov_of_scale_bound {d : ℕ} (t : ℤ) (ρ A : ℝ)
    (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (hA : 0 ≤ A)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (h : ∀ n : ℕ, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w) ≤
          A * (3 : ℝ) ^ (ρ * (n : ℝ))) :
    Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ ((ρ - 1) / 2) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hr1 : (3 : ℝ) ^ ((ρ - 1) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith only [hρ])
  refine Summable.of_nonneg_of_le (fun n => ?_)
    (fun n => besov_term_le_of_scale_bound t ρ A hρ hρ0 hA avg h n)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left
      ((3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A))
  exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.sqrt_nonneg _)

/-- The scale-average seminorm of AK.HC (2.130) is bounded by the geometric series of its
per-scale majorant: for a squared per-scale average at most `A * 3 ^ (ρ * n)` with `ρ < 1`,
`besovSeminorm t avg ≤ 3 ^ (t / 2) * sqrt A * (1 - 3 ^ ((ρ - 1) / 2))⁻¹`. -/
theorem besovSeminorm_le_of_scale_bound {d : ℕ} (t : ℤ) (ρ A : ℝ)
    (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (hA : 0 ≤ A)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (h : ∀ n : ℕ, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w) ≤
          A * (3 : ℝ) ^ (ρ * (n : ℝ))) :
    besovSeminorm t avg ≤
      (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * (1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹ := by
  have hr0 : 0 ≤ (3 : ℝ) ^ ((ρ - 1) / 2) :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hr1 : (3 : ℝ) ^ ((ρ - 1) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (by linarith only [hρ])
  have hsum := summable_besov_of_scale_bound t ρ A hρ hρ0 hA avg h
  have hmaj : Summable fun n : ℕ =>
      (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hb : besovSeminorm t avg ≤
      ∑' n : ℕ, (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n := by
    unfold besovSeminorm
    exact Summable.tsum_le_tsum
      (fun n => besov_term_le_of_scale_bound t ρ A hρ hρ0 hA avg h n) hsum hmaj
  have htsum : (∑' n : ℕ,
        (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * ((3 : ℝ) ^ ((ρ - 1) / 2)) ^ n) =
      (3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A * (1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rwa [htsum] at hb

/-- Squared form of the preceding bound.  For a squared per-scale average at most
`A * 3 ^ (ρ * n)` with `ρ < 1`,
`besovSeminorm t avg ^ 2 ≤ ((1 - 3 ^ ((ρ - 1) / 2))⁻¹) ^ 2 * (3 ^ t * A)`. -/
theorem besovSeminorm_sq_le_of_scale_bound {d : ℕ} (t : ℤ) (ρ A : ℝ)
    (hρ : ρ < 1) (hρ0 : 0 ≤ ρ) (hA : 0 ≤ A)
    (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (h : ∀ n : ℕ, (((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w) ≤
          A * (3 : ℝ) ^ (ρ * (n : ℝ))) :
    besovSeminorm t avg ^ 2 ≤
      ((1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹) ^ 2 * ((3 : ℝ) ^ (t : ℝ) * A) := by
  have hle := besovSeminorm_le_of_scale_bound t ρ A hρ hρ0 hA avg h
  have hb0 : 0 ≤ besovSeminorm t avg := by
    unfold besovSeminorm
    exact tsum_nonneg fun n =>
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hb0 hle 2
  have h3sq : ((3 : ℝ) ^ ((t : ℝ) / 2)) ^ (2 : ℕ) = (3 : ℝ) ^ (t : ℝ) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((t : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  calc besovSeminorm t avg ^ 2
      ≤ ((3 : ℝ) ^ ((t : ℝ) / 2) * Real.sqrt A *
          (1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹) ^ 2 := hsq
    _ = ((1 - (3 : ℝ) ^ ((ρ - 1) / 2))⁻¹) ^ 2 * ((3 : ℝ) ^ (t : ℝ) * A) := by
        rw [mul_pow, mul_pow, h3sq, Real.sq_sqrt hA]
        ring

end

end Homogenization.HighContrast.Multiscale
