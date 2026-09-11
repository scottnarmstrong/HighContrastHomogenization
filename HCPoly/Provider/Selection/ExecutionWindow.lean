/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.SelectionObjects

/-!
# Execution-window arithmetic for the selector

The coupled execution burn makes the execution interval a positive-height
coupled window and gives the additive upper bound on its lower endpoint.
-/

namespace Homogenization.HighContrast.Selection

private theorem zero_lt_logb_growthBar (K : ℝ) :
    0 < Real.logb 3 (growthBar K) := by
  have h2 : (2 : ℝ) ≤ growthBar K := le_max_left _ _
  have hmono : Real.logb 3 2 ≤ Real.logb 3 (growthBar K) :=
    Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2
  have hpos : 0 < Real.logb 3 2 :=
    Real.logb_pos (by norm_num) (by norm_num)
  linarith only [hmono, hpos]

private theorem zero_le_sourceBurn (d : ℕ) (Q K : ℝ) :
    (0 : ℤ) ≤ sourceBurn d Q K :=
  le_trans (Int.natCast_nonneg _) (le_max_left _ _)

/-- The execution window has positive height, is coupled, and its burn obeys
the additive bound used by the global selector. -/
theorem execution_window_facts (d : ℕ) (g K Cexec Lam : ℝ)
    (hCexec : 0 < Cexec) (hLam : 1 ≤ Lam) (jdag Mexec : ℤ)
    (hjdag : jdag = coupledExecBurn d (initExpQ d g : ℝ) K Cexec Lam)
    (hMexec : Mexec = jdag + ⌈Cexec * Lam⌉) :
    1 ≤ Mexec - jdag ∧
      IsCoupledWindow d (initExpQ d g : ℝ) K jdag Mexec ∧
      (jdag : ℝ) ≤ (sourceBurn d (initExpQ d g : ℝ) K : ℝ) + 1 +
        ((d : ℝ) * (1 + Cexec * Lam) +
            16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
          (4 * (d : ℝ) + 3) := by
  have hLam0 : (0 : ℝ) < Lam := lt_of_lt_of_le one_pos hLam
  have hCL : 0 < Cexec * Lam := mul_pos hCexec hLam0
  have hdenpos : (0 : ℝ) < 4 * (d : ℝ) + 3 := by positivity
  have hLpos : 0 ≤ 16 * ((d : ℝ) + 1) ^ 2 *
      Real.logb 3 (growthBar K) := by
    have := zero_lt_logb_growthBar K
    positivity
  have hNone : (1 : ℤ) ≤ ⌈Cexec * Lam⌉ := Int.one_le_ceil_iff.mpr hCL
  have hheight : 1 ≤ Mexec - jdag := by omega
  have hburn : jdag =
      max (sourceBurn d (initExpQ d g : ℝ) K)
        ⌈((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
            16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
          (4 * (d : ℝ) + 3)⌉ := hjdag
  have hceil_le :
      ((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3) ≤ (jdag : ℝ) := by
    refine le_trans (Int.le_ceil _) ?_
    have h2 : (⌈((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
        16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
          (4 * (d : ℝ) + 3)⌉ : ℤ) ≤ jdag := by
      rw [hburn]
      exact le_max_right _ _
    exact_mod_cast h2
  have hprod := (div_le_iff₀ hdenpos).mp hceil_le
  have hcoupled : IsCoupledWindow d (initExpQ d g : ℝ) K jdag Mexec := by
    refine ⟨by rw [hburn]; exact le_max_left _ _, by omega, ?_⟩
    have hsub : (Mexec : ℝ) - (jdag : ℝ) =
        ((⌈Cexec * Lam⌉ : ℤ) : ℝ) := by
      rw [hMexec]
      push_cast
      ring
    rw [hsub]
    linarith only [hprod]
  refine ⟨hheight, hcoupled, ?_⟩
  have hNle : ((⌈Cexec * Lam⌉ : ℤ) : ℝ) ≤ 1 + Cexec * Lam := by
    have := Int.ceil_lt_add_one (Cexec * Lam)
    linarith only [this]
  have hZ :
      ((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3) ≤
      ((d : ℝ) * (1 + Cexec * Lam) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3) := by
    gcongr
  have hZnn : (0 : ℝ) ≤
      ((d : ℝ) * (1 + Cexec * Lam) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3) := by
    have h1 : (0 : ℝ) ≤ (d : ℝ) * (1 + Cexec * Lam) := by positivity
    positivity
  have hAnn : (0 : ℝ) ≤
      ((sourceBurn d (initExpQ d g : ℝ) K : ℤ) : ℝ) := by
    exact_mod_cast zero_le_sourceBurn d (initExpQ d g : ℝ) K
  rw [hburn]
  rcases le_total (sourceBurn d (initExpQ d g : ℝ) K)
      ⌈((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3)⌉ with h | h
  · rw [max_eq_right h]
    have h1 := (Int.ceil_lt_add_one
      (((d : ℝ) * ((⌈Cexec * Lam⌉ : ℤ) : ℝ) +
          16 * ((d : ℝ) + 1) ^ 2 * Real.logb 3 (growthBar K)) /
        (4 * (d : ℝ) + 3))).le
    push_cast at h1 ⊢
    linarith only [h1, hZ, hAnn]
  · rw [max_eq_left h]
    linarith only [hZnn]

end Homogenization.HighContrast.Selection
