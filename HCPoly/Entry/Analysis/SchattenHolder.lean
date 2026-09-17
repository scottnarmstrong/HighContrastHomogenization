import HCPoly.Entry.Analysis.SchattenHolderLossy
import HCPoly.Entry.Analysis.SingularValueTensor
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Trace Holder for Schatten norms

This file removes the word-length constant in the lossy trace Holder bound by
applying it to tensor powers and using Archimedean growth of powers.
-/

namespace Homogenization.HighContrast.Analysis

open scoped BigOperators

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem le_of_all_pow_le_mul_pow {a b c : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (_hc : 1 ≤ c) (h : ∀ q : ℕ, a^q ≤ c*b^q) : a ≤ b := by
  by_contra hab
  have hba : b < a := not_le.mp hab
  by_cases hb0 : b = 0
  · subst b
    have h1 := h 1
    have ha0 : a ≤ 0 := by simpa using h1
    exact (not_lt_of_ge ha0) hba
  · have hbpos : 0 < b := lt_of_le_of_ne' hb hb0
    have hratio : 1 < a / b := (one_lt_div hbpos).mpr hba
    obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt c hratio
    have hbqpos : 0 < b^q := pow_pos hbpos q
    have hlt : c*b^q < a^q := by
      have hmul := mul_lt_mul_of_pos_right hq hbqpos
      have hdiv : (a / b)^q * b^q = a^q := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero q hbpos.ne')]
      simpa [hdiv] using hmul
    exact (not_lt_of_ge (h q)) hlt

theorem trace_prod_pow_le_card_mul_prod_singularNorm_pow {N : ℕ} (hN : 0 < N)
    (A : Fin N → Matrix n n ℝ) (q : ℕ) :
    |Matrix.trace ((List.ofFn A).prod)|^q ≤
      (N:ℝ) * (∏ k, singularNorm (N:ℝ) (A k))^q := by
  have h :=
    abs_trace_prod_le_card_mul_prod_singularNorm (n := Fin q → n) hN
      (fun k => tensorPower (A k) q)
  rw [← tensorPower_prod, trace_tensorPower, abs_pow] at h
  simpa only [singularNorm_tensorPower _ (Nat.cast_pos.mpr hN), Finset.prod_pow] using h

theorem abs_trace_prod_le_prod_singularNorm {N : ℕ} (hN : 0 < N)
    (A : Fin N → Matrix n n ℝ) :
    |Matrix.trace ((List.ofFn A).prod)| ≤ ∏ k, singularNorm (N:ℝ) (A k) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hN
  exact le_of_all_pow_le_mul_pow (abs_nonneg _)
    (Finset.prod_nonneg fun k _ => singularNorm_nonneg (N:ℝ) (A k))
    hNreal
    (trace_prod_pow_le_card_mul_prod_singularNorm_pow hN A)

theorem abs_trace_prod_le_prod_absSchattenNorm {d N : ℕ} (hN : 2 ≤ N)
    (A : Fin N → BlockMat d)
    (hA : ∀ k, (toFullBlockMat (A k)).IsHermitian) :
    |Matrix.trace ((List.ofFn fun k => toFullBlockMat (A k)).prod)| ≤
      ∏ k : Fin N, absSchattenNorm (N:ℝ) (A k) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (by decide : 1 ≤ 2) hN
  calc
    |Matrix.trace ((List.ofFn fun k => toFullBlockMat (A k)).prod)|
        ≤ ∏ k, singularNorm (N:ℝ) (toFullBlockMat (A k)) :=
          abs_trace_prod_le_prod_singularNorm hNpos (fun k => toFullBlockMat (A k))
    _ = ∏ k : Fin N, absSchattenNorm (N:ℝ) (A k) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          exact singularNorm_eq_absSchattenNorm (hA k) hNreal

end

end Homogenization.HighContrast.Analysis
