/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ComparisonScalarRows
import HCPoly.Provider.Recurrence.SchattenSpectral

/-!
# Matrix rows for two-grid comparison

Each positive increment is measured by its trace in the terminal geometry.
The scalar boundary-row estimate then lifts directly to a Loewner estimate for
the corresponding weighted row of adapted means.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem sum_Icc_sub_pred {M : Type*} [AddCommGroup M] (f : ℤ → M)
    {u v : ℤ} (huv : u ≤ v) :
    ∑ j ∈ Finset.Icc (u + 1) v, (f (j - 1) - f j) = f u - f v := by
  induction v, huv using Int.leInduction with
  | base =>
    have hempty : Finset.Icc (u + 1) u = (∅ : Finset ℤ) := by
      ext x
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and, not_le]
      omega
    rw [hempty, Finset.sum_empty, sub_self]
  | succ w hw ih =>
    have hins : Finset.Icc (u + 1) (w + 1) =
        insert (w + 1) (Finset.Icc (u + 1) w) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (w + 1) ∉ Finset.Icc (u + 1) w := by
      simp only [Finset.mem_Icc, not_and, not_le]
      omega
    rw [hins, Finset.sum_insert hnot, ih, add_sub_cancel_right]
    abel

/-- A positive semidefinite matrix is bounded by its trace in any positive
terminal geometry. -/
theorem posSemidef_le_trace_inv_smul {A G : FullBlockMat d}
    (hA : A.PosDef) (hG : G.PosSemidef) :
    G ≤ Matrix.trace (A⁻¹ * G) • A := by
  let S : FullBlockMat d := matSqrt A⁻¹
  have hnorm : (S * G * S).PosSemidef := posSemidef_normalize hG hA
  have htrace : Matrix.trace (S * G * S) = Matrix.trace (A⁻¹ * G) := by
    calc
      Matrix.trace (S * G * S) = Matrix.trace (S * (S * G)) :=
        Matrix.trace_mul_comm (S * G) S
      _ = Matrix.trace ((S * S) * G) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (A⁻¹ * G) := by rw [matSqrt_inv_mul_self hA]
  have hle := Recurrence.le_trace_smul_one hnorm
  rw [htrace] at hle
  exact (conj_normalize hA (Matrix.trace (A⁻¹ * G))).mpr hle

/-- An earlier positive mean is bounded by the terminal mean and the trace of
their positive difference in the terminal geometry. -/
theorem matrix_le_terminal_trace_sub {A B : FullBlockMat d}
    (hB : B.PosDef) (hBA : B ≤ A) :
    A ≤ (1 + Matrix.trace (B⁻¹ * (A - B))) • B := by
  have hG : (A - B).PosSemidef := Matrix.le_iff.mp hBA
  have htrace := posSemidef_le_trace_inv_smul hB hG
  refine Matrix.le_iff.mpr ?_
  have hps := Matrix.le_iff.mp htrace
  rw [add_smul, one_smul]
  have heq : B + Matrix.trace (B⁻¹ * (A - B)) • B - A =
      Matrix.trace (B⁻¹ * (A - B)) • B - (A - B) := by abel
  rw [heq]
  exact hps

/-- A weighted boundary row of decreasing positive means is controlled by the
terminal mean, the geometric boundary mass, and the terminal weighted drift. -/
theorem weighted_mean_row_le {rho D K mass : ℝ} {b T l : ℤ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hl : 0 ≤ l)
    (hbTl : b ≤ T - l) (hDK : 0 ≤ D * K)
    (F : ℤ → FullBlockMat d) (theta : ℤ → ℝ)
    (hpos : ∀ r ∈ Finset.Icc b T, (F r).PosDef)
    (hmono : ∀ r ∈ Finset.Icc (b + 1) T, F r ≤ F (r - 1))
    (hterminal : ∀ a ∈ Finset.Icc b (T - l), F T ≤ F a)
    (htheta0 : ∀ a ∈ Finset.Icc b (T - l), 0 ≤ theta a)
    (hmass : ∑ a ∈ Finset.Icc b (T - l), theta a ≤ mass)
    (hrow : ∀ a ∈ Finset.Icc b (T - l),
      theta a ≤ D * K * (3 : ℝ) ^ (a - T)) :
    ∑ a ∈ Finset.Icc b (T - l), theta a • F a ≤
      (mass + (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * K *
        (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
          ∑ r ∈ Finset.Icc (b + 1) T,
            (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) *
              Matrix.trace ((F T)⁻¹ * (F (r - 1) - F r))) • F T := by
  classical
  have hbT : b ≤ T := hbTl.trans (by omega)
  have hTpos : (F T).PosDef := hpos T (Finset.mem_Icc.mpr ⟨hbT, le_rfl⟩)
  let x : ℤ → ℝ := fun r => Matrix.trace ((F T)⁻¹ * (F (r - 1) - F r))
  have hx : ∀ r ∈ Finset.Icc (b + 1) T, 0 ≤ x r := by
    intro r hr
    have hG : (F (r - 1) - F r).PosSemidef := Matrix.le_iff.mp (hmono r hr)
    exact PortableHistory.trace_mul_nonneg hTpos.inv.posSemidef hG
  have hmean : ∀ a ∈ Finset.Icc b (T - l),
      F a ≤ (1 + ∑ r ∈ Finset.Icc (a + 1) T, x r) • F T := by
    intro a ha
    have haT : a ≤ T := (Finset.mem_Icc.mp ha).2.trans (by omega)
    have htrace : Matrix.trace ((F T)⁻¹ * (F a - F T)) =
        ∑ r ∈ Finset.Icc (a + 1) T, x r := by
      dsimp only [x]
      rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_Icc_sub_pred F haT]
    rw [← htrace]
    exact matrix_le_terminal_trace_sub hTpos (hterminal a ha)
  have hscaled : ∀ a ∈ Finset.Icc b (T - l),
      theta a • F a ≤ theta a •
        ((1 + ∑ r ∈ Finset.Icc (a + 1) T, x r) • F T) := fun a ha =>
    smul_le_smul_of_le (htheta0 a ha) (hmean a ha)
  have hmatrix := Finset.sum_le_sum hscaled
  have htail := weighted_tail_sum_le hrho0 hrho1 hDK theta x hrow hx
  have hcoef : ∑ a ∈ Finset.Icc b (T - l),
      theta a * (1 + ∑ r ∈ Finset.Icc (a + 1) T, x r) ≤
        mass + (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * K *
          (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
            ∑ r ∈ Finset.Icc (b + 1) T,
              (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) * x r := by
    have hsplit : ∑ a ∈ Finset.Icc b (T - l),
        theta a * (1 + ∑ r ∈ Finset.Icc (a + 1) T, x r) =
          (∑ a ∈ Finset.Icc b (T - l), theta a) +
            ∑ a ∈ Finset.Icc b (T - l), theta a *
              ∑ r ∈ Finset.Icc (a + 1) T, x r := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hsplit]
    exact add_le_add hmass htail
  calc
    ∑ a ∈ Finset.Icc b (T - l), theta a • F a ≤
        ∑ a ∈ Finset.Icc b (T - l), theta a •
          ((1 + ∑ r ∈ Finset.Icc (a + 1) T, x r) • F T) := hmatrix
    _ = (∑ a ∈ Finset.Icc b (T - l),
        theta a * (1 + ∑ r ∈ Finset.Icc (a + 1) T, x r)) • F T := by
      simp_rw [smul_smul]
      rw [Finset.sum_smul]
    _ ≤ (mass + (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * K *
        (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
          ∑ r ∈ Finset.Icc (b + 1) T,
            (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) * x r) • F T := by
      refine Matrix.le_iff.mpr ?_
      rw [← sub_smul]
      exact hTpos.posSemidef.smul (sub_nonneg.mpr hcoef)

end

end Bridge
end HighContrast
end Homogenization
