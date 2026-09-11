/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CollectivePositiveGap

open MeasureTheory
open scoped ENNReal

namespace Homogenization
namespace HighContrast
namespace Transport

/-! Finite-family wrapper for the collective positive-gap absorption. -/

/-- A finite family satisfies the positive-gap estimate pathwise after one
shared absorption.  The trace charges are summed, while the centered
fluctuation is maximized and therefore paid only once. -/
theorem finite_family_collective_gap_pointwise {d : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) {Q C K B : ℝ}
    (hQ : 2 ≤ Q) (hC : 0 < C) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (wt : ι → ℝ) (hwt : ∀ i ∈ s, 0 < wt i)
    (cellF cellD cellY cellT : ι → CoeffSpace d → ℝ) (cellB : ι → ℝ)
    (hF0 : ∀ i ∈ s, ∀ a, 0 ≤ cellF i a)
    (hD0 : ∀ i ∈ s, ∀ a, 0 ≤ cellD i a)
    (hY0 : ∀ i ∈ s, ∀ a, 0 ≤ cellY i a)
    (hT0 : ∀ i ∈ s, ∀ a, 0 ≤ cellT i a)
    (hB0 : ∀ i ∈ s, 0 ≤ cellB i)
    (hcellQ : ∀ i ∈ s, ∀ a,
      cellD i a ^ Q ≤ C * cellT i a + C * (cellY i a ^ (Q - 1) * cellD i a))
    (hcellTri : ∀ i ∈ s, ∀ a,
      cellF i a ≤ K * (cellY i a + cellD i a + cellB i))
    (u v f tsum : CoeffSpace d → ℝ)
    (hu : ∀ a, u a = s.sup' hs (fun i => wt i * cellD i a))
    (hv : ∀ a, v a = s.sup' hs (fun i => wt i * cellY i a))
    (hf : ∀ a, f a = s.sup' hs (fun i => wt i * cellF i a))
    (ht : ∀ a, tsum a = ∑ i ∈ s, wt i ^ Q * cellT i a)
    (hBsum : ∑ i ∈ s, (wt i * cellB i) ^ Q ≤ B) :
    ∀ a, f a ^ Q ≤
      (K * (1 + (2 * C) ^ Q⁻¹ + (2 * C) ^ (Q - 1)⁻¹)) ^ Q *
        (2 : ℝ) ^ (Q - 1) * (v a ^ Q + (tsum a + B)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_two hQ
  have hQm : 0 ≤ Q - 1 := by linarith only [hQ]
  intro a
  have hu0 : 0 ≤ u a := by
    rw [hu a]
    obtain ⟨i, hi, hiEq⟩ := Finset.exists_mem_eq_sup' hs (fun i => wt i * cellD i a)
    rw [hiEq]
    exact mul_nonneg (hwt i hi).le (hD0 i hi a)
  have hv0 : 0 ≤ v a := by
    rw [hv a]
    obtain ⟨i, hi, hiEq⟩ := Finset.exists_mem_eq_sup' hs (fun i => wt i * cellY i a)
    rw [hiEq]
    exact mul_nonneg (hwt i hi).le (hY0 i hi a)
  have hf0 : 0 ≤ f a := by
    rw [hf a]
    obtain ⟨i, hi, hiEq⟩ := Finset.exists_mem_eq_sup' hs (fun i => wt i * cellF i a)
    rw [hiEq]
    exact mul_nonneg (hwt i hi).le (hF0 i hi a)
  have ht0 : 0 ≤ tsum a := by
    rw [ht a]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (Real.rpow_nonneg (hwt i hi).le Q) (hT0 i hi a)
  have hquad : u a ^ Q ≤ C * tsum a + C * (v a ^ (Q - 1) * u a) := by
    rw [hu a]
    obtain ⟨i, hi, hiEq⟩ := Finset.exists_mem_eq_sup' hs (fun i => wt i * cellD i a)
    rw [hiEq]
    have hwi := (hwt i hi).le
    have hdi := hD0 i hi a
    have hyi := hY0 i hi a
    have hmul := mul_le_mul_of_nonneg_left (hcellQ i hi a) (Real.rpow_nonneg hwi Q)
    have htmem : wt i ^ Q * cellT i a ≤ tsum a := by
      rw [ht a]
      exact Finset.single_le_sum (fun k hk =>
        mul_nonneg (Real.rpow_nonneg (hwt k hk).le Q) (hT0 k hk a)) hi
    have hyv : wt i * cellY i a ≤ v a := by
      rw [hv a]
      exact (Finset.le_sup'_iff hs).2 ⟨i, hi, le_rfl⟩
    have hypow : (wt i * cellY i a) ^ (Q - 1) ≤ v a ^ (Q - 1) :=
      Real.rpow_le_rpow (mul_nonneg hwi hyi) hyv hQm
    have hmix : wt i ^ Q * (cellY i a ^ (Q - 1) * cellD i a) =
        (wt i * cellY i a) ^ (Q - 1) * (wt i * cellD i a) := by
      have hwq : wt i ^ Q = wt i ^ (Q - 1) * wt i := by
        calc wt i ^ Q = wt i ^ ((Q - 1) + 1) := by congr 1; ring
          _ = wt i ^ (Q - 1) * wt i ^ (1 : ℝ) := Real.rpow_add (hwt i hi) _ _
          _ = wt i ^ (Q - 1) * wt i := by rw [Real.rpow_one]
      rw [Real.mul_rpow hwi hyi, hwq]
      ring
    have hpow : (wt i * cellD i a) ^ Q = wt i ^ Q * cellD i a ^ Q :=
      Real.mul_rpow hwi hdi
    rw [hpow]
    have hfirst := mul_le_mul_of_nonneg_left htmem hC.le
    have hsecond := mul_le_mul_of_nonneg_right hypow (mul_nonneg hwi hdi)
    calc wt i ^ Q * cellD i a ^ Q
        ≤ wt i ^ Q * (C * cellT i a +
            C * (cellY i a ^ (Q - 1) * cellD i a)) := hmul
      _ = C * (wt i ^ Q * cellT i a) +
            C * (wt i ^ Q * (cellY i a ^ (Q - 1) * cellD i a)) := by ring
      _ = C * (wt i ^ Q * cellT i a) +
            C * ((wt i * cellY i a) ^ (Q - 1) * (wt i * cellD i a)) := by rw [hmix]
      _ ≤ C * tsum a + C * (v a ^ (Q - 1) * (wt i * cellD i a)) :=
        add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond hC.le)
  have htri : f a ≤ K * (v a + u a + B ^ Q⁻¹) := by
    rw [hf a]
    obtain ⟨i, hi, hiEq⟩ := Finset.exists_mem_eq_sup' hs (fun i => wt i * cellF i a)
    rw [hiEq]
    have hwi := (hwt i hi).le
    have hmul := mul_le_mul_of_nonneg_left (hcellTri i hi a) hwi
    have hyv : wt i * cellY i a ≤ v a := by
      rw [hv a]
      exact (Finset.le_sup'_iff hs).2 ⟨i, hi, le_rfl⟩
    have hdu : wt i * cellD i a ≤ u a := by
      rw [hu a]
      exact (Finset.le_sup'_iff hs).2 ⟨i, hi, le_rfl⟩
    have hBpow : (wt i * cellB i) ^ Q ≤ B := by
      exact (Finset.single_le_sum (fun k hk => Real.rpow_nonneg
        (mul_nonneg (hwt k hk).le (hB0 k hk)) Q) hi).trans hBsum
    have hBroot : wt i * cellB i ≤ B ^ Q⁻¹ := by
      have hr := Real.rpow_le_rpow (Real.rpow_nonneg
        (mul_nonneg hwi (hB0 i hi)) Q) hBpow (inv_nonneg.mpr hQ0.le)
      rw [← Real.rpow_mul (mul_nonneg hwi (hB0 i hi)),
        mul_inv_cancel₀ (ne_of_gt hQ0), Real.rpow_one] at hr
      exact hr
    have hright := mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add hyv hdu) hBroot) hK
    nlinarith only [hmul, hright]
  have hquad' : u a ^ Q ≤ C * (tsum a + B) + C * (v a ^ (Q - 1) * u a) := by
    have hCB : 0 ≤ C * B := mul_nonneg hC.le hB
    nlinarith only [hquad, hCB]
  have hroot : B ^ Q⁻¹ ≤ (tsum a + B) ^ Q⁻¹ :=
    Real.rpow_le_rpow hB (by linarith only [ht0]) (inv_nonneg.mpr hQ0.le)
  have htri' : f a ≤ K * (v a + u a + (tsum a + B) ^ Q⁻¹) := by
    exact htri.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hroot) hK)
  exact collective_gap_absorption hQ hC hK hf0 hu0 hv0
    (add_nonneg ht0 hB) (by simpa only [mul_assoc] using hquad') htri'

end Transport
end HighContrast
end Homogenization
