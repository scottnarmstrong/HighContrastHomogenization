/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Transport
import HCPoly.Provider.Recurrence.GainArith
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The powered recurrence

`e.fixed.geometry.parent.child.powered` is the `Q`-th power of
`p.fixed.geometry.parent.child.recurrence`:

`(v_{r+h}^q)^Q ≤ β_h e^{QΔ_{r,r+h}^q}(v_r^q)^Q + C(d,Q)(e^{QΔ_{r,r+h}^q} - 1)`,
`β_h = 2^{Q-1}C_{\rm rec}^Q3^{-hQd/2}`,

which is exactly the centered part of the portable contraction factor
`λ_port` of `p.fixed.geometry.one.grid.propagation`.

Two elementary steps produce it.  The first is the unweighted mean inequality
`(x + y)^Q ≤ 2^{Q-1}(x^Q + y^Q)`, which turns the recurrence's two-term right
side into two powered terms.  The second is the estimate

`Φ_Q(x)^Q ≤ 2^Q(e^{Qx} - 1)`,

which says that the increment's own gain contributes no scale-independent error
once it is raised to the power `Q`: the first summand of `Φ_Q` powers to
`e^{(Q-1)x}(e^x - 1) = e^{Qx} - e^{(Q-1)x}`, and the second to `(e^x - 1)^Q`,
which is at most `e^{Qx} - 1` because `t ↦ t^Q` is superadditive.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open scoped ENNReal

noncomputable section

/-! ## The unweighted mean inequality over the reals -/

/-- The unweighted mean inequality for two nonnegative reals. -/
theorem rpow_add_le_mul_rpow_add_rpow {A B Q : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 1 ≤ Q) :
    (A + B) ^ Q ≤ 2 ^ (Q - 1) * (A ^ Q + B ^ Q) := by
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow ⟨A, hA⟩ ⟨B, hB⟩ hQ
  have hcoe := NNReal.coe_le_coe.mpr h
  push_cast at hcoe
  exact hcoe

/-! ## The gain at a power -/

/-- **The gain of an increment carries no scale-independent error at the power
`Q`.**  This is `Φ_Q(x)^Q ≤ 2^Q(e^{Qx} - 1)`. -/
theorem gainPhi_rpow_le {Q x : ℝ} (hQ : 1 ≤ Q) (hx : 0 ≤ x) :
    gainPhi Q x ^ Q ≤ 2 ^ Q * (Real.exp (Q * x) - 1) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hB0 : (0 : ℝ) ≤ Real.exp x - 1 := by
    have := Real.one_le_exp hx
    linarith only [this]
  have hA0 : (0 : ℝ) ≤ Real.exp ((1 - Q⁻¹) * x) * (Real.exp x - 1) ^ Q⁻¹ :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hB0 _)
  -- the first summand at the power `Q`
  have hQne : Q ≠ 0 := ne_of_gt hQ0
  have hexpo : (1 - Q⁻¹) * x * Q = (Q - 1) * x := by
    field_simp
  have hApow : (Real.exp ((1 - Q⁻¹) * x) * (Real.exp x - 1) ^ Q⁻¹) ^ Q =
      Real.exp ((Q - 1) * x) * (Real.exp x - 1) := by
    rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg hB0 _), ← Real.exp_mul,
      ← Real.rpow_mul hB0, inv_mul_cancel₀ hQne, Real.rpow_one, hexpo]
  have hAle : Real.exp ((Q - 1) * x) * (Real.exp x - 1) ≤ Real.exp (Q * x) - 1 := by
    have hexp : Real.exp ((Q - 1) * x) * (Real.exp x - 1) =
        Real.exp (Q * x) - Real.exp ((Q - 1) * x) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2
      ring
    have hone : (1 : ℝ) ≤ Real.exp ((Q - 1) * x) :=
      Real.one_le_exp (mul_nonneg (by linarith only [hQ]) hx)
    rw [hexp]
    linarith only [hone]
  -- the second summand at the power `Q`
  have hBle : (Real.exp x - 1) ^ Q ≤ Real.exp (Q * x) - 1 := by
    have hsuper := Real.add_rpow_le_rpow_add (p := Q) (a := 1) (b := Real.exp x - 1)
      zero_le_one hB0 hQ
    rw [Real.one_rpow] at hsuper
    have hsum : (1 : ℝ) + (Real.exp x - 1) = Real.exp x := by ring
    rw [hsum, ← Real.exp_mul, mul_comm x Q] at hsuper
    linarith only [hsuper]
  have hmean := rpow_add_le_mul_rpow_add_rpow hA0 hB0 hQ
  have htwo : (2 : ℝ) ^ (Q - 1) * 2 = 2 ^ Q := by
    have h1 : (2 : ℝ) ^ (Q - 1) * (2 : ℝ) ^ (1 : ℝ) = 2 ^ (Q - 1 + 1) :=
      (Real.rpow_add two_pos _ _).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    congr 1
    ring
  have hpos : (0 : ℝ) < 2 ^ (Q - 1) := Real.rpow_pos_of_pos two_pos _
  have hstep : (2 : ℝ) ^ (Q - 1) *
      ((Real.exp ((1 - Q⁻¹) * x) * (Real.exp x - 1) ^ Q⁻¹) ^ Q + (Real.exp x - 1) ^ Q) ≤
      2 ^ (Q - 1) * (2 * (Real.exp (Q * x) - 1)) := by
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    rw [hApow]
    linarith only [hAle, hBle]
  have hfinal : (2 : ℝ) ^ (Q - 1) * (2 * (Real.exp (Q * x) - 1)) =
      2 ^ Q * (Real.exp (Q * x) - 1) := by
    rw [← htwo]
    ring
  calc gainPhi Q x ^ Q
      = (Real.exp ((1 - Q⁻¹) * x) * (Real.exp x - 1) ^ Q⁻¹ + (Real.exp x - 1)) ^ Q := rfl
    _ ≤ 2 ^ (Q - 1) *
          ((Real.exp ((1 - Q⁻¹) * x) * (Real.exp x - 1) ^ Q⁻¹) ^ Q +
            (Real.exp x - 1) ^ Q) := hmean
    _ ≤ 2 ^ (Q - 1) * (2 * (Real.exp (Q * x) - 1)) := hstep
    _ = 2 ^ Q * (Real.exp (Q * x) - 1) := hfinal

/-! ## The two-term step in the extended reals -/

/-- **The unweighted mean inequality on a two-term bound in `ℝ≥0∞`.** -/
theorem rpow_le_of_le_add {Q : ℝ} (hQ : 1 ≤ Q) {c g : ℝ} (hc : 0 ≤ c) (hg : 0 ≤ g)
    {u v : ℝ≥0∞} (h : v ≤ ENNReal.ofReal c * u + ENNReal.ofReal g) :
    v ^ Q ≤ ENNReal.ofReal (2 ^ (Q - 1) * c ^ Q) * u ^ Q +
      ENNReal.ofReal (2 ^ (Q - 1) * g ^ Q) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hQ1 : (0 : ℝ) ≤ Q - 1 := by linarith only [hQ]
  have htwo : (2 : ℝ≥0∞) ^ (Q - 1) = ENNReal.ofReal (2 ^ (Q - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hQ1, ENNReal.ofReal_ofNat]
  calc v ^ Q ≤ (ENNReal.ofReal c * u + ENNReal.ofReal g) ^ Q := ENNReal.rpow_le_rpow h hQ0
    _ ≤ 2 ^ (Q - 1) * ((ENNReal.ofReal c * u) ^ Q + ENNReal.ofReal g ^ Q) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hQ
    _ = ENNReal.ofReal (2 ^ (Q - 1) * c ^ Q) * u ^ Q +
          ENNReal.ofReal (2 ^ (Q - 1) * g ^ Q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hQ0,
          ENNReal.ofReal_rpow_of_nonneg hc hQ0, ENNReal.ofReal_rpow_of_nonneg hg hQ0,
          htwo, mul_add, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
          ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), ← mul_assoc]

/-! ## The powered recurrence -/

/-- **`e.fixed.geometry.parent.child.powered`.**  Raising the fixed-grid
recurrence to the power `Q` produces the contraction factor
`β_h = 2^{Q-1}C_{\rm rec}^Q(3^{-hd/2})^Q` on the powered moment, and an error
proportional to `e^{QΔ} - 1` only. -/
theorem powered_recurrence {Q Crec D e : ℝ} (hQ : 1 ≤ Q) (hCrec : 0 ≤ Crec) (hD : 0 ≤ D)
    (he : 0 ≤ e) {u v : ℝ≥0∞}
    (hstep : v ≤ ENNReal.ofReal (Crec * e * Real.exp D) * u +
      ENNReal.ofReal (Crec * gainPhi Q D)) :
    v ^ Q ≤ ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * e ^ Q * Real.exp (Q * D)) * u ^ Q +
      ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q * (Real.exp (Q * D) - 1)) := by
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hgain : 0 ≤ gainPhi Q D := Recurrence.gainPhi_nonneg hD
  have hc : 0 ≤ Crec * e * Real.exp D :=
    mul_nonneg (mul_nonneg hCrec he) (Real.exp_pos _).le
  have hg : 0 ≤ Crec * gainPhi Q D := mul_nonneg hCrec hgain
  have hcpow : (Crec * e * Real.exp D) ^ Q = Crec ^ Q * e ^ Q * Real.exp (Q * D) := by
    rw [Real.mul_rpow (mul_nonneg hCrec he) (Real.exp_pos _).le,
      Real.mul_rpow hCrec he, ← Real.exp_mul, mul_comm D Q]
  have hgpow : (Crec * gainPhi Q D) ^ Q ≤ Crec ^ Q * (2 ^ Q * (Real.exp (Q * D) - 1)) := by
    rw [Real.mul_rpow hCrec hgain]
    exact mul_le_mul_of_nonneg_left (gainPhi_rpow_le hQ hD) (Real.rpow_nonneg hCrec _)
  have hbase := rpow_le_of_le_add hQ hc hg hstep
  have hfirst : ENNReal.ofReal (2 ^ (Q - 1) * (Crec * e * Real.exp D) ^ Q) =
      ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * e ^ Q * Real.exp (Q * D)) := by
    rw [hcpow]
    congr 1
    ring
  have hsecond : ENNReal.ofReal (2 ^ (Q - 1) * (Crec * gainPhi Q D) ^ Q) ≤
      ENNReal.ofReal (2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q * (Real.exp (Q * D) - 1)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_left hgpow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (Q - 1))
    calc (2 : ℝ) ^ (Q - 1) * (Crec * gainPhi Q D) ^ Q
        ≤ 2 ^ (Q - 1) * (Crec ^ Q * (2 ^ Q * (Real.exp (Q * D) - 1))) := this
      _ = 2 ^ (Q - 1) * Crec ^ Q * 2 ^ Q * (Real.exp (Q * D) - 1) := by ring
  rw [hfirst] at hbase
  exact le_trans hbase (add_le_add le_rfl hsecond)

end

end PortableHistory
end HighContrast
end Homogenization
