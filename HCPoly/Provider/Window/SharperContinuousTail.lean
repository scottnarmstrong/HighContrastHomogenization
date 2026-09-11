/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.SharperSuccessorTail


namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory Filter
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

private theorem growthBar_pow_pos_sharp (K : ℝ) (d : ℕ) :
    0 < growthBar K ^ (4 * (d + 1)) := by
  apply pow_pos
  rw [growthBar]
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

private theorem sharp_prefactor_identity {C x y : ℝ} {k : ℤ}
    (hC : 0 < C) (hy : 0 < y) (hx : x = C⁻¹ * (3 : ℝ) ^ k) :
    (3 / 2 : ℝ) * (3 : ℝ) ^ (-k) * y⁻¹ =
      (3 / (2 * C)) * (x * y)⁻¹ := by
  rw [hx, zpow_neg]
  field_simp [hC.ne', hy.ne', zpow_ne_zero]

/-- The continuous strict-successor estimate before the geometric prefactor
is absorbed into the gauge tail. -/
theorem measureReal_successorScale_tail_sharp [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {t : ℝ} (ht : 1 ≤ t) :
    P.real {a : CoeffSpace d |
        ENNReal.ofReal
          (max ((3 : ℝ) ^ M)
            (t * growthBar K ^ (4 * (d + 1)) *
              (3 : ℝ) ^ (M - jStar + 1))) <
          successorScale g E (M - jStar) a} ≤
      (3 / (2 * growthBar K ^ (4 * (d + 1))) : ℝ) *
        (t * Ψ t)⁻¹ := by
  let h : ℤ := M - jStar
  let C : ℝ := growthBar K ^ (4 * (d + 1))
  let T : ℝ := (3 : ℝ) ^ (jStar - 1) * C⁻¹
  let X : ℝ := t * C * (3 : ℝ) ^ (h + 1)
  have hC : 0 < C := growthBar_pow_pos_sharp K d
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hX : 0 < X := by dsimp only [X]; positivity
  have hthreshold : T * C * (3 : ℝ) ^ (h + 1) = (3 : ℝ) ^ M := by
    calc
      T * C * (3 : ℝ) ^ (h + 1) =
          (3 : ℝ) ^ (jStar - 1) * (3 : ℝ) ^ (h + 1) := by
            dsimp only [T]
            field_simp [hC.ne']
      _ = (3 : ℝ) ^ ((jStar - 1) + (h + 1)) :=
        (zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) _ _).symm
      _ = (3 : ℝ) ^ M := by dsimp only [h]; congr 1; omega
  by_cases hlarge : T ≤ t
  · obtain ⟨n, hnlow, hnup⟩ := exists_mem_Ico_zpow hX (by norm_num : (1 : ℝ) < 3)
    let x : ℝ := C⁻¹ * (3 : ℝ) ^ (n - h)
    have hxpos : 0 < x := by dsimp only [x]; positivity
    have hMX : (3 : ℝ) ^ M ≤ X := by
      have hm := mul_le_mul_of_nonneg_right hlarge
        (mul_nonneg hC.le (by positivity : 0 ≤ (3 : ℝ) ^ (h + 1)))
      calc
        (3 : ℝ) ^ M = T * C * (3 : ℝ) ^ (h + 1) := hthreshold.symm
        _ = T * (C * (3 : ℝ) ^ (h + 1)) := by ring
        _ ≤ t * (C * (3 : ℝ) ^ (h + 1)) := hm
        _ = X := by dsimp only [X]; ring
    have hnM : M ≤ n := by
      have hlt : (3 : ℝ) ^ M < (3 : ℝ) ^ (n + 1) := hMX.trans_lt hnup
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hlt
      omega
    have hden : 0 < C * (3 : ℝ) ^ (h + 1) := by positivity
    have htx : t < x := by
      have hraw : t < (3 : ℝ) ^ (n + 1) /
          (C * (3 : ℝ) ^ (h + 1)) := by
        apply (lt_div_iff₀ hden).2
        simpa only [X, mul_assoc] using hnup
      have hpow : (3 : ℝ) ^ (n + 1) / (3 : ℝ) ^ (h + 1) =
          (3 : ℝ) ^ (n - h) := by
        rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
        congr 1
        omega
      calc
        t < (3 : ℝ) ^ (n + 1) / (C * (3 : ℝ) ^ (h + 1)) := hraw
        _ = C⁻¹ * ((3 : ℝ) ^ (n + 1) / (3 : ℝ) ^ (h + 1)) := by
          field_simp [hC.ne', zpow_ne_zero]
        _ = x := by rw [hpow]
    have hψle : Ψ t ≤ Ψ x := hdag.gauge_admissible.1
      (zero_le_one.trans ht) hxpos.le htx.le
    have hψt : 0 < Ψ t := lt_of_lt_of_le zero_lt_one
      (hdag.gauge_admissible.2 (zero_le_one.trans ht))
    have hψx : 0 < Ψ x := lt_of_lt_of_le zero_lt_one
      (hdag.gauge_admissible.2 hxpos.le)
    have hprod : t * Ψ t ≤ x * Ψ x :=
      mul_le_mul htx.le hψle hψt.le hxpos.le
    have hinv : (x * Ψ x)⁻¹ ≤ (t * Ψ t)⁻¹ :=
      (inv_le_inv₀ (mul_pos hxpos hψx) (mul_pos htpos hψt)).2 hprod
    have hsub : {a : CoeffSpace d |
        ENNReal.ofReal (max ((3 : ℝ) ^ M) X) < successorScale g E h a} ⊆
        {a : CoeffSpace d |
          ENNReal.ofReal ((3 : ℝ) ^ n) < successorScale g E h a} := by
      intro a ha
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal
        (hnlow.trans (le_max_right _ _))) ha
    calc
      P.real {a : CoeffSpace d |
          ENNReal.ofReal
            (max ((3 : ℝ) ^ M)
              (t * growthBar K ^ (4 * (d + 1)) *
                (3 : ℝ) ^ (M - jStar + 1))) <
            successorScale g E (M - jStar) a}
          ≤ P.real {a : CoeffSpace d |
            ENNReal.ofReal ((3 : ℝ) ^ n) < successorScale g E h a} := by
              simpa only [C, h, X] using measureReal_mono hsub
      _ ≤ (3 / 2 : ℝ) * (3 : ℝ) ^ (-(n - h)) * (Ψ x)⁻¹ := by
        simpa only [C, h, x] using
          measureReal_successorScale_gt_zpow_le_sharp hstat hdag hQ hw hnM
      _ = (3 / (2 * C) : ℝ) * (x * Ψ x)⁻¹ :=
        sharp_prefactor_identity hC hψx rfl
      _ ≤ (3 / (2 * C) : ℝ) * (t * Ψ t)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (3 / (2 * growthBar K ^ (4 * (d + 1))) : ℝ) *
          (t * Ψ t)⁻¹ := by rfl
  · have hsmall : t < T := lt_of_not_ge hlarge
    let x : ℝ := C⁻¹ * (3 : ℝ) ^ (M - h)
    have hxpos : 0 < x := by dsimp only [x]; positivity
    have hXM : X < (3 : ℝ) ^ M := by
      have hm := mul_lt_mul_of_pos_right hsmall
        (mul_pos hC (by positivity : 0 < (3 : ℝ) ^ (h + 1)))
      calc
        X = t * (C * (3 : ℝ) ^ (h + 1)) := by dsimp only [X]; ring
        _ < T * (C * (3 : ℝ) ^ (h + 1)) := hm
        _ = T * C * (3 : ℝ) ^ (h + 1) := by ring
        _ = (3 : ℝ) ^ M := hthreshold
    have htx : t ≤ x := by
      have hTle : T ≤ x := by
        have hz : (3 : ℝ) ^ (jStar - 1) ≤ (3 : ℝ) ^ jStar :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have hm := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hC.le)
        dsimp only [T, x, h]
        rw [show M - (M - jStar) = jStar by omega]
        simpa only [mul_comm] using hm
      exact hsmall.le.trans hTle
    have hψle : Ψ t ≤ Ψ x := hdag.gauge_admissible.1
      (zero_le_one.trans ht) hxpos.le htx
    have hψt : 0 < Ψ t := lt_of_lt_of_le zero_lt_one
      (hdag.gauge_admissible.2 (zero_le_one.trans ht))
    have hψx : 0 < Ψ x := lt_of_lt_of_le zero_lt_one
      (hdag.gauge_admissible.2 hxpos.le)
    have hprod : t * Ψ t ≤ x * Ψ x :=
      mul_le_mul htx hψle hψt.le hxpos.le
    have hinv : (x * Ψ x)⁻¹ ≤ (t * Ψ t)⁻¹ :=
      (inv_le_inv₀ (mul_pos hxpos hψx) (mul_pos htpos hψt)).2 hprod
    calc
      P.real {a : CoeffSpace d |
          ENNReal.ofReal
            (max ((3 : ℝ) ^ M)
              (t * growthBar K ^ (4 * (d + 1)) *
                (3 : ℝ) ^ (M - jStar + 1))) <
            successorScale g E (M - jStar) a}
          = P.real {a : CoeffSpace d |
              ENNReal.ofReal ((3 : ℝ) ^ M) < successorScale g E h a} := by
                simp only [C, h, X, max_eq_left hXM.le]
      _ ≤ (3 / 2 : ℝ) * (3 : ℝ) ^ (-(M - h)) * (Ψ x)⁻¹ := by
        simpa only [C, h, x] using
          measureReal_successorScale_gt_zpow_le_sharp hstat hdag hQ hw le_rfl
      _ = (3 / (2 * C) : ℝ) * (x * Ψ x)⁻¹ :=
        sharp_prefactor_identity hC hψx rfl
      _ ≤ (3 / (2 * C) : ℝ) * (t * Ψ t)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (3 / (2 * growthBar K ^ (4 * (d + 1))) : ℝ) *
          (t * Ψ t)⁻¹ := by rfl

end
end Window
end HighContrast
end Homogenization

