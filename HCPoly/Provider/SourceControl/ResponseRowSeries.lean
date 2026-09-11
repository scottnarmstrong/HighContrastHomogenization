/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.DiscreteConvolution
import HCPoly.Provider.Transport.WindowCellBounds

/-!
# The all-earlier geometric series of `e.source.adapted.bound`

The all-earlier response row at the response scale weights
the scale-`k` cell average by `3^{\lambda(k-s)}` and pays the burn discount
`3^{g(j_*-k)}` that every cell bound below the alignment scale carries.  The
printed proof sums the resulting weights: with `k = j_* - u`,
`u \geq 1`,
```
∑_{k<j_*} 3^{λ(k-s)}3^{g(j_*-k)}
  = 3^{-λ(s-j_*)} ∑_{u≥1} 3^{-(λ-g)u}
  = 3^{-λ(s-j_*)}/(3^{λ-g}-1).
```
This file proves that bound in the partial-sum form the frozen statement
carries, over an arbitrary window `Ico Klo j_*` of scales below the alignment.

Two facts do the work.  Below the alignment scale the positive part in the burn
discount is inert, so the discount is the bare power `3^{g(j_*-k)}`; and the
product of the two powers factors as
`3^{-λ(s-j_*)}·3^{-(λ-g)}·3^{-(λ-g)((j_*-1)-k)}`, which is the printed index
shift `u \geq 1` written so that the exponent is measured from the top scale
`j_*-1` of the summation range.  The geometric weight below a threshold
then bounds the remaining sum by `(1-3^{-(λ-g)})^{-1}`, and the one factor
`3^{-(λ-g)}` pulled out in front turns that into the printed `(3^{λ-g}-1)^{-1}`.
The series converges precisely because `λ > g`, which is the printed hypothesis.

No hypothesis beyond `λ > g` is used: the bound holds for every `s`, every
`j_*` and every lower cut `Klo`, in particular for cuts at or above the
alignment scale, where the sum is empty.
-/

namespace Homogenization
namespace HighContrast
namespace SourceControl

noncomputable section

/-! ## The burn discount below the alignment scale -/

/-- **The burn discount below the alignment scale** is the bare power
`3^{g(j_*-k)}`: the positive part of `e.source.adapted.bound` is
inert there. -/
theorem burnDiscount_of_lt {g : ℝ} {jStar k : ℤ} (hk : k < jStar) :
    burnDiscount g jStar k = (3 : ℝ) ^ (g * ((jStar : ℝ) - (k : ℝ))) := by
  have hkk : (k : ℝ) < (jStar : ℝ) := by exact_mod_cast hk
  rw [burnDiscount,
    max_eq_left (by linarith only [hkk] : (0 : ℝ) ≤ (jStar : ℝ) - (k : ℝ))]

/-- **The printed index shift.**  The scale weight times the burn discount
factors into the row prefactor `3^{-λ(s-j_*)}`, the one factor `3^{-(λ-g)}` of
the shift `u \geq 1`, and the geometric weight of `k` measured from the top
scale `j_*-1` of the all-earlier range. -/
theorem rpow_mul_burnDiscount_eq {g lam : ℝ} {jStar s k : ℤ} (hk : k < jStar) :
    (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) * burnDiscount g jStar k =
      ((3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) * (3 : ℝ) ^ (-(lam - g))) *
        (3 : ℝ) ^ (-(lam - g) * (((jStar - 1 : ℤ) : ℝ) - (k : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [burnDiscount_of_lt hk, ← Real.rpow_add h3, ← Real.rpow_add h3, ← Real.rpow_add h3]
  congr 1
  push_cast
  ring

/-! ## The series -/

/-- The ratio of the all-earlier series exceeds one exactly because `λ > g`. -/
theorem one_lt_rpow_sub {g lam : ℝ} (hlam : g < lam) :
    (1 : ℝ) < (3 : ℝ) ^ (lam - g) := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (x := (3 : ℝ)) (by norm_num)
    (show (0 : ℝ) < lam - g by linarith only [hlam])
  rwa [Real.rpow_zero] at h

/-- **The all-earlier geometric series**, the sum of 02:2604-2613 in the
partial-sum form of the frozen statement.  Every scale below the alignment
carries the scale weight and the burn discount; the total is the printed
`3^{-λ(s-j_*)}/(3^{λ-g}-1)`. -/
theorem sum_rpow_mul_burnDiscount_le {g lam : ℝ} (hlam : g < lam) (jStar s Klo : ℤ) :
    ∑ k ∈ Finset.Ico Klo jStar,
        (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) * burnDiscount g jStar k ≤
      (3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) / ((3 : ℝ) ^ (lam - g) - 1) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hc : (0 : ℝ) < lam - g := by linarith only [hlam]
  have hR : (1 : ℝ) < (3 : ℝ) ^ (lam - g) := one_lt_rpow_sub hlam
  have hfac : (0 : ℝ) ≤ (3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) *
      (3 : ℝ) ^ (-(lam - g)) :=
    mul_nonneg (Real.rpow_nonneg h3.le _) (Real.rpow_nonneg h3.le _)
  have hgeom := Transport.sum_geom_below_le hc (jStar - 1) (Finset.Ico Klo jStar)
    (fun k hk => by have := (Finset.mem_Ico.mp hk).2; omega)
  rw [Finset.sum_congr rfl
      (fun k hk => rpow_mul_burnDiscount_eq (s := s) (Finset.mem_Ico.mp hk).2),
    ← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left hgeom hfac) (le_of_eq ?_)
  rw [Real.rpow_neg h3.le]
  have hRne : ((3 : ℝ) ^ (lam - g)) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hR)
  have hsub : ((3 : ℝ) ^ (lam - g)) - 1 ≠ 0 := by
    have : (0 : ℝ) < (3 : ℝ) ^ (lam - g) - 1 := by linarith only [hR]
    exact ne_of_gt this
  field_simp

end

end SourceControl
end HighContrast
end Homogenization
