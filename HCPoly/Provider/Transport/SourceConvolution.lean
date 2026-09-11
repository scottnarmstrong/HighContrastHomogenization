/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.DiscreteConvolution
import HCPoly.Provider.Transport.TransportCoefficients

/-!
# The transported source rows and their convolution

The transport of a complete history across one change of adapted geometry pays a
source residual at every target level of the new grid.  For the first `ℓ₀` levels
above the alignment scale the target cell is treated as one whole-source
residual, and the row is the early transport coefficient `𝖣_early^{tr,𝒮}(q')`;
from the level `j_* + ℓ₀` on the residual is continued, and the row is the
continued transport coefficient `𝖣_cont^{tr,𝒮}(q,q')` discounted by
`3^{-(1-g)(j-j_*)}`.  Those are the two rows of
`e.two.grid.whitney.fine.bound`, and the source charge `𝓔_src` of the two halves
of `e.two.grid.profile` is the sum of the weighted first and `Q`-th powers of
them.

This file computes that charge, the convolution of the source rows against the
profile weights:

`𝓔_src ≤ C3^{aℓ₀}(𝖣_src^{tr,𝒮} + (𝖣_src^{tr,𝒮})^Q)3^{-a(n-j_*)} = C3^{aℓ₀}𝓡_src^{tr,𝒮}`,

with the constant exhibited as the sum of three geometric totals, and with the
right-hand side exactly the transported source majorant.

Both weightings are proved, and both reduce to one estimate over an arbitrary
finite set of target levels above the alignment scale.  The early rows are
constant while the row weight grows geometrically towards the terminal scale, so
their total is the geometric series measured *down* from the last early level;
this is the one place the buffer factor `3^{aℓ₀}` is paid, and the total does not
grow with the number of early levels.  The continued rows decay at rate `p(1-g)`
for `p ∈ {1, Q}` while the row weight grows at rate `a`, and the printed
admissibility condition `a < 1 - g` gives `p(1-g) > a` for both, so their total
is the geometric series measured *up* from the alignment scale and costs no
buffer factor at all.  The `Q`-th powers need no separate argument: a row is a
coefficient times a geometric weight, so its `Q`-th power is again of that shape.

The centered weighting carries the `Q`-th power target coefficient
`3^{-(Qρ_max-d)(n-j)}` over the closed range of target levels rather than the
nonlinear row weight over the half-open one; the identity `Qρ_max - d = Qg + a`
makes it the smaller of the two at every level, so the same estimate serves, and
the one-step shift between the two weights is absorbed into the same constant.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

noncomputable section

variable {d : ℕ}

/-! ## The two geometric totals -/

/-- **The early levels.**  A row bounded by a constant on target levels at or
below the last early level pays, against the growing row weight, the geometric
total measured down from that level, at the single cost `3^{a(1+ℓ₀)}`. -/
private theorem early_geom_le {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    {jStar l0 n : ℤ} {f : ℤ → ℝ} (s : Finset ℤ) (hf : ∀ j ∈ s, f j ≤ c)
    (hs : ∀ j ∈ s, j ≤ jStar + l0) :
    ∑ j ∈ s, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * f j ≤
      (3 : ℝ) ^ a * (3 : ℝ) ^ (a * (l0 : ℝ)) * (1 / (1 - (3 : ℝ) ^ (-a))) *
        (c * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hK : (0 : ℝ) ≤ (3 : ℝ) ^ a * (3 : ℝ) ^ (a * (l0 : ℝ)) *
      (c * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg h3.le _) (Real.rpow_nonneg h3.le _))
      (mul_nonneg hc (Real.rpow_nonneg h3.le _))
  have hstep : ∀ j ∈ s, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * f j ≤
      ((3 : ℝ) ^ a * (3 : ℝ) ^ (a * (l0 : ℝ)) *
          (c * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))))) *
        (3 : ℝ) ^ (-a * (((jStar + l0 : ℤ) : ℝ) - (j : ℝ))) := by
    intro j hj
    have hw : (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) =
        ((3 : ℝ) ^ a * (3 : ℝ) ^ (a * (l0 : ℝ)) *
            (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) *
          (3 : ℝ) ^ (-a * (((jStar + l0 : ℤ) : ℝ) - (j : ℝ))) := by
      rw [← Real.rpow_add h3, ← Real.rpow_add h3, ← Real.rpow_add h3]
      congr 1
      push_cast
      ring
    have hA : (0 : ℝ) ≤ (3 : ℝ) ^ a * (3 : ℝ) ^ (a * (l0 : ℝ)) *
        (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) *
        (3 : ℝ) ^ (-a * (((jStar + l0 : ℤ) : ℝ) - (j : ℝ))) := by positivity
    rw [hw]
    exact le_trans (mul_le_mul_of_nonneg_left (hf j hj) hA) (le_of_eq (by ring))
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  exact le_trans (mul_le_mul_of_nonneg_left
    (sum_geom_below_le ha (jStar + l0) s hs) hK) (le_of_eq (by ring))

/-- **The continued levels.**  A row decaying at a rate above the row weight's
growth rate pays, against that weight, the geometric total of the difference
measured up from the alignment scale, and no buffer factor. -/
private theorem cont_geom_le {a p c : ℝ} (hap : a < p) (hc : 0 ≤ c)
    {jStar n : ℤ} {f : ℤ → ℝ} (s : Finset ℤ)
    (hf : ∀ j ∈ s, f j ≤ c * (3 : ℝ) ^ (-p * ((j : ℝ) - (jStar : ℝ))))
    (hs : ∀ j ∈ s, jStar ≤ j) :
    ∑ j ∈ s, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * f j ≤
      (3 : ℝ) ^ a * (1 / (1 - (3 : ℝ) ^ (-(p - a)))) *
        (c * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hpa : (0 : ℝ) < p - a := by linarith only [hap]
  have hK : (0 : ℝ) ≤ (3 : ℝ) ^ a *
      (c * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) :=
    mul_nonneg (Real.rpow_nonneg h3.le _)
      (mul_nonneg hc (Real.rpow_nonneg h3.le _))
  have hstep : ∀ j ∈ s, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * f j ≤
      ((3 : ℝ) ^ a * (c * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))))) *
        (3 : ℝ) ^ (-(p - a) * ((j : ℝ) - (jStar : ℝ))) := by
    intro j hj
    have hexp : (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
        (3 : ℝ) ^ (-p * ((j : ℝ) - (jStar : ℝ))) =
        (3 : ℝ) ^ a * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) *
          (3 : ℝ) ^ (-(p - a) * ((j : ℝ) - (jStar : ℝ))) := by
      rw [← Real.rpow_add h3, ← Real.rpow_add h3, ← Real.rpow_add h3]
      congr 1
      ring
    refine le_trans (mul_le_mul_of_nonneg_left (hf j hj)
      (Real.rpow_nonneg h3.le _)) (le_of_eq ?_)
    calc (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
          (c * (3 : ℝ) ^ (-p * ((j : ℝ) - (jStar : ℝ))))
        = c * ((3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            (3 : ℝ) ^ (-p * ((j : ℝ) - (jStar : ℝ)))) := by ring
      _ = c * ((3 : ℝ) ^ a * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) *
            (3 : ℝ) ^ (-(p - a) * ((j : ℝ) - (jStar : ℝ)))) := by rw [hexp]
      _ = ((3 : ℝ) ^ a * (c * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))))) *
            (3 : ℝ) ^ (-(p - a) * ((j : ℝ) - (jStar : ℝ))) := by ring
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  exact le_trans (mul_le_mul_of_nonneg_left
    (sum_geom_above_le hpa jStar s hs) hK) (le_of_eq (by ring))

/-! ## The source charge -/

/-- **The convolution of the source rows against the profile weights.**
A row bounded by the two branches of `e.two.grid.whitney.fine.bound`, together
with its `Q`-th power, summed against the nonlinear row weight over an arbitrary
finite set of target levels above the alignment scale, is at most one buffer
factor times `(D + D^Q)3^{-a(n-j_*)}` for any `D` dominating both branches.  The
constant is exhibited as the sum of the three geometric totals: the early one
measured down from the last early level, and the two continued ones measured up
from the alignment scale at the rates `1 - g - a` and `Q(1-g) - a`. -/
theorem source_rows_le {g Q a Dcont Dearly Dsrc : ℝ} (ha : 0 < a)
    (hahi : a < 1 - g) (hQ : 1 ≤ Q) (hDc : 0 ≤ Dcont)
    (hDs : 0 ≤ Dsrc) (hcs : Dcont ≤ Dsrc) (hes : Dearly ≤ Dsrc)
    {eps : ℤ → ℝ} (heps : ∀ j, 0 ≤ eps j) {jStar l0 : ℤ} (hl0 : 0 ≤ l0)
    (hearly : ∀ j, jStar ≤ j → j < jStar + l0 → eps j ≤ Dearly)
    (hcont : ∀ j, jStar + l0 ≤ j →
      eps j ≤ Dcont * (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))))
    (n : ℤ) (s : Finset ℤ) (hs : ∀ j ∈ s, jStar ≤ j) :
    ∑ j ∈ s, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * (eps j + eps j ^ Q) ≤
      (3 : ℝ) ^ a *
            (1 / (1 - (3 : ℝ) ^ (-a)) + 1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
              1 / (1 - (3 : ℝ) ^ (-(Q * (1 - g) - a)))) *
          (3 : ℝ) ^ (a * (l0 : ℝ)) *
        ((Dsrc + Dsrc ^ Q) * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hg1 : (0 : ℝ) < 1 - g := by linarith only [ha, hahi]
  have hcQ : a < Q * (1 - g) := by
    have h1 : (1 : ℝ) - g ≤ Q * (1 - g) := le_mul_of_one_le_left hg1.le hQ
    linarith only [h1, hahi]
  have hden1 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 - g - a)) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num)
      (neg_neg_iff_pos.mpr (by linarith only [hahi] : (0 : ℝ) < 1 - g - a))
    linarith only [hlt]
  have hden2 : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(Q * (1 - g) - a)) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num)
      (neg_neg_iff_pos.mpr (by linarith only [hcQ] : (0 : ℝ) < Q * (1 - g) - a))
    linarith only [hlt]
  have hDsQ : (0 : ℝ) ≤ Dsrc ^ Q := Real.rpow_nonneg hDs Q
  have hD0 : (0 : ℝ) ≤ Dsrc + Dsrc ^ Q := by linarith only [hDs, hDsQ]
  have hDcD : Dcont ≤ Dsrc + Dsrc ^ Q := by linarith only [hcs, hDsQ]
  have hDcQD : Dcont ^ Q ≤ Dsrc + Dsrc ^ Q := by
    have h := Real.rpow_le_rpow hDc hcs hQ0
    linarith only [h, hDs]
  have hW0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) :=
    Real.rpow_nonneg h3.le _
  have hDW : (0 : ℝ) ≤ (Dsrc + Dsrc ^ Q) *
      (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) := mul_nonneg hD0 hW0
  have hbuf : (1 : ℝ) ≤ (3 : ℝ) ^ (a * (l0 : ℝ)) := by
    have hnn : (0 : ℝ) ≤ a * (l0 : ℝ) :=
      mul_nonneg ha.le (by exact_mod_cast hl0)
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hnn
  -- the early levels
  have hE : ∑ j ∈ s.filter (fun j => j < jStar + l0),
      (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * (eps j + eps j ^ Q) ≤
      (3 : ℝ) ^ a * (1 / (1 - (3 : ℝ) ^ (-a))) *
        ((3 : ℝ) ^ (a * (l0 : ℝ)) * ((Dsrc + Dsrc ^ Q) *
          (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))))) := by
    refine le_trans (early_geom_le ha hD0 _ (fun j hj => ?_) (fun j hj => ?_))
      (le_of_eq (by ring))
    · obtain ⟨hjs, hjlt⟩ := Finset.mem_filter.mp hj
      have hle : eps j ≤ Dsrc := le_trans (hearly j (hs j hjs) hjlt) hes
      exact add_le_add hle (Real.rpow_le_rpow (heps j) hle hQ0)
    · exact le_of_lt (Finset.mem_filter.mp hj).2
  -- the continued levels, split into the first and the `Q`-th power
  have hmem : ∀ j ∈ s.filter (fun j => ¬ j < jStar + l0), jStar + l0 ≤ j :=
    fun j hj => not_lt.mp (Finset.mem_filter.mp hj).2
  have hC1 : ∑ j ∈ s.filter (fun j => ¬ j < jStar + l0),
      (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * eps j ≤
      (3 : ℝ) ^ a * (1 / (1 - (3 : ℝ) ^ (-(1 - g - a)))) *
        ((3 : ℝ) ^ (a * (l0 : ℝ)) * ((Dsrc + Dsrc ^ Q) *
          (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))))) := by
    refine le_trans (cont_geom_le hahi hDc _ (fun j hj => hcont j (hmem j hj))
      (fun j hj => le_trans (show jStar ≤ jStar + l0 by omega) (hmem j hj))) ?_
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (Real.rpow_nonneg h3.le _) (div_nonneg zero_le_one hden1.le))
    calc Dcont * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))
        ≤ (Dsrc + Dsrc ^ Q) * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) :=
          mul_le_mul_of_nonneg_right hDcD hW0
      _ = 1 * ((Dsrc + Dsrc ^ Q) *
            (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) := by ring
      _ ≤ (3 : ℝ) ^ (a * (l0 : ℝ)) * ((Dsrc + Dsrc ^ Q) *
            (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) :=
          mul_le_mul_of_nonneg_right hbuf hDW
  have hC2 : ∑ j ∈ s.filter (fun j => ¬ j < jStar + l0),
      (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * eps j ^ Q ≤
      (3 : ℝ) ^ a * (1 / (1 - (3 : ℝ) ^ (-(Q * (1 - g) - a)))) *
        ((3 : ℝ) ^ (a * (l0 : ℝ)) * ((Dsrc + Dsrc ^ Q) *
          (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))))) := by
    refine le_trans (cont_geom_le hcQ (Real.rpow_nonneg hDc Q) _
      (fun j hj => ?_)
      (fun j hj => le_trans (show jStar ≤ jStar + l0 by omega) (hmem j hj))) ?_
    · refine le_trans (Real.rpow_le_rpow (heps j) (hcont j (hmem j hj)) hQ0)
        (le_of_eq ?_)
      have hexp : -(1 - g) * ((j : ℝ) - (jStar : ℝ)) * Q =
          -(Q * (1 - g)) * ((j : ℝ) - (jStar : ℝ)) := by ring
      rw [Real.mul_rpow hDc (Real.rpow_nonneg h3.le _), ← Real.rpow_mul h3.le,
        hexp]
    · refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (Real.rpow_nonneg h3.le _) (div_nonneg zero_le_one hden2.le))
      calc Dcont ^ Q * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))
          ≤ (Dsrc + Dsrc ^ Q) * (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ))) :=
            mul_le_mul_of_nonneg_right hDcQD hW0
        _ = 1 * ((Dsrc + Dsrc ^ Q) *
              (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) := by ring
        _ ≤ (3 : ℝ) ^ (a * (l0 : ℝ)) * ((Dsrc + Dsrc ^ Q) *
              (3 : ℝ) ^ (-a * ((n : ℝ) - (jStar : ℝ)))) :=
            mul_le_mul_of_nonneg_right hbuf hDW
  have hsplit : ∑ j ∈ s,
      (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * (eps j + eps j ^ Q) =
      (∑ j ∈ s.filter (fun j => j < jStar + l0),
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * (eps j + eps j ^ Q)) +
        ((∑ j ∈ s.filter (fun j => ¬ j < jStar + l0),
            (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * eps j) +
          ∑ j ∈ s.filter (fun j => ¬ j < jStar + l0),
            (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * eps j ^ Q) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_filter_add_sum_filter_not s
      (fun j => j < jStar + l0)]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)
  rw [hsplit]
  exact le_trans (add_le_add hE (add_le_add hC1 hC2)) (le_of_eq (by ring))

end

end Transport
end HighContrast
end Homogenization
