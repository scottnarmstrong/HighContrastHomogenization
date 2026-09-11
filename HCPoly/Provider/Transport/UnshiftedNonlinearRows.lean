/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.DiscreteConvolution

/-!
# Unshifted nonlinear rows

This is the bulk-plus-boundary convolution for a filling that runs through the
target scale itself.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

noncomputable section

/-- An unshifted bulk row and its lower-scale boundary rows are paid by the old
nonlinear row total with one buffer factor. -/
theorem unshifted_nonlinear_rows_le {a g C : ℝ}
    (hahi : a < 1 - g) (hC : 0 ≤ C) {jStar n t l0 : ℤ}
    (ht : t = n + l0) (hl0 : 1 ≤ l0) {hold hnew : ℤ → ℝ}
    (hold0 : ∀ r ∈ Finset.Ico jStar t, 0 ≤ hold r)
    (hrow : ∀ j ∈ Finset.Icc jStar n,
      hnew j ≤ hold j +
        C * ∑ r ∈ Finset.Ico jStar j,
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r) :
    ∑ j ∈ Finset.Icc jStar n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hnew j ≤
      (1 + C *
          ((3 : ℝ) ^ (-(1 - g - a)) /
            (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
        (3 : ℝ) ^ (a * (l0 : ℝ)) *
          ∑ r ∈ Finset.Ico jStar t,
            (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) * hold r := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have htR : (t : ℝ) = (n : ℝ) + (l0 : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ht
  have hnt : n < t := by omega
  have hsubJ : Finset.Icc jStar n ⊆ Finset.Ico jStar t := by
    intro j hj
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hj).1,
      lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 hnt⟩
  have hweight0 : ∀ j : ℤ,
      (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) := fun _ =>
    Real.rpow_nonneg h3.le _
  have htarget0 : ∀ r ∈ Finset.Ico jStar t,
      0 ≤ (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) * hold r := by
    intro r hr
    exact mul_nonneg (Real.rpow_nonneg h3.le _) (hold0 r hr)
  have hbuf0 : (0 : ℝ) ≤ (3 : ℝ) ^ (a * (l0 : ℝ)) :=
    Real.rpow_nonneg h3.le _
  have hbulk :
      ∑ j ∈ Finset.Icc jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hold j ≤
        (3 : ℝ) ^ (a * (l0 : ℝ)) *
          ∑ r ∈ Finset.Ico jStar t,
            (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) * hold r := by
    have heq :
        ∑ j ∈ Finset.Icc jStar n,
            (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hold j =
          (3 : ℝ) ^ (a * (l0 : ℝ)) *
            ∑ j ∈ Finset.Icc jStar n,
              (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (j : ℝ))) * hold j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hconv := bulk_convolution_eq (a := a) (l0 : ℝ) 0
        (n : ℝ) (t : ℝ) (j : ℝ) htR
      rw [hconv]
      ring_nf
    rw [heq]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsubJ
        (fun r hr _ => htarget0 r hr)) hbuf0
  have hrowSub : ∀ j ∈ Finset.Icc jStar n,
      Finset.Ico jStar j ⊆ Finset.Ico jStar t := by
    intro j hj r hr
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hr).1,
      lt_trans (Finset.mem_Ico.mp hr).2
        (lt_of_le_of_lt (Finset.mem_Icc.mp hj).2 hnt)⟩
  have hswap :
      ∑ j ∈ Finset.Icc jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            ∑ r ∈ Finset.Ico jStar j,
              (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r =
        ∑ r ∈ Finset.Ico jStar t,
          ∑ j ∈ (Finset.Icc jStar n).filter
              (fun j => r ∈ Finset.Ico jStar j),
            (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
              ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r) := by
    have hleft : ∀ j ∈ Finset.Icc jStar n,
        ∑ r ∈ Finset.Ico jStar j,
            (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
              ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r) =
          ∑ r ∈ Finset.Ico jStar t,
            if r ∈ Finset.Ico jStar j then
              (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
                ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r)
            else 0 := by
      intro j hj
      rw [Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr (hrowSub j hj)]
    calc
      ∑ j ∈ Finset.Icc jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            ∑ r ∈ Finset.Ico jStar j,
              (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r
          = ∑ j ∈ Finset.Icc jStar n,
              ∑ r ∈ Finset.Ico jStar j,
                (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
                  ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
                    hold r) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.Icc jStar n,
            ∑ r ∈ Finset.Ico jStar t,
              if r ∈ Finset.Ico jStar j then
                (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
                  ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
                    hold r)
              else 0 := Finset.sum_congr rfl hleft
      _ = ∑ r ∈ Finset.Ico jStar t,
            ∑ j ∈ Finset.Icc jStar n,
              if r ∈ Finset.Ico jStar j then
                (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
                  ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
                    hold r)
              else 0 := by rw [Finset.sum_comm]
      _ = _ := Finset.sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm
  have hboundary :
      ∑ j ∈ Finset.Icc jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            ∑ r ∈ Finset.Ico jStar j,
              (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r ≤
        (3 : ℝ) ^ (a * (l0 : ℝ)) *
          ((3 : ℝ) ^ (-(1 - g - a)) /
            (1 - (3 : ℝ) ^ (-(1 - g - a)))) *
          ∑ r ∈ Finset.Ico jStar t,
            (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) * hold r := by
    rw [hswap]
    have hterm : ∀ r ∈ Finset.Ico jStar t,
        (∑ j ∈ (Finset.Icc jStar n).filter
            (fun j => r ∈ Finset.Ico jStar j),
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            ((3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r)) ≤
          (3 : ℝ) ^ (a * (l0 : ℝ)) *
            ((3 : ℝ) ^ (-(1 - g - a)) /
              (1 - (3 : ℝ) ^ (-(1 - g - a)))) *
            ((3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) * hold r) := by
      intro r hr
      have hs : ∀ j ∈ (Finset.Icc jStar n).filter
          (fun j => r ∈ Finset.Ico jStar j), r + 1 ≤ j := by
        intro j hj
        exact Int.add_one_le_iff.mpr
          (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).2).2
      have hconv := boundary_convolution (a := a) (g := g) hahi ht 1 r
        ((Finset.Icc jStar n).filter fun j => r ∈ Finset.Ico jStar j) hs
      have hmul := mul_le_mul_of_nonneg_right hconv (hold0 r hr)
      rw [Finset.sum_mul] at hmul
      simpa only [Int.cast_one, mul_one, mul_assoc] using hmul
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
  have hweighted := Finset.sum_le_sum fun j hj =>
    mul_le_mul_of_nonneg_left (hrow j hj) (hweight0 j)
  refine hweighted.trans ?_
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hCboundary := mul_le_mul_of_nonneg_left hboundary hC
  calc
    (∑ j ∈ Finset.Icc jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * hold j) +
        ∑ j ∈ Finset.Icc jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
            (C * ∑ r ∈ Finset.Ico jStar j,
              (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r)
        ≤ (3 : ℝ) ^ (a * (l0 : ℝ)) *
              ∑ r ∈ Finset.Ico jStar t,
                (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) * hold r +
            C * ((3 : ℝ) ^ (a * (l0 : ℝ)) *
              ((3 : ℝ) ^ (-(1 - g - a)) /
                (1 - (3 : ℝ) ^ (-(1 - g - a)))) *
              ∑ r ∈ Finset.Ico jStar t,
                (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) * hold r) := by
          refine add_le_add hbulk ?_
          calc
            ∑ j ∈ Finset.Icc jStar n,
                (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
                  (C * ∑ r ∈ Finset.Ico jStar j,
                    (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
                      hold r)
                = C * ∑ j ∈ Finset.Icc jStar n,
                    (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
                      ∑ r ∈ Finset.Ico jStar j,
                        (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) *
                          hold r := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun j _ => by ring_nf
            _ ≤ _ := hCboundary
    _ = _ := by ring_nf

end

end Transport
end HighContrast
end Homogenization
