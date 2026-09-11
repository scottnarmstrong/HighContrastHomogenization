/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ComparisonScalarRows
import HCPoly.Provider.Bridge.DecaySums

/-!
# Auxiliary shifted geometric sums

These estimates retain the integer endpoints used by the early, continued,
and boundary-mass parts of the shifted determinant drift.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

noncomputable section

/-- The backward shifted weights have at most their infinite geometric mass. -/
theorem shifted_weight_sum_le {rho : ℝ} (hrho : 0 < rho) {b n : ℤ} :
    ∑ j ∈ Finset.Ico b n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-rho)) := by
  have hbelow : ∀ j ∈ Finset.Ico b n, j ≤ n - 1 := by
    intro j hj
    exact by have := (Finset.mem_Ico.mp hj).2; omega
  have h := Transport.sum_geom_below_le hrho (n - 1) (Finset.Ico b n) hbelow
  simpa only [Int.cast_sub, Int.cast_one] using h

/-- The boundary-volume part of all continued shifted rows has one separation
factor and the product of the two geometric masses. -/
theorem shifted_boundary_mass_sum_le {rho : ℝ} (hrho : 0 < rho)
    {b n l : ℤ} :
    ∑ j ∈ Finset.Ico (b + l) n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          ∑ a ∈ Finset.Icc b (j - l - 1),
            (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) ≤
      (1 / (1 - (3 : ℝ) ^ (-rho))) *
        (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
          (3 : ℝ) ^ (-(l : ℝ)) := by
  have hinner : ∀ j ∈ Finset.Ico (b + l) n,
      ∑ a ∈ Finset.Icc b (j - l - 1),
          (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) ≤
        (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
          (3 : ℝ) ^ (-(l : ℝ)) := by
    intro j _
    have hgeom := sum_zpow_sub_le_geom (T := j)
      (Finset.Icc b (j - l - 1)) (fun a ha => (Finset.mem_Icc.mp ha).2)
    have hpow : (3 : ℝ) ^ (((j - l - 1 : ℤ) : ℝ) - (j : ℝ)) ≤
        (3 : ℝ) ^ (-(l : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      push_cast
      ring_nf
      norm_num
    have hG0 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))) := by positivity
    have hpowCast : ∀ a : ℤ,
        (3 : ℝ) ^ (a - j) = (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) := by
      intro a
      simpa only [Int.cast_sub] using (Real.rpow_intCast (3 : ℝ) (a - j)).symm
    calc
      ∑ a ∈ Finset.Icc b (j - l - 1),
            (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) =
          ∑ a ∈ Finset.Icc b (j - l - 1), (3 : ℝ) ^ (a - j) :=
        Finset.sum_congr rfl fun a _ => (hpowCast a).symm
      _ ≤
          (3 : ℝ) ^ (((j - l - 1 : ℤ) : ℝ) - (j : ℝ)) *
            (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) := hgeom
      _ ≤ (3 : ℝ) ^ (-(l : ℝ)) *
            (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) :=
        mul_le_mul_of_nonneg_right hpow hG0
      _ = _ := by ring
  have hrow :
      ∑ j ∈ Finset.Ico (b + l) n,
          (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
            ∑ a ∈ Finset.Icc b (j - l - 1),
              (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) ≤
        ∑ j ∈ Finset.Ico (b + l) n,
          (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
            ((1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
              (3 : ℝ) ^ (-(l : ℝ))) :=
    Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (hinner j hj) (Real.rpow_nonneg (by norm_num) _)
  refine hrow.trans ?_
  rw [← Finset.sum_mul]
  have hweights := shifted_weight_sum_le hrho (b := b + l) (n := n)
  have hfactor0 : 0 ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
        (3 : ℝ) ^ (-(l : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hweights hfactor0
  simpa only [mul_assoc] using hmul

/-- The early shifted levels fit the common shifted source envelope. -/
theorem shifted_early_weight_sum_le {rho : ℝ} (hrho : 0 < rho)
    {b n l : ℤ} (hl : 0 ≤ l) (hbln : b + l ≤ n) :
    ∑ j ∈ Finset.Ico b (b + l),
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) ≤
      (1 + ((n : ℝ) - (b : ℝ))) *
        (3 : ℝ) ^ (rho * (l : ℝ)) *
          (3 : ℝ) ^ (-rho * ((n : ℝ) - (b : ℝ))) := by
  let N : ℤ := n - b
  let envelope : ℝ := (3 : ℝ) ^ (rho * (l : ℝ)) *
    (3 : ℝ) ^ (-rho * (N : ℝ))
  have hpoint : ∀ j ∈ Finset.Ico b (b + l),
      (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) ≤ envelope := by
    intro j hj
    have hjtop := (Finset.mem_Ico.mp hj).2
    have hexp : -rho * ((n : ℝ) - 1 - (j : ℝ)) ≤
        rho * (l : ℝ) + -rho * (N : ℝ) := by
      have hjR : (j : ℝ) ≤ (b : ℝ) + (l : ℝ) - 1 := by
        exact_mod_cast (by omega : j ≤ b + l - 1)
      dsimp only [N]
      push_cast
      nlinarith only [hrho, hjR]
    calc
      (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) ≤
          (3 : ℝ) ^ (rho * (l : ℝ) + -rho * (N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = envelope := by
        dsimp only [envelope]
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hsum := Finset.sum_le_card_nsmul _ _ _ hpoint
  have hcard : (Finset.Ico b (b + l)).card = l.toNat := by
    rw [Int.card_Ico]
    congr 1
    ring
  have hlcast : ((l.toNat : ℕ) : ℝ) = (l : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hl
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by
    have : 0 ≤ N := by dsimp only [N]; omega
    exact_mod_cast this
  have hlN : (l : ℝ) ≤ (N : ℝ) := by
    have : l ≤ N := by dsimp only [N]; omega
    exact_mod_cast this
  have henv0 : 0 ≤ envelope := by dsimp only [envelope]; positivity
  rw [hcard, nsmul_eq_mul, hlcast] at hsum
  calc
    _ ≤ (l : ℝ) * envelope := hsum
    _ ≤ (1 + (N : ℝ)) * envelope :=
      mul_le_mul_of_nonneg_right (by linarith only [hlN]) henv0
    _ = _ := by
      dsimp only [N, envelope]
      push_cast
      ring

/-- All continued shifted source rows fit the same common envelope. -/
theorem shifted_continued_source_sum_le {rho a : ℝ} (hrho : 0 < rho)
    (hrhoa : rho ≤ a) {b n l : ℤ} (hl : 1 ≤ l) (hbln : b + l ≤ n) :
    ∑ j ∈ Finset.Ico (b + l) n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          (3 : ℝ) ^ (-a * ((j : ℝ) - (b : ℝ))) ≤
      (1 + ((n : ℝ) - (b : ℝ))) *
        (3 : ℝ) ^ (rho * (l : ℝ)) *
          (3 : ℝ) ^ (-rho * ((n : ℝ) - (b : ℝ))) := by
  let N : ℤ := n - b
  let envelope : ℝ := (3 : ℝ) ^ (rho * (l : ℝ)) *
    (3 : ℝ) ^ (-rho * (N : ℝ))
  have hpoint : ∀ j ∈ Finset.Ico (b + l) n,
      (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          (3 : ℝ) ^ (-a * ((j : ℝ) - (b : ℝ))) ≤ envelope := by
    intro j hj
    have hls : l ≤ j - b := by have := (Finset.mem_Ico.mp hj).1; omega
    have hterm := source_convolution_term_le hrho.le hrhoa hl hls
      (N := N) (s := j - b)
    dsimp only [N, envelope] at hterm ⊢
    convert hterm using 1
    all_goals push_cast; ring_nf
  have hsum := Finset.sum_le_card_nsmul _ _ _ hpoint
  have hcard : (Finset.Ico (b + l) n).card = (n - (b + l)).toNat := by
    rw [Int.card_Ico]
  have hdiff0 : 0 ≤ n - (b + l) := by omega
  have hcast : ((((n - (b + l)).toNat : ℕ) : ℝ)) =
      (n : ℝ) - ((b : ℝ) + (l : ℝ)) := by
    exact_mod_cast Int.toNat_of_nonneg hdiff0
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by
    have : 0 ≤ N := by dsimp only [N]; omega
    exact_mod_cast this
  have henv0 : 0 ≤ envelope := by dsimp only [envelope]; positivity
  rw [hcard, nsmul_eq_mul, hcast] at hsum
  calc
    _ ≤ ((n : ℝ) - ((b : ℝ) + (l : ℝ))) * envelope := hsum
    _ ≤ (1 + (N : ℝ)) * envelope := by
      apply mul_le_mul_of_nonneg_right _ henv0
      dsimp only [N]
      push_cast
      have hlR : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast le_trans (by omega) hl
      linarith only [hlR]
    _ = _ := by
      dsimp only [N, envelope]
      push_cast
      ring

end

end Bridge
end HighContrast
end Homogenization
