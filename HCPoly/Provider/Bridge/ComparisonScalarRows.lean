/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.BridgeNormalization
import HCPoly.Provider.Bridge.DecaySums

/-!
# Finite scalar rows for two-grid comparison

The boundary weight of a maximal filling is summed before the increments of the
terminal mean.  Exchanging these two finite sums produces the maximum of the
grid separation and the distance from the terminal scale.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

noncomputable section

private theorem sum_row_comm {f : ℤ → ℤ → ℝ} {s R : Finset ℤ} {T : ℤ}
    (hsub : ∀ a ∈ s, Finset.Icc (a + 1) T ⊆ R) :
    ∑ a ∈ s, ∑ r ∈ Finset.Icc (a + 1) T, f a r =
      ∑ r ∈ R, ∑ a ∈ s.filter fun a => r ∈ Finset.Icc (a + 1) T, f a r := by
  classical
  have hleft : ∀ a ∈ s,
      ∑ r ∈ Finset.Icc (a + 1) T, f a r =
        ∑ r ∈ R, if r ∈ Finset.Icc (a + 1) T then f a r else 0 := by
    intro a ha
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub a ha)]
  rw [Finset.sum_congr rfl hleft, Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => (Finset.sum_filter _ _).symm

/-- A finite set of integer scales below `u` has the corresponding geometric
mass, measured relative to a terminal scale `T`. -/
theorem sum_zpow_sub_le_geom {u T : ℤ} (s : Finset ℤ)
    (hs : ∀ a ∈ s, a ≤ u) :
    ∑ a ∈ s, (3 : ℝ) ^ (a - T) ≤
      (3 : ℝ) ^ ((u : ℝ) - (T : ℝ)) *
        (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) := by
  have hgeom := Transport.sum_geom_below_le (c := (1 : ℝ)) one_pos u s hs
  have hfactor : ∀ a ∈ s,
      (3 : ℝ) ^ (a - T) =
        (3 : ℝ) ^ ((u : ℝ) - (T : ℝ)) *
          (3 : ℝ) ^ (-((u : ℝ) - (a : ℝ))) := by
    intro a _
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  have hgeom' : ∑ j ∈ s, (3 : ℝ) ^ (-((u : ℝ) - (j : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))) := by
    simpa only [neg_mul, one_mul] using hgeom
  exact mul_le_mul_of_nonneg_left hgeom' (Real.rpow_nonneg (by norm_num) _)

/-- The weighted tails of a boundary row are controlled by the terminal
weighted increment row. -/
theorem weighted_tail_sum_le {rho D K : ℝ} {b T l : ℤ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hDK : 0 ≤ D * K) (theta x : ℤ → ℝ)
    (htheta : ∀ a ∈ Finset.Icc b (T - l),
      theta a ≤ D * K * (3 : ℝ) ^ (a - T))
    (hx : ∀ r ∈ Finset.Icc (b + 1) T, 0 ≤ x r) :
    ∑ a ∈ Finset.Icc b (T - l), theta a *
        ∑ r ∈ Finset.Icc (a + 1) T, x r ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * K *
        (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
          ∑ r ∈ Finset.Icc (b + 1) T,
            (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) * x r := by
  classical
  let A : Finset ℤ := Finset.Icc b (T - l)
  let R : Finset ℤ := Finset.Icc (b + 1) T
  have hsub : ∀ a ∈ A, Finset.Icc (a + 1) T ⊆ R := by
    intro a ha r hr
    rw [show A = Finset.Icc b (T - l) by rfl, Finset.mem_Icc] at ha
    rw [Finset.mem_Icc] at hr
    change r ∈ Finset.Icc (b + 1) T
    rw [Finset.mem_Icc]
    exact ⟨by omega, hr.2⟩
  have hswap :
      ∑ a ∈ A, theta a * ∑ r ∈ Finset.Icc (a + 1) T, x r =
        ∑ r ∈ R, ∑ a ∈ A.filter fun a => r ∈ Finset.Icc (a + 1) T,
          theta a * x r := by
    rw [← sum_row_comm
      (f := fun a r => theta a * x r) hsub]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  change (∑ a ∈ A, theta a * ∑ r ∈ Finset.Icc (a + 1) T, x r) ≤ _
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hrange : b + 1 ≤ r ∧ r ≤ T := by
    simpa only [R, Finset.mem_Icc] using hr
  have hxr : 0 ≤ x r := hx r (by simpa only [R] using hr)
  rw [← Finset.sum_mul]
  let Ar : Finset ℤ := A.filter fun a => r ∈ Finset.Icc (a + 1) T
  have hArA : Ar ⊆ A := Finset.filter_subset _ _
  have hthetaAr : ∀ a ∈ Ar,
      theta a ≤ D * K * (3 : ℝ) ^ (a - T) := by
    intro a ha
    exact htheta a <| by
      simpa only [A] using hArA ha
  have hsumtheta : ∑ a ∈ Ar, theta a ≤
      D * K * ∑ a ∈ Ar, (3 : ℝ) ^ (a - T) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hthetaAr
  have hpower : ∑ a ∈ Ar, (3 : ℝ) ^ (a - T) ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
        (3 : ℝ) ^ (-max (l : ℝ) ((T : ℝ) - (r : ℝ))) := by
    by_cases hrl : r ≤ T - l
    · have hbelow : ∀ a ∈ Ar, a ≤ r - 1 := by
        intro a ha
        have har := (Finset.mem_filter.mp ha).2
        rw [Finset.mem_Icc] at har
        omega
      have hgeom := sum_zpow_sub_le_geom (T := T) Ar hbelow
      have hrlR : (l : ℝ) ≤ (T : ℝ) - (r : ℝ) := by exact_mod_cast (by omega : l ≤ T - r)
      have hpow : (3 : ℝ) ^ (((r - 1 : ℤ) : ℝ) - (T : ℝ)) ≤
          (3 : ℝ) ^ (-max (l : ℝ) ((T : ℝ) - (r : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        rw [max_eq_right hrlR]
        push_cast
        norm_num
      calc
        ∑ a ∈ Ar, (3 : ℝ) ^ (a - T) ≤
            (3 : ℝ) ^ (((r - 1 : ℤ) : ℝ) - (T : ℝ)) *
              (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) := hgeom
        _ ≤ (3 : ℝ) ^ (-max (l : ℝ) ((T : ℝ) - (r : ℝ))) *
              (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) := by
          exact mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = _ := by ring
    · have hbelow : ∀ a ∈ Ar, a ≤ T - l := by
        intro a ha
        exact (Finset.mem_Icc.mp <| by simpa only [A] using hArA ha).2
      have hgeom := sum_zpow_sub_le_geom (T := T) Ar hbelow
      have hrlR : (T : ℝ) - (r : ℝ) ≤ (l : ℝ) := by
        have : T - r ≤ l := by omega
        exact_mod_cast this
      have hpow : (3 : ℝ) ^ (((T - l : ℤ) : ℝ) - (T : ℝ)) =
          (3 : ℝ) ^ (-max (l : ℝ) ((T : ℝ) - (r : ℝ))) := by
        rw [max_eq_left hrlR]
        congr 1
        push_cast
        ring
      calc
        ∑ a ∈ Ar, (3 : ℝ) ^ (a - T) ≤
            (3 : ℝ) ^ (((T - l : ℤ) : ℝ) - (T : ℝ)) *
              (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) := hgeom
        _ = (3 : ℝ) ^ (-max (l : ℝ) ((T : ℝ) - (r : ℝ))) *
              (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) := by rw [hpow]
        _ = _ := by ring
  have hsplit := rpow_neg_max_le_split hrho0 hrho1
    (l := (l : ℝ)) (x := (T : ℝ) - (r : ℝ))
  have hgeom0 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))) := by positivity
  have hcoeff : ∑ a ∈ Ar, theta a ≤
      (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * K *
        (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
          (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) := by
    have h1 := hsumtheta.trans <|
      mul_le_mul_of_nonneg_left hpower hDK
    have h2 := mul_le_mul_of_nonneg_left hsplit
      (mul_nonneg hDK hgeom0)
    nlinarith only [h1, h2]
  change (∑ a ∈ Ar, theta a) * x r ≤ _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff hxr

end

end Bridge
end HighContrast
end Homogenization
