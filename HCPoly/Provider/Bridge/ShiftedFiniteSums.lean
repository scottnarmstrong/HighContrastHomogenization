/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.DiscreteConvolution

/-!
# Finite sums for the shifted determinant drift

This file reorganizes the principal and boundary sums in
`e.two.grid.drift.old.grid` and
`e.two.grid.whitney.drift.boundary`.  Both estimates retain every
finite endpoint.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

noncomputable section

private theorem sum_row_comm {f : ℤ → ℤ → ℝ} {s t : Finset ℤ}
    {v : ℤ → Finset ℤ} (hv : ∀ j ∈ s, v j ⊆ t) :
    ∑ j ∈ s, ∑ r ∈ v j, f j r =
      ∑ r ∈ t, ∑ j ∈ s.filter fun j ↦ r ∈ v j, f j r := by
  classical
  have hleft : ∀ j ∈ s,
      ∑ r ∈ v j, f j r = ∑ r ∈ t, if r ∈ v j then f j r else 0 := by
    intro j hj
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hv j hj)]
  rw [Finset.sum_congr rfl hleft, Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ ↦ (Finset.sum_filter _ _).symm

private theorem shifted_tail_sum_le {rho : ℝ} (hrho : 0 < rho) {b T : ℤ}
    (x : ℤ → ℝ) (hx : ∀ r ∈ Finset.Icc (b + 1) T, 0 ≤ x r)
    (s : Finset ℤ) (hs : ∀ a ∈ s, b ≤ a) :
    ∑ a ∈ s, (3 : ℝ) ^ (-rho * ((T : ℝ) - 1 - (a : ℝ))) *
        ∑ r ∈ Finset.Icc (a + 1) T, x r ≤
      1 / (1 - (3 : ℝ) ^ (-rho)) *
        ∑ r ∈ Finset.Icc (b + 1) T,
          (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) * x r := by
  classical
  have hsub : ∀ a ∈ s, Finset.Icc (a + 1) T ⊆ Finset.Icc (b + 1) T := by
    intro a ha r hr
    rw [Finset.mem_Icc] at hr ⊢
    have hab := hs a ha
    exact ⟨by omega, hr.2⟩
  have hswap :
      ∑ a ∈ s, (3 : ℝ) ^ (-rho * ((T : ℝ) - 1 - (a : ℝ))) *
          ∑ r ∈ Finset.Icc (a + 1) T, x r =
        ∑ r ∈ Finset.Icc (b + 1) T,
          ∑ a ∈ s.filter fun a ↦ r ∈ Finset.Icc (a + 1) T,
            (3 : ℝ) ^ (-rho * ((T : ℝ) - 1 - (a : ℝ))) * x r := by
    rw [← sum_row_comm
      (f := fun a r ↦
        (3 : ℝ) ^ (-rho * ((T : ℝ) - 1 - (a : ℝ))) * x r) hsub]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [Finset.mul_sum]
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr ↦ ?_
  have hr0 : 0 ≤ x r := hx r hr
  rw [← Finset.sum_mul]
  have hbelow : ∀ a ∈ s.filter fun a ↦ r ∈ Finset.Icc (a + 1) T,
      a ≤ r - 1 := by
    intro a ha
    have har := (Finset.mem_filter.mp ha).2
    have := (Finset.mem_Icc.mp har).1
    omega
  have hgeom := Transport.sum_geom_below_le hrho (r - 1)
    (s.filter fun a ↦ r ∈ Finset.Icc (a + 1) T) hbelow
  have hfactor : ∀ a ∈ s.filter fun a ↦ r ∈ Finset.Icc (a + 1) T,
      (3 : ℝ) ^ (-rho * ((T : ℝ) - 1 - (a : ℝ))) =
        (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) *
          (3 : ℝ) ^ (-rho * (((r - 1 : ℤ) : ℝ) - (a : ℝ))) := by
    intro a _
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  have hcoeff :
      (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) *
          ∑ a ∈ s.filter fun a ↦ r ∈ Finset.Icc (a + 1) T,
            (3 : ℝ) ^ (-rho * (((r - 1 : ℤ) : ℝ) - (a : ℝ))) ≤
        1 / (1 - (3 : ℝ) ^ (-rho)) *
          (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) := by
    calc
      (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) *
            ∑ a ∈ s.filter fun a ↦ r ∈ Finset.Icc (a + 1) T,
              (3 : ℝ) ^ (-rho * (((r - 1 : ℤ) : ℝ) - (a : ℝ)))
          ≤ (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) *
              (1 / (1 - (3 : ℝ) ^ (-rho))) :=
            mul_le_mul_of_nonneg_left hgeom (Real.rpow_nonneg (by norm_num) _)
      _ = 1 / (1 - (3 : ℝ) ^ (-rho)) *
            (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) := by ring_nf
  have hmul := mul_le_mul_of_nonneg_right hcoeff hr0
  exact hmul.trans_eq (by ring_nf)

/-- The shifted principal means are bounded by the terminal weighted drift,
with the exact geometric-series constant. -/
theorem shifted_main_sum_le {rho : ℝ} (hrho : 0 < rho) {b n l : ℤ}
    (x : ℤ → ℝ)
    (hx : ∀ r ∈ Finset.Icc (b + 1) (n + l), 0 ≤ x r) :
    ∑ j ∈ Finset.Ico (b + l) n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          ∑ r ∈ Finset.Icc (j - l + 1) (n + l), x r ≤
      1 / (1 - (3 : ℝ) ^ (-rho)) *
        (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
          ∑ r ∈ Finset.Icc (b + 1) (n + l),
            (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ))) * x r := by
  classical
  have hsub : ∀ j ∈ Finset.Ico (b + l) n,
      Finset.Icc (j - l + 1) (n + l) ⊆ Finset.Icc (b + 1) (n + l) := by
    intro j hj r hr
    rw [Finset.mem_Icc] at hr ⊢
    have hjlo := (Finset.mem_Ico.mp hj).1
    exact ⟨by omega, hr.2⟩
  have hswap :
      ∑ j ∈ Finset.Ico (b + l) n,
          (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
            ∑ r ∈ Finset.Icc (j - l + 1) (n + l), x r =
        ∑ r ∈ Finset.Icc (b + 1) (n + l),
          ∑ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
              r ∈ Finset.Icc (j - l + 1) (n + l),
            (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) * x r := by
    rw [← sum_row_comm
      (f := fun j r ↦
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) * x r) hsub]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr ↦ ?_
  have hr0 : 0 ≤ x r := hx r hr
  rw [← Finset.sum_mul]
  have hbelow : ∀ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
      r ∈ Finset.Icc (j - l + 1) (n + l), j ≤ r + l - 1 := by
    intro j hj
    have hjr := (Finset.mem_filter.mp hj).2
    have := (Finset.mem_Icc.mp hjr).1
    omega
  have hgeom := Transport.sum_geom_below_le hrho (r + l - 1)
    ((Finset.Ico (b + l) n).filter fun j ↦
      r ∈ Finset.Icc (j - l + 1) (n + l)) hbelow
  have hfactor : ∀ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
      r ∈ Finset.Icc (j - l + 1) (n + l),
      (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) =
        ((3 : ℝ) ^ (2 * rho * (l : ℝ)) *
          (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ)))) *
            (3 : ℝ) ^ (-rho * (((r + l - 1 : ℤ) : ℝ) - (j : ℝ))) := by
    intro j _
    simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  have hcoeff :
      ((3 : ℝ) ^ (2 * rho * (l : ℝ)) *
          (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ)))) *
          ∑ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
              r ∈ Finset.Icc (j - l + 1) (n + l),
            (3 : ℝ) ^ (-rho * (((r + l - 1 : ℤ) : ℝ) - (j : ℝ))) ≤
        1 / (1 - (3 : ℝ) ^ (-rho)) *
          (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
            (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ))) := by
    calc
      ((3 : ℝ) ^ (2 * rho * (l : ℝ)) *
            (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ)))) *
            ∑ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
                r ∈ Finset.Icc (j - l + 1) (n + l),
              (3 : ℝ) ^ (-rho * (((r + l - 1 : ℤ) : ℝ) - (j : ℝ)))
          ≤ ((3 : ℝ) ^ (2 * rho * (l : ℝ)) *
              (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ)))) *
                (1 / (1 - (3 : ℝ) ^ (-rho))) :=
            mul_le_mul_of_nonneg_left hgeom
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                (Real.rpow_nonneg (by norm_num) _))
      _ = 1 / (1 - (3 : ℝ) ^ (-rho)) *
            (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
              (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ))) := by ring_nf
  have hmul := mul_le_mul_of_nonneg_right hcoeff hr0
  exact hmul.trans_eq (by ring_nf)

/-- The shifted boundary rows are bounded by the terminal weighted drift.  The
constant is the product of the two geometric-series masses. -/
theorem shifted_boundary_sum_le {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1)
    {b n l : ℤ} (hl : 0 ≤ l) (x : ℤ → ℝ)
    (hx : ∀ r ∈ Finset.Icc (b + 1) (n + l), 0 ≤ x r) :
    ∑ j ∈ Finset.Ico (b + l) n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          ∑ a ∈ Finset.Icc b (j - l),
            (3 : ℝ) ^ (((a : ℝ) - (j : ℝ))) *
              ∑ r ∈ Finset.Icc (a + 1) (n + l), x r ≤
      (1 / (1 - (3 : ℝ) ^ (-rho)) *
          (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
        (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
          ∑ r ∈ Finset.Icc (b + 1) (n + l),
            (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ))) * x r := by
  classical
  let A : Finset ℤ := Finset.Icc b (n - l)
  have hsub : ∀ j ∈ Finset.Ico (b + l) n, Finset.Icc b (j - l) ⊆ A := by
    intro j hj a ha
    rw [Finset.mem_Icc] at ha
    rw [show A = Finset.Icc b (n - l) by rfl, Finset.mem_Icc]
    exact ⟨ha.1, by have := (Finset.mem_Ico.mp hj).2; omega⟩
  have hswap :
      ∑ j ∈ Finset.Ico (b + l) n,
          (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
            ∑ a ∈ Finset.Icc b (j - l),
              (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) *
                ∑ r ∈ Finset.Icc (a + 1) (n + l), x r =
        ∑ a ∈ A,
          ∑ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
              a ∈ Finset.Icc b (j - l),
            ((3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
              (3 : ℝ) ^ ((a : ℝ) - (j : ℝ))) *
                ∑ r ∈ Finset.Icc (a + 1) (n + l), x r := by
    rw [← sum_row_comm
      (f := fun j a ↦
        ((3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          (3 : ℝ) ^ ((a : ℝ) - (j : ℝ))) *
            ∑ r ∈ Finset.Icc (a + 1) (n + l), x r) hsub]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by ring_nf
  rw [hswap]
  have hA : ∀ a ∈ A, b ≤ a := by
    intro a ha
    rw [show A = Finset.Icc b (n - l) by rfl, Finset.mem_Icc] at ha
    exact ha.1
  have htail0 : ∀ a ∈ A, 0 ≤ ∑ r ∈ Finset.Icc (a + 1) (n + l), x r := by
    intro a ha
    exact Finset.sum_nonneg fun r hr ↦ hx r <| by
      rw [Finset.mem_Icc] at hr ⊢
      have hab := hA a ha
      exact ⟨by omega, hr.2⟩
  have hrows : ∀ a ∈ A,
      ∑ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
          a ∈ Finset.Icc b (j - l),
        ((3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          (3 : ℝ) ^ ((a : ℝ) - (j : ℝ))) *
            ∑ r ∈ Finset.Icc (a + 1) (n + l), x r ≤
      ((3 : ℝ) ^ (rho * (l : ℝ)) *
          ((3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) /
            (1 - (3 : ℝ) ^ (-(1 - rho))))) *
        ((3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - 1 - (a : ℝ))) *
          ∑ r ∈ Finset.Icc (a + 1) (n + l), x r) := by
    intro a ha
    rw [← Finset.sum_mul]
    have htargets : ∀ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
        a ∈ Finset.Icc b (j - l), a + l ≤ j := by
      intro j hj
      have haj := (Finset.mem_filter.mp hj).2
      have := (Finset.mem_Icc.mp haj).2
      omega
    have hconv := Transport.boundary_convolution (a := rho) (g := 0) (by linarith only [hrho1])
      (l0 := l) (n := n) (t := n + l) rfl l a
      ((Finset.Ico (b + l) n).filter fun j ↦ a ∈ Finset.Icc b (j - l)) htargets
    have hkernel : ∀ j ∈ (Finset.Ico (b + l) n).filter fun j ↦
        a ∈ Finset.Icc b (j - l),
        (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) =
          (3 : ℝ) ^ (-(1 - (0 : ℝ)) * ((j : ℝ) - (a : ℝ))) := by
      intro j _
      congr 1
      ring_nf
    rw [Finset.sum_congr rfl fun j hj ↦ by rw [hkernel j hj]]
    have hmul := mul_le_mul_of_nonneg_right hconv (htail0 a ha)
    exact hmul.trans_eq (by ring_nf)
  refine le_trans (Finset.sum_le_sum hrows) ?_
  rw [← Finset.mul_sum]
  have htail := shifted_tail_sum_le hrho x hx A hA
  have hrowFactor0 : 0 ≤ (3 : ℝ) ^ (rho * (l : ℝ)) *
      ((3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) /
        (1 - (3 : ℝ) ^ (-(1 - rho)))) := by
    have hratio : (3 : ℝ) ^ (-(1 - rho)) < 1 :=
      PortableHistory.geom_ratio_lt_one (by linarith only [hrho1])
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hratio.le))
  have hstep := mul_le_mul_of_nonneg_left htail hrowFactor0
  refine hstep.trans ?_
  have hgeom0 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-rho)) := by
    have hratio := PortableHistory.geom_ratio_lt_one hrho
    exact div_nonneg zero_le_one (sub_nonneg.mpr hratio.le)
  have hgeom1 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 - rho))) := by
    have hratio : (3 : ℝ) ^ (-(1 - rho)) < 1 :=
      PortableHistory.geom_ratio_lt_one (by linarith only [hrho1])
    exact div_nonneg zero_le_one (sub_nonneg.mpr hratio.le)
  have hbuffer :
      (3 : ℝ) ^ (rho * (l : ℝ)) * (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) ≤
        (3 : ℝ) ^ (2 * rho * (l : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hlR : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    calc
      rho * (l : ℝ) + -(1 - rho) * (l : ℝ) =
          2 * rho * (l : ℝ) - (l : ℝ) := by ring_nf
      _ ≤ 2 * rho * (l : ℝ) := sub_le_self _ hlR
  have hsum0 : 0 ≤ ∑ r ∈ Finset.Icc (b + 1) (n + l),
      (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ))) * x r :=
    Finset.sum_nonneg fun r hr ↦
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hx r hr)
  have hfactor := mul_le_mul_of_nonneg_left hbuffer (mul_nonneg hgeom0 hgeom1)
  have hfactor' :
      ((3 : ℝ) ^ (rho * (l : ℝ)) *
          ((3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) /
            (1 - (3 : ℝ) ^ (-(1 - rho))))) *
          (1 / (1 - (3 : ℝ) ^ (-rho))) ≤
        (1 / (1 - (3 : ℝ) ^ (-rho)) *
          (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
            (3 : ℝ) ^ (2 * rho * (l : ℝ)) := by
    calc
      ((3 : ℝ) ^ (rho * (l : ℝ)) *
            ((3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) /
              (1 - (3 : ℝ) ^ (-(1 - rho))))) *
            (1 / (1 - (3 : ℝ) ^ (-rho))) =
          (1 / (1 - (3 : ℝ) ^ (-rho)) *
            (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
              ((3 : ℝ) ^ (rho * (l : ℝ)) *
                (3 : ℝ) ^ (-(1 - rho) * (l : ℝ))) := by ring_nf
      _ ≤ (1 / (1 - (3 : ℝ) ^ (-rho)) *
            (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
              (3 : ℝ) ^ (2 * rho * (l : ℝ)) := hfactor
  have hmul := mul_le_mul_of_nonneg_right hfactor' hsum0
  calc
    (3 : ℝ) ^ (rho * (l : ℝ)) *
          ((3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) /
            (1 - (3 : ℝ) ^ (-(1 - rho)))) *
        (1 / (1 - (3 : ℝ) ^ (-rho)) *
          ∑ r ∈ Finset.Icc (b + 1) (n + l),
            (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ))) * x r)
        = (((3 : ℝ) ^ (rho * (l : ℝ)) *
              ((3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) /
                (1 - (3 : ℝ) ^ (-(1 - rho))))) *
              (1 / (1 - (3 : ℝ) ^ (-rho)))) *
            ∑ r ∈ Finset.Icc (b + 1) (n + l),
              (3 : ℝ) ^ (-rho * (((n + l : ℤ) : ℝ) - (r : ℝ))) * x r := by ring_nf
    _ ≤ _ := hmul

end

end Bridge
end HighContrast
end Homogenization
