/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredAncestor

/-!
# Uniform inherited-row envelope

The maximal filling is run through the target scale.  Its rows at or below a
checkpoint still obey the envelope needed by the pathwise inherited supremum:
the top row is paid by total mass, and every lower row by codimension-one
decay.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

noncomputable section

/-- The checkpoint-truncated mass of an unshifted filling has the uniform
`3^{rhoMax (b-j)}` envelope. -/
theorem inherited_row_mass_envelope {rhoMax C : ℝ}
    (hrho1 : rhoMax < 1) {jStar b j : ℤ} (hjj : jStar ≤ j)
    {m : ℤ → ℝ} (hm0 : ∀ r, 0 ≤ m r)
    (hmass : ∑ r ∈ Finset.Icc jStar j, m r ≤ 1)
    (hrow : ∀ r ∈ Finset.Icc jStar j, r < j →
      m r ≤ C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ))) :
    ∑ r ∈ Finset.Icc jStar (min b j),
        m r * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) ≤
      max 1 C * (1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax)))) *
        (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ))) := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hD0 : (0 : ℝ) ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have hCD : C ≤ max 1 C := le_max_right _ _
  have hden0 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax))) := by
    have hr := PortableHistory.geom_ratio_lt_one (by linarith only [hrho1] : 0 < 1 - rhoMax)
    exact (one_div_pos.mpr (sub_pos.mpr hr)).le
  by_cases hjb' : j ≤ b
  · rw [min_eq_right hjb']
    have hpoint : ∀ r ∈ Finset.Icc jStar j,
        m r ≤ max 1 C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
      intro r hr
      rcases lt_or_eq_of_le (Finset.mem_Icc.mp hr).2 with hrj | hrj
      · exact (hrow r hr hrj).trans
          (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg h3.le _))
      · subst r
        rw [sub_self, Real.rpow_zero, mul_one]
        have hmj : m j ≤ ∑ r ∈ Finset.Icc jStar j, m r :=
          Finset.single_le_sum (fun r _ => hm0 r) (Finset.mem_Icc.mpr ⟨hjj, le_rfl⟩)
        exact hmj.trans hmass |>.trans (le_max_left _ _)
    have hsum :
        ∑ r ∈ Finset.Icc jStar j,
            m r * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) ≤
          max 1 C * ∑ r ∈ Finset.Icc jStar j,
            (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) *
              (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r hr => ?_
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right (hpoint r hr) (Real.rpow_nonneg h3.le _))
    refine hsum.trans ?_
    have ha := ancestor_row_le hrho1 jStar b j 0
    simp only [sub_zero, Int.cast_zero, mul_zero, Real.rpow_zero, mul_one] at ha
    have hm := mul_le_mul_of_nonneg_left ha hD0
    linarith only [hm]
  · have hbj' : b < j := lt_of_not_ge hjb'
    rw [min_eq_left hbj'.le]
    have hpoint : ∀ r ∈ Finset.Icc jStar b,
        m r ≤ max 1 C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) := by
      intro r hr
      have hrj : r < j := lt_of_le_of_lt (Finset.mem_Icc.mp hr).2 hbj'
      have hr' : r ∈ Finset.Icc jStar j :=
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hrj.le⟩
      exact (hrow r hr' hrj).trans
        (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg h3.le _))
    have hsum :
        ∑ r ∈ Finset.Icc jStar b,
            m r * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) ≤
          max 1 C * ∑ r ∈ Finset.Icc jStar b,
            (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)) *
              (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r hr => ?_
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right (hpoint r hr) (Real.rpow_nonneg h3.le _))
    refine hsum.trans ?_
    have ha := ancestor_sum_le hrho1 jStar b j
    have hm := mul_le_mul_of_nonneg_left ha hD0
    have hexp : (b : ℝ) - (j : ℝ) ≤ rhoMax * ((b : ℝ) - (j : ℝ)) := by
      have hrhoLe : rhoMax ≤ 1 := hrho1.le
      have hbjR' : (b : ℝ) < (j : ℝ) := by exact_mod_cast hbj'
      have hbjR : (b : ℝ) - (j : ℝ) < 0 := by linarith only [hbjR']
      nlinarith only [hrhoLe, hbjR]
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hmul := mul_le_mul_of_nonneg_left hp (mul_nonneg hD0 hden0)
    linarith only [hm, hmul]

end

end Transport
end HighContrast
end Homogenization
