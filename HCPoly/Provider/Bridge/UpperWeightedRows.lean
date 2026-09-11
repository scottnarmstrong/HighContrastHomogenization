/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ComparisonMatrixRows

/-!
# Endpoint-aware upper comparison rows

The last cell row of the upper filling carries only the unit volume budget.
All earlier rows have geometric decay and are compared with the terminal mean
through the weighted determinant drift.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- A weighted decreasing row is bounded by its undecayed endpoint together
with the geometrically decaying earlier rows. -/
theorem weighted_mean_row_with_endpoint_le {rho D K : ℝ} {b T l : ℤ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) (hl : 0 ≤ l)
    (hbTl : b ≤ T - l) (hDK : 0 ≤ D * K)
    (F : ℤ → FullBlockMat d) (theta : ℤ → ℝ)
    (hpos : ∀ r ∈ Finset.Icc b T, (F r).PosDef)
    (hmono : ∀ r ∈ Finset.Icc (b + 1) T, F r ≤ F (r - 1))
    (hterminal : ∀ a ∈ Finset.Icc b (T - l - 1), F T ≤ F a)
    (htheta0 : ∀ a ∈ Finset.Icc b (T - l), 0 ≤ theta a)
    (hmass : ∑ a ∈ Finset.Icc b (T - l), theta a ≤ 1)
    (hrow : ∀ a ∈ Finset.Icc b (T - l - 1),
      theta a ≤ D * K * (3 : ℝ) ^ (a - T)) :
    ∑ a ∈ Finset.Icc b (T - l), theta a • F a ≤
      F (T - l) +
        ((1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) * D * K *
          ((3 : ℝ) ^ (-(l : ℝ)) +
            (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) *
              ∑ r ∈ Finset.Icc (b + 1) T,
                (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) *
                  Matrix.trace ((F T)⁻¹ * (F (r - 1) - F r)))) • F T := by
  classical
  let U : ℤ := T - l
  let G : ℝ := 1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))
  let drift : ℝ := ∑ r ∈ Finset.Icc (b + 1) T,
    (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) *
      Matrix.trace ((F T)⁻¹ * (F (r - 1) - F r))
  change ∑ a ∈ Finset.Icc b U, theta a • F a ≤
    F U + (G * D * K *
      ((3 : ℝ) ^ (-(l : ℝ)) +
        (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) * drift)) • F T
  have hUT : U ≤ T := by dsimp only [U]; omega
  have hbT : b ≤ T := hbTl.trans hUT
  have hTpos : (F T).PosDef := hpos T (Finset.mem_Icc.mpr ⟨hbT, le_rfl⟩)
  have hUmem : U ∈ Finset.Icc b T :=
    Finset.mem_Icc.mpr ⟨by simpa only [U] using hbTl, hUT⟩
  have hUps : (F U).PosSemidef := (hpos U hUmem).posSemidef
  have hthetaU : theta U ≤ 1 := by
    have hmem : U ∈ Finset.Icc b (T - l) := by
      simpa only [U] using Finset.mem_Icc.mpr ⟨hbTl, le_rfl⟩
    exact (Finset.single_le_sum (f := theta) htheta0 hmem).trans hmass
  have hend : theta U • F U ≤ F U := by
    refine Matrix.le_iff.mpr ?_
    simpa only [sub_smul, one_smul] using
      hUps.smul (sub_nonneg.mpr hthetaU)
  have hdrift : 0 ≤ drift := by
    dsimp only [drift]
    refine Finset.sum_nonneg fun r hr => mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_
    have hG : (F (r - 1) - F r).PosSemidef := Matrix.le_iff.mp (hmono r hr)
    exact PortableHistory.trace_mul_nonneg hTpos.inv.posSemidef hG
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hslow0 : 0 ≤ (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hcoef0 : 0 ≤ G * D * K *
      ((3 : ℝ) ^ (-(l : ℝ)) +
        (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) * drift) := by
    have hGDK : 0 ≤ G * (D * K) := mul_nonneg hG0 hDK
    have hsum0 : 0 ≤ (3 : ℝ) ^ (-(l : ℝ)) +
        (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) * drift := by positivity
    nlinarith only [hGDK, hsum0]
  have hsplit : ∑ a ∈ Finset.Icc b U, theta a • F a =
      (∑ a ∈ Finset.Icc b (U - 1), theta a • F a) + theta U • F U := by
    have hnot : U ∉ Finset.Icc b (U - 1) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      omega
    rw [← Finset.insert_Icc_sub_one_right_eq_Icc (by simpa only [U] using hbTl),
      Finset.sum_insert hnot]
    abel
  by_cases hbpred : b ≤ U - 1
  · have hgeom := sum_zpow_sub_le_geom (T := T) (Finset.Icc b (U - 1))
        (fun a ha => (Finset.mem_Icc.mp ha).2)
    have hmassEarly : ∑ a ∈ Finset.Icc b (U - 1), theta a ≤
        G * D * K * (3 : ℝ) ^ (-((l : ℝ) + 1)) := by
      calc
        ∑ a ∈ Finset.Icc b (U - 1), theta a ≤
            ∑ a ∈ Finset.Icc b (U - 1), D * K * (3 : ℝ) ^ (a - T) :=
          Finset.sum_le_sum fun a ha => hrow a (by simpa only [U] using ha)
        _ = D * K * ∑ a ∈ Finset.Icc b (U - 1), (3 : ℝ) ^ (a - T) := by
          rw [Finset.mul_sum]
        _ ≤ D * K * ((3 : ℝ) ^ (((U - 1 : ℤ) : ℝ) - (T : ℝ)) * G) :=
          mul_le_mul_of_nonneg_left hgeom hDK
        _ = G * D * K * (3 : ℝ) ^ (-((l : ℝ) + 1)) := by
          have hexp : (((U - 1 : ℤ) : ℝ) - (T : ℝ)) = -((l : ℝ) + 1) := by
            dsimp only [U]
            push_cast
            ring
          rw [hexp]
          ring
    have hidx : T - (l + 1) = U - 1 := by
      dsimp only [U]
      ring
    have hmassEarly' : ∑ a ∈ Finset.Icc b (T - (l + 1)), theta a ≤
        G * D * K * (3 : ℝ) ^ (-((l : ℝ) + 1)) := by
      rw [hidx]
      exact hmassEarly
    have hearly := weighted_mean_row_le hrho0 hrho1 (by omega : 0 ≤ l + 1)
      (by dsimp only [U] at hbpred ⊢; omega) hDK F theta hpos hmono
      (fun a ha => hterminal a (by
        rw [Finset.mem_Icc] at ha ⊢
        exact ⟨ha.1, by omega⟩))
      (fun a ha => htheta0 a (by
        rw [Finset.mem_Icc] at ha ⊢
        exact ⟨ha.1, by omega⟩)) hmassEarly'
      (fun a ha => hrow a (by
        rw [Finset.mem_Icc] at ha ⊢
        exact ⟨ha.1, by omega⟩))
    rw [hidx] at hearly
    have hpow : (3 : ℝ) ^ (-((l : ℝ) + 1)) ≤
        (3 : ℝ) ^ (-(l : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hslow : (3 : ℝ) ^ (-(1 - rho) * (((l + 1 : ℤ) : ℝ))) ≤
        (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      push_cast
      nlinarith only [hrho1]
    have hcoef :
        G * D * K * (3 : ℝ) ^ (-((l : ℝ) + 1)) +
            G * D * K *
              (3 : ℝ) ^ (-(1 - rho) * (((l + 1 : ℤ) : ℝ))) * drift ≤
          G * D * K *
            ((3 : ℝ) ^ (-(l : ℝ)) +
              (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) * drift) := by
      have hA0 : 0 ≤ G * (D * K) := mul_nonneg hG0 hDK
      have hfirst := mul_le_mul_of_nonneg_left hpow hA0
      have hsecond0 := mul_le_mul_of_nonneg_right hslow hdrift
      have hsecond := mul_le_mul_of_nonneg_left hsecond0 hA0
      nlinarith only [hfirst, hsecond]
    have hearly' : ∑ a ∈ Finset.Icc b (U - 1), theta a • F a ≤
        (G * D * K *
          ((3 : ℝ) ^ (-(l : ℝ)) +
            (3 : ℝ) ^ (-(1 - rho) * (l : ℝ)) * drift)) • F T := by
      refine hearly.trans ?_
      change
        (G * D * K * (3 : ℝ) ^ (-((l : ℝ) + 1)) +
          G * D * K *
            (3 : ℝ) ^ (-(1 - rho) * (((l + 1 : ℤ) : ℝ))) * drift) • F T ≤ _
      refine Matrix.le_iff.mpr ?_
      rw [← sub_smul]
      exact hTpos.posSemidef.smul (sub_nonneg.mpr hcoef)
    rw [hsplit]
    simpa only [add_comm] using add_le_add hearly' hend
  · have hbU : b = U := by omega
    subst b
    have hsingleton : Finset.Icc U U = {U} := by simp
    rw [hsingleton, Finset.sum_singleton]
    refine hend.trans ?_
    refine Matrix.le_iff.mpr ?_
    rw [add_sub_cancel_left]
    exact hTpos.posSemidef.smul hcoef0

end

end Bridge
end HighContrast
end Homogenization
