/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationCentered
import HCPoly.Provider.PortableHistory.MajorizationNonlinear
import HCPoly.Provider.PortableHistory.Checkpoint

/-!
# `e.fixed.geometry.profile.majorization`

The profile retains the complete history: for every terminal scale `T ≥ b`,

`𝓗_q(T) ≤ C_0 𝒫_q(T;b)`,   `C_0 = (1 - 3^{-a})^{-1}`.

The three rows of `e.scale.selection.complete.profile` receive the three parts of
the history.  The centered maximum at `T` splits at the checkpoint into the part
carried by the scales at most `b`, which the first row absorbs, and the part
carried by the scales above `b`, which is the second row.  The nonlinear history
at `T` splits at the checkpoint too: the terms above `b` are exactly the third
row, and the terms below `b` are absorbed by the first row except for one
residual, which is at most `3^{-a}(1-3^{-a})^{-1}` times the `j = b` term of the
third row.  The constant is therefore `1 + 3^{-a}(1-3^{-a})^{-1}`, which is
`(1-3^{-a})^{-1}`, and it depends on `a` alone.  The endpoint `T = b` is the
identity `𝒫_q(b;b) = 𝓗_q(b)`.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- The bookkeeping of the three rows: the two halves of the history are
majorized row by row, and the residual of the nonlinear transport is charged to
the last row. -/
private theorem row_combine {W X Y V R E c : ℝ≥0∞} (hE : E ≤ c * R) :
    W * X + V + (W * Y + E + R) ≤ W * (X + Y) + V + (1 + c) * R := by
  calc W * X + V + (W * Y + E + R) ≤ W * X + V + (W * Y + c * R + R) := by gcongr
    _ = W * (X + Y) + V + (1 + c) * R := by ring

/-- Every row of the profile absorbs its share of the constant. -/
private theorem const_absorb {c C : ℝ≥0∞} (hC : 1 ≤ C) (hcC : 1 + c ≤ C) (X Y Z : ℝ≥0∞) :
    X + Y + (1 + c) * Z ≤ C * (X + Y + Z) := by
  calc X + Y + (1 + c) * Z ≤ C * X + C * Y + C * Z :=
        add_le_add (add_le_add (le_mul_of_one_le_left (zero_le) hC)
          (le_mul_of_one_le_left (zero_le) hC)) (mul_le_mul_left hcC Z)
    _ = C * (X + Y + Z) := by ring

/-! ## The constant -/

/-- The constant of `e.fixed.geometry.profile.majorization` is at least one. -/
theorem one_le_majorization_const {a : ℝ} (ha : 0 < a) :
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) := by
  have hr1 : (3 : ℝ) ^ (-a) < 1 := geom_ratio_lt_one ha
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-a) := geom_ratio_pos a
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by linarith only [hr1]
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hden]
  linarith only [hr0]

/-- The residual of the nonlinear transport, added to the last row of the
profile, is exactly the constant of `e.fixed.geometry.profile.majorization`. -/
theorem one_add_residual_le_majorization_const {a : ℝ} (ha : 0 < a) :
    (1 : ℝ≥0∞) + ENNReal.ofReal ((3 : ℝ) ^ (-a) / (1 - (3 : ℝ) ^ (-a))) ≤
      ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) := by
  have hr1 : (3 : ℝ) ^ (-a) < 1 := geom_ratio_lt_one ha
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-a) := geom_ratio_pos a
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by linarith only [hr1]
  have hval : (1 : ℝ) + (3 : ℝ) ^ (-a) / (1 - (3 : ℝ) ^ (-a)) =
      1 / (1 - (3 : ℝ) ^ (-a)) := by
    field_simp
    ring
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (div_nonneg hr0.le hden.le),
    hval]

/-- The constant of `e.fixed.geometry.profile.majorization` is positive. -/
theorem majorization_const_pos {a : ℝ} (ha : 0 < a) :
    (0 : ℝ) < 1 / (1 - (3 : ℝ) ^ (-a)) := by
  have hr1 : (3 : ℝ) ^ (-a) < 1 := geom_ratio_lt_one ha
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by linarith only [hr1]
  positivity

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- **`e.fixed.geometry.profile.majorization`.**  The complete history at the
terminal scale is majorized by the profile carried from the checkpoint, with a
constant depending on `a` alone. -/
theorem portable_majorization [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ}
    (hQ : 0 < Q) (ha : 0 < a) (hadm : a ≤ Q * rhoMax - (d : ℝ))
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ TMax → HasFiniteAdaptedMean P q r)
    {b T : ℤ} (hjb : jStar ≤ b) (hbT : b ≤ T) (hT : T ≤ TMax) :
    portableHistory P Q a rhoMax q jStar T ≤
      ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) *
        portableProfile P Q a rhoMax q jStar b T := by
  classical
  have hC0 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) :=
    one_le_majorization_const ha
  rcases eq_or_lt_of_le hbT with hEq | hlt
  · subst hEq
    rw [portableProfile_self Q a rhoMax hP hq hlj hfin hjb hT]
    exact le_mul_of_one_le_left (zero_le) hC0
  have hsplit : nonlinearHistory P Q a q jStar T =
      (∑ j ∈ Finset.Ico jStar b,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            frakH Q (relMean P q j T))) +
        ∑ j ∈ Finset.Ico b T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            frakH Q (relMean P q j T)) := by
    rw [nonlinearHistory, ← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive jStar b T),
      Finset.Ico_union_Ico_eq_Ico hjb hbT]
  -- the residual of the nonlinear transport is charged to the `j = b` term
  have hresidual : ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
        frakH Q (relMean P q b T) * (1 / (1 - (3 : ℝ) ^ (-a)))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-a) / (1 - (3 : ℝ) ^ (-a))) *
        ∑ j ∈ Finset.Ico b T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            frakH Q (relMean P q j T)) := by
    have hr1 : (3 : ℝ) ^ (-a) < 1 := geom_ratio_lt_one ha
    have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-a) := geom_ratio_pos a
    have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by linarith only [hr1]
    have hbmem : b ∈ Finset.Ico b T := Finset.mem_Ico.mpr ⟨le_rfl, hlt⟩
    have hterm : ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (b : ℝ))) *
        frakH Q (relMean P q b T)) ≤
        ∑ j ∈ Finset.Ico b T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
            frakH Q (relMean P q j T)) :=
      Finset.single_le_sum (f := fun j : ℤ =>
        ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j T))) (fun _ _ => zero_le) hbmem
    have hrw : (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * frakH Q (relMean P q b T) *
          (1 / (1 - (3 : ℝ) ^ (-a))) =
        (3 : ℝ) ^ (-a) / (1 - (3 : ℝ) ^ (-a)) *
          ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (b : ℝ))) * frakH Q (relMean P q b T)) := by
      have hpow : (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) =
          (3 : ℝ) ^ (-a) * (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (b : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        ring_nf
      rw [hpow]
      field_simp
    rw [hrw, ENNReal.ofReal_mul (div_nonneg hr0.le hden.le)]
    exact mul_le_mul_right hterm _
  -- the three rows of the profile
  have hmain : portableHistory P Q a rhoMax q jStar T ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
            (1 + frakH Q (relMean P q b T))) *
          portableHistory P Q a rhoMax q jStar b +
        (∑ j ∈ Finset.Icc (b + 1) T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j T)) * centeredMoment P Q q j ^ Q) +
        ((1 : ℝ≥0∞) + ENNReal.ofReal ((3 : ℝ) ^ (-a) / (1 - (3 : ℝ) ^ (-a)))) *
          ∑ j ∈ Finset.Ico b T,
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
              frakH Q (relMean P q j T)) := by
    rw [portableHistory, portableHistory, hsplit]
    exact le_trans
      (add_le_add (centered_majorization hQ hadm hP hq hlj hfin hjb hbT hT)
        (add_le_add (nonlinear_low_le hQ.le ha hP hq hlj hfin hjb hbT hT) le_rfl))
      (row_combine hresidual)
  refine hmain.trans ?_
  rw [portableProfile]
  exact const_absorb hC0 (one_add_residual_le_majorization_const ha) _ _ _

end Window

end

end PortableHistory
end HighContrast
end Homogenization
