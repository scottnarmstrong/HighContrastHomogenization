/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.Geometry

/-!
# The dimensional tolerances of the entry argument

The proof of `t.polynomial.entry` opens by fixing an entry
threshold `c_*(d)` strictly inside the calibration window `min{c_sc, c_end}`,
an adapted slack `δ_ad ∈ (0,1]`, and three isotropy tolerances
`η_+, η_-, η_iso ∈ (0,1)` subject to

* the isotropy hierarchy `η_+ ≤ η_iso`,
* the volume constraint `(1+δ_ad)^{-d} - η_- ≥ 1 - η_iso`, and
* the contrast constraint
  `3((1+η_iso)^3(1-η_iso)^{-1}(1+δ_ad) - 1) ≤ c_*(d)`.

The printed argument fixes them in that order: `η_iso` first, so small that the
contrast constraint is strict at `δ_ad = 0`; then `δ_ad`, so small that it
survives and that `1 - (1+δ_ad)^{-d} < η_iso`; then `η_+ ≤ η_iso` and
`η_- ≤ η_iso - (1 - (1+δ_ad)^{-d})`.

The witnesses below make that order explicit.  With `c := ½ min{c_sc, c_end}`
and `ε := min{½, c/60}` the choice is

`c_* = c`, `η_iso = η_+ = ε`, `η_- = ε/2`, `δ_ad = ε/(2d)`,

and the two nontrivial verifications are elementary:

* on `0 < ε ≤ ½` one has `(1+ε)^4(1-ε)^{-1} ≤ 1 + 20ε`, because
  `26ε^2 + 4ε^3 + ε^4 ≤ 15ε` there, so the contrast constraint holds with the
  factor-three margin `60ε ≤ c`;
* Bernoulli's inequality at `-δ/(1+δ)` gives `(1+δ)^{-d} ≥ 1 - dδ`, and
  `dδ = ε/2` by the choice of `δ_ad`, so the volume constraint holds.
-/

namespace Homogenization
namespace HighContrast
namespace Entry

noncomputable section

/-- Bernoulli's inequality in the reciprocal form: a negative integer power of
`1 + δ` is at least `1 - dδ`. -/
private theorem one_sub_mul_le_zpow_neg {del : ℝ} (hdel0 : 0 < del) (hdel1 : del ≤ 1)
    (d : ℕ) : 1 - (d : ℝ) * del ≤ (1 + del) ^ (-(d : ℤ)) := by
  have hone : (1 : ℝ) ≤ 1 + del := by linarith only [hdel0]
  have hfrac : del / (1 + del) ≤ del := div_le_self hdel0.le hone
  have hfrac0 : (0 : ℝ) ≤ del / (1 + del) := by positivity
  have hb2 : (-2 : ℝ) ≤ -(del / (1 + del)) := by linarith only [hfrac, hfrac0, hdel1]
  have hstep : 1 - (d : ℝ) * (del / (1 + del)) ≤ ((1 + del)⁻¹) ^ d := by
    have h := one_add_mul_le_pow hb2 d
    rw [show (1 : ℝ) + -(del / (1 + del)) = (1 + del)⁻¹ by
      field_simp
      ring] at h
    linarith only [h]
  have hzp : (1 + del) ^ (-(d : ℤ)) = ((1 + del)⁻¹) ^ d := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hmul : (d : ℝ) * (del / (1 + del)) ≤ (d : ℝ) * del :=
    mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg d)
  rw [hzp]
  linarith only [hstep, hmul]

/-- The quartic comparison behind the contrast constraint: on `0 < ε ≤ ½` the
ratio `(1+ε)^4(1-ε)^{-1}` stays below `1 + 20ε`. -/
private theorem quartic_div_le {e : ℝ} (he0 : 0 < e) (he2 : e ≤ 1 / 2) :
    (1 + e) ^ 4 / (1 - e) ≤ 1 + 20 * e := by
  have hq : (0 : ℝ) < 1 - e := by linarith only [he2]
  have hE2 : e ^ 2 ≤ e / 2 := by
    have h := mul_le_mul_of_nonneg_left he2 he0.le
    rw [pow_two]
    linarith only [h]
  have hE3 : e ^ 3 ≤ e / 4 := by
    have h : e ^ 2 * e ≤ e / 2 * (1 / 2) :=
      mul_le_mul hE2 he2 he0.le (by positivity)
    rw [show e ^ 3 = e ^ 2 * e by ring]
    linarith only [h]
  have hE4 : e ^ 4 ≤ e / 8 := by
    have h : e ^ 3 * e ≤ e / 4 * (1 / 2) :=
      mul_le_mul hE3 he2 he0.le (by positivity)
    rw [show e ^ 4 = e ^ 3 * e by ring]
    linarith only [h]
  rw [div_le_iff₀ hq, show (1 + e) ^ 4 = 1 + 4 * e + 6 * e ^ 2 + 4 * e ^ 3 + e ^ 4 by ring,
    show (1 + 20 * e) * (1 - e) = 1 + 19 * e - 20 * e ^ 2 by ring]
  linarith only [hE2, hE3, hE4, he0]

/-- **The tolerance choice of the entry argument.**  Inside any calibration
window there is an entry threshold together with an adapted slack and three
isotropy tolerances satisfying the isotropy hierarchy, the volume constraint and
the contrast constraint of the proof of
`t.polynomial.entry`. -/
theorem exists_entry_tolerances (d : ℕ) (hd : 2 ≤ d) (cSc cEnd : ℝ) (hcSc : 0 < cSc)
    (hcEnd : 0 < cEnd) :
    ∃ cStar deltaAd etaPlus etaMinus etaIso : ℝ,
      cStar ∈ Set.Ioc (0 : ℝ) (min cSc cEnd) ∧
        0 < deltaAd ∧ deltaAd ≤ 1 ∧
        0 < etaPlus ∧ etaPlus < 1 ∧
        0 < etaMinus ∧ etaMinus < 1 ∧
        0 < etaIso ∧ etaIso < 1 ∧
        etaPlus ≤ etaIso ∧
        1 - etaIso ≤ (1 + deltaAd) ^ (-(d : ℤ)) - etaMinus ∧
        3 * ((1 + etaIso) ^ 3 / (1 - etaIso) * (1 + deltaAd) - 1) ≤ cStar := by
  have hmin : (0 : ℝ) < min cSc cEnd := lt_min hcSc hcEnd
  obtain ⟨c, hc0, hcle⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ min cSc cEnd :=
    ⟨min cSc cEnd / 2, by linarith only [hmin], by linarith only [hmin]⟩
  obtain ⟨e, he0, he2, he60⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 2 ∧ e ≤ c / 60 :=
    ⟨min (1 / 2) (c / 60), lt_min (by norm_num) (by linarith only [hc0]),
      min_le_left _ _, min_le_right _ _⟩
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := by linarith only [hdR]
  obtain ⟨del, hdel0, hdele, hdeld⟩ :
      ∃ del : ℝ, 0 < del ∧ del ≤ e ∧ (d : ℝ) * del ≤ e / 2 := by
    refine ⟨e / (2 * (d : ℝ)), by positivity, ?_, ?_⟩
    · exact div_le_self he0.le (by linarith only [hdR])
    · rw [show (d : ℝ) * (e / (2 * (d : ℝ))) = e / 2 by field_simp]
  have hdel1 : del ≤ 1 := by linarith only [hdele, he2]
  have hq : (0 : ℝ) < 1 - e := by linarith only [he2]
  refine ⟨c, del, e, e / 2, e, ⟨hc0, hcle⟩, hdel0, hdel1, he0, by linarith only [he2],
    by linarith only [he0], by linarith only [he2], he0, by linarith only [he2], le_rfl,
    ?_, ?_⟩
  · have hbern := one_sub_mul_le_zpow_neg hdel0 hdel1 d
    linarith only [hbern, hdeld]
  · have hstep : (1 + e) ^ 3 / (1 - e) * (1 + del) ≤ 1 + 20 * e := by
      calc (1 + e) ^ 3 / (1 - e) * (1 + del)
          ≤ (1 + e) ^ 3 / (1 - e) * (1 + e) := by
            refine mul_le_mul_of_nonneg_left (by linarith only [hdele]) ?_
            positivity
        _ = (1 + e) ^ 4 / (1 - e) := by ring
        _ ≤ 1 + 20 * e := quartic_div_le he0 he2
    linarith only [hstep, he60]

end

end Entry
end HighContrast
end Homogenization
