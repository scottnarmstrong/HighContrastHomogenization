/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRecentCell
import HCPoly.Provider.PortableHistory.Checkpoint

/-!
# Summing the recent cell profile

The terminal nonlinear history controls each nonterminal mean increment.  The
terminal increment itself vanishes exactly.  Combining these facts with the
one-scale cell estimate gives the two finite coefficients in the recent-cell
bound.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}

/-- A nonterminal relative-mean gain is controlled by its summand in the
terminal nonlinear history. -/
theorem ofReal_frakH_root_le_nonlinearHistory_root [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} {jStar t : ℤ} {H j : ℕ}
    {Q a : ℝ} (hQ : 1 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ)) (hj : j ∈ Finset.Icc 1 H) :
    ENNReal.ofReal
        (frakH Q (relMean P q (t - (j : ℤ)) t) ^ Q⁻¹) ≤
      ENNReal.ofReal
          ((3 : ℝ) ^ (a * ((j : ℝ) - 1) / Q)) *
        nonlinearHistory P Q a q jStar t ^ Q⁻¹ := by
  have hjbounds := Finset.mem_Icc.mp hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjbounds.1
  have hj0 : (0 : ℝ) ≤ (j : ℝ) - 1 := by linarith only [hj1]
  have hklo : jStar ≤ t - (j : ℤ) := by
    have hjH : (j : ℤ) ≤ (H : ℤ) := by exact_mod_cast hjbounds.2
    exact hstart.trans (sub_le_sub_left hjH t)
  have hkhi : t - (j : ℤ) < t := by
    have hjpos : (0 : ℤ) < (j : ℤ) := by exact_mod_cast (by omega : 0 < j)
    omega
  have hkhi' : t - (j : ℤ) ≤ t := le_of_lt hkhi
  have hfrak0 : 0 ≤ frakH Q (relMean P q (t - (j : ℤ)) t) :=
    PortableHistory.frakH_relMean_nonneg (by linarith only [hQ]) hP hgrid hlj hfin
      hklo hkhi' le_rfl
  let w : ℝ := (3 : ℝ) ^ (-a * ((j : ℝ) - 1))
  let c : ℝ := (3 : ℝ) ^ (a * ((j : ℝ) - 1))
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hcw : c * w = 1 := by
    dsimp only [c, w]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring_nf
    exact Real.rpow_zero 3
  have hterm : ENNReal.ofReal
      (w * frakH Q (relMean P q (t - (j : ℤ)) t)) ≤
      nonlinearHistory P Q a q jStar t := by
    rw [nonlinearHistory]
    have hweight : (3 : ℝ) ^
        (-a * ((t : ℝ) - 1 - ((t - (j : ℤ) : ℤ) : ℝ))) = w := by
      dsimp only [w]
      congr 1
      push_cast
      ring
    rw [← hweight]
    exact Finset.single_le_sum (s := Finset.Ico jStar t)
      (f := fun k : ℤ ↦ ENNReal.ofReal
        ((3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (k : ℝ))) *
          frakH Q (relMean P q k t)))
      (fun k _ ↦ zero_le _) (Finset.mem_Ico.mpr ⟨hklo, hkhi⟩)
  have hbase : ENNReal.ofReal
      (frakH Q (relMean P q (t - (j : ℤ)) t)) ≤
      ENNReal.ofReal c * nonlinearHistory P Q a q jStar t := by
    calc
      ENNReal.ofReal (frakH Q (relMean P q (t - (j : ℤ)) t)) =
          ENNReal.ofReal c * ENNReal.ofReal
            (w * frakH Q (relMean P q (t - (j : ℤ)) t)) := by
        rw [← ENNReal.ofReal_mul hc0, ← mul_assoc, hcw, one_mul]
      _ ≤ ENNReal.ofReal c * nonlinearHistory P Q a q jStar t :=
        mul_right_mono hterm
  have hinvQ0 : 0 ≤ Q⁻¹ := inv_nonneg.mpr (by linarith only [hQ])
  have hroot := ENNReal.rpow_le_rpow hbase hinvQ0
  rw [ENNReal.mul_rpow_of_nonneg _ _ hinvQ0] at hroot
  have hcroot : c ^ Q⁻¹ = (3 : ℝ) ^ (a * ((j : ℝ) - 1) / Q) := by
    dsimp only [c]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
  calc
    ENNReal.ofReal
        (frakH Q (relMean P q (t - (j : ℤ)) t) ^ Q⁻¹) =
        ENNReal.ofReal (frakH Q (relMean P q (t - (j : ℤ)) t)) ^ Q⁻¹ :=
      (ENNReal.ofReal_rpow_of_nonneg hfrak0 hinvQ0).symm
    _ ≤ ENNReal.ofReal c ^ Q⁻¹ *
        nonlinearHistory P Q a q jStar t ^ Q⁻¹ := hroot
    _ = ENNReal.ofReal ((3 : ℝ) ^ (a * ((j : ℝ) - 1) / Q)) *
        nonlinearHistory P Q a q jStar t ^ Q⁻¹ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hc0 hinvQ0, hcroot]

/-- The recent cell sum is bounded pointwise by the centered terminal maximum
and the root of the nonlinear history, with the exact finite coefficients. -/
theorem ofReal_diagonalWeakCellSum_le_profile [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hq : q.PosDef) {jStar t : ℤ} {H : ℕ}
    {Q alpha rhoMax : ℝ} (hQ : 1 ≤ Q) (hrho : 0 ≤ rhoMax)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hgrid : IsRoundedGrid l q)
    (hlj : l ≤ jStar)
    (hfin : ∀ k : ℤ, jStar ≤ k → k ≤ t → HasFiniteAdaptedMean P q k)
    (hstart : jStar ≤ t - (H : ℤ))
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmean : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q k))
    (coeff : CoeffSpace d) :
    ENNReal.ofReal
        (diagonalWeakCellSum q t H (1 / 2) (adaptedMean P q t) coeff) ≤
      ENNReal.ofReal (centeredWindowCoefficient H rhoMax) *
          profileCenteredMaximum P rhoMax q jStar t coeff +
        ENNReal.ofReal (nonlinearCellWindowCoefficient H alpha Q) *
          nonlinearHistory P Q alpha q jStar t ^ Q⁻¹ := by
  let Z := profileCenteredMaximum P rhoMax q jStar t coeff
  let N := nonlinearHistory P Q alpha q jStar t ^ Q⁻¹
  let ccen : ℕ → ℝ := fun j ↦
    2 * (3 : ℝ) ^ (-(1 / 2 - rhoMax) * (j : ℝ))
  let cnl : ℕ → ℝ := fun j ↦
    (3 : ℝ) ^ (-(j : ℝ) / 2 + alpha * ((j : ℝ) - 1) / Q)
  have hccen0 : ∀ j, 0 ≤ ccen j := fun _ ↦ by positivity
  have hcnl0 : ∀ j, 0 ≤ cnl j := fun _ ↦ Real.rpow_nonneg (by norm_num) _
  have hsummand0 : ∀ j : ℕ, 0 ≤
      (3 : ℝ) ^ (-(1 / 2) * (j : ℝ)) *
        diagonalWeakCellDefect q (t - (j : ℤ)) t
          (adaptedMean P q t) coeff := by
    intro j
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (diagonalWeakCellDefect_nonneg q (t - (j : ℤ)) t
        (adaptedMean P q t) coeff)
  have hterm : ∀ j ∈ Finset.range (H + 1),
      ENNReal.ofReal
          ((3 : ℝ) ^ (-(1 / 2) * (j : ℝ)) *
            diagonalWeakCellDefect q (t - (j : ℤ)) t
              (adaptedMean P q t) coeff) ≤
        ENNReal.ofReal (ccen j) * Z +
          if j = 0 then 0 else ENNReal.ofReal (cnl j) * N := by
    intro j hj
    have hjH : j ≤ H := by
      have := Finset.mem_range.mp hj
      omega
    have hklo : jStar ≤ t - (j : ℤ) := by
      have hjH' : (j : ℤ) ≤ (H : ℤ) := by exact_mod_cast hjH
      exact hstart.trans (sub_le_sub_left hjH' t)
    have hkhi : t - (j : ℤ) ≤ t := sub_le_self t (Int.natCast_nonneg j)
    have hcell := ofReal_diagonalWeakCellDefect_le_profile hq hklo hkhi hQ hrho
      hEt (hmean _ hklo hkhi) coeff
    let w : ℝ := (3 : ℝ) ^ (-(1 / 2) * (j : ℝ))
    let r : ℝ := (3 : ℝ) ^ (rhoMax * ((t : ℝ) - ((t - (j : ℤ) : ℤ) : ℝ)))
    let f : ℝ := frakH Q (relMean P q (t - (j : ℤ)) t) ^ Q⁻¹
    have hw0 : 0 ≤ w := Real.rpow_nonneg (by norm_num) _
    have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
    have hf0 : 0 ≤ f := Real.rpow_nonneg
      (frakH_nonneg_of_one_le (by linarith only [hQ]) <| by
        rw [Recurrence.toFullBlockMat_relMean]
        exact Recurrence.one_le_normalize
          (posDef_toFullBlockMat
            (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt)
          ((blockMatLoewnerLE_iff_le
            (Recurrence.isSymmetricBlockMat_adaptedMean P q t)
            (Recurrence.isSymmetricBlockMat_adaptedMean P q (t - (j : ℤ)))).mp
              (hmean _ hklo hkhi))) _
    have hraw : ENNReal.ofReal w * ENNReal.ofReal
        (diagonalWeakCellDefect q (t - (j : ℤ)) t
          (adaptedMean P q t) coeff) ≤
        ENNReal.ofReal w *
          (ENNReal.ofReal (2 * r) * Z + ENNReal.ofReal f) := by
      apply mul_right_mono
      simpa only [r, f] using hcell
    have hcenter : w * (2 * r) = ccen j := by
      dsimp only [w, r, ccen]
      calc
        (3 : ℝ) ^ (-(1 / 2) * (j : ℝ)) *
            (2 * (3 : ℝ) ^
              (rhoMax * ((t : ℝ) - ((t - (j : ℤ) : ℤ) : ℝ)))) =
          2 * ((3 : ℝ) ^ (-(1 / 2) * (j : ℝ)) *
            (3 : ℝ) ^
              (rhoMax * ((t : ℝ) - ((t - (j : ℤ) : ℤ) : ℝ)))) := by ring
        _ = 2 * (3 : ℝ) ^ (-(1 / 2 - rhoMax) * (j : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
          push_cast
          congr 2
          ring
    have hscaled : ENNReal.ofReal
        (w * diagonalWeakCellDefect q (t - (j : ℤ)) t
          (adaptedMean P q t) coeff) ≤
        ENNReal.ofReal (ccen j) * Z + ENNReal.ofReal w * ENNReal.ofReal f := by
      rw [ENNReal.ofReal_mul hw0]
      calc
        ENNReal.ofReal w * ENNReal.ofReal
            (diagonalWeakCellDefect q (t - (j : ℤ)) t
              (adaptedMean P q t) coeff) ≤
            ENNReal.ofReal w *
              (ENNReal.ofReal (2 * r) * Z + ENNReal.ofReal f) := hraw
        _ = (ENNReal.ofReal w * ENNReal.ofReal (2 * r)) * Z +
              ENNReal.ofReal w * ENNReal.ofReal f := by ring
        _ = ENNReal.ofReal (ccen j) * Z +
              ENNReal.ofReal w * ENNReal.ofReal f := by
          rw [← ENNReal.ofReal_mul hw0, hcenter]
    by_cases hj0 : j = 0
    · subst j
      have hself : frakH Q (relMean P q t t) = 0 :=
        PortableHistory.frakH_relMean_self Q hP hgrid hlj hfin
          (hstart.trans (sub_le_self t (Int.natCast_nonneg H))) le_rfl
      have hfzero : f = 0 := by
        dsimp only [f]
        rw [Int.natCast_zero, sub_zero, hself, Real.zero_rpow]
        exact inv_ne_zero (by linarith only [hQ])
      simpa only [if_pos, hfzero, ENNReal.ofReal_zero, mul_zero, add_zero]
        using hscaled
    · have hjone : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hjIcc : j ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨hjone, hjH⟩
      have hnl := ofReal_frakH_root_le_nonlinearHistory_root (a := alpha)
        hQ hP hgrid hlj hfin hstart hjIcc
      have hnlscaled := mul_right_mono (a := ENNReal.ofReal w) hnl
      have hnonlinear : ENNReal.ofReal w * ENNReal.ofReal f ≤
          ENNReal.ofReal (cnl j) * N := by
        calc
          ENNReal.ofReal w * ENNReal.ofReal f ≤
              ENNReal.ofReal w *
                (ENNReal.ofReal
                  ((3 : ℝ) ^ (alpha * ((j : ℝ) - 1) / Q)) * N) := by
            simpa only [f, N] using hnlscaled
          _ = (ENNReal.ofReal w * ENNReal.ofReal
                ((3 : ℝ) ^ (alpha * ((j : ℝ) - 1) / Q))) * N := by ring
          _ = ENNReal.ofReal (cnl j) * N := by
            rw [← ENNReal.ofReal_mul hw0]
            congr 2
            dsimp only [w, cnl]
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
            congr 1
            ring
      simpa only [hj0, if_neg] using
        hscaled.trans (add_le_add le_rfl hnonlinear)
  have hcenterSum :
      (∑ j ∈ Finset.range (H + 1), ENNReal.ofReal (ccen j) * Z) =
        ENNReal.ofReal (centeredWindowCoefficient H rhoMax) * Z := by
    calc
      (∑ j ∈ Finset.range (H + 1), ENNReal.ofReal (ccen j) * Z) =
          (∑ j ∈ Finset.range (H + 1), ENNReal.ofReal (ccen j)) * Z := by
            rw [Finset.sum_mul]
      _ = ENNReal.ofReal
            (∑ j ∈ Finset.range (H + 1), ccen j) * Z := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hccen0 j)]
      _ = ENNReal.ofReal (centeredWindowCoefficient H rhoMax) * Z := by
          congr 2
          rw [centeredWindowCoefficient_eq]
          dsimp only [ccen]
          rw [Finset.mul_sum]
  have hrange : Finset.range (H + 1) = insert 0 (Finset.Icc 1 H) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hdrop :
      (∑ j ∈ Finset.range (H + 1),
        if j = 0 then 0 else ENNReal.ofReal (cnl j) * N) =
      ∑ j ∈ Finset.Icc 1 H, ENNReal.ofReal (cnl j) * N := by
    rw [hrange, Finset.sum_insert (by simp)]
    simp only [if_pos, zero_add]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [if_neg]
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hj).1
  have hnonlinearSum :
      (∑ j ∈ Finset.range (H + 1),
        if j = 0 then 0 else ENNReal.ofReal (cnl j) * N) =
        ENNReal.ofReal (nonlinearCellWindowCoefficient H alpha Q) * N := by
    rw [hdrop]
    calc
      (∑ j ∈ Finset.Icc 1 H, ENNReal.ofReal (cnl j) * N) =
          (∑ j ∈ Finset.Icc 1 H, ENNReal.ofReal (cnl j)) * N := by
            rw [Finset.sum_mul]
      _ = ENNReal.ofReal (∑ j ∈ Finset.Icc 1 H, cnl j) * N := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hcnl0 j)]
      _ = ENNReal.ofReal (nonlinearCellWindowCoefficient H alpha Q) * N := by
          congr 2
  rw [diagonalWeakCellSum_eq,
    ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hsummand0 j)]
  calc
    (∑ j ∈ Finset.range (H + 1),
        ENNReal.ofReal
          ((3 : ℝ) ^ (-(1 / 2) * (j : ℝ)) *
            diagonalWeakCellDefect q (t - (j : ℤ)) t
              (adaptedMean P q t) coeff)) ≤
      ∑ j ∈ Finset.range (H + 1),
        (ENNReal.ofReal (ccen j) * Z +
          if j = 0 then 0 else ENNReal.ofReal (cnl j) * N) :=
      Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range (H + 1), ENNReal.ofReal (ccen j) * Z) +
        ∑ j ∈ Finset.range (H + 1),
          if j = 0 then 0 else ENNReal.ofReal (cnl j) * N := by
      rw [Finset.sum_add_distrib]
    _ = ENNReal.ofReal (centeredWindowCoefficient H rhoMax) * Z +
        ENNReal.ofReal (nonlinearCellWindowCoefficient H alpha Q) * N := by
      rw [hcenterSum, hnonlinearSum]

end

end Homogenization.HighContrast.Response
