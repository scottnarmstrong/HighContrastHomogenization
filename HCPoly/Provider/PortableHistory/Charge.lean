/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Transport

/-!
# Multiplicity of the synchronized charges

`e.fixed.geometry.synchronized.multiplicity` states that along an arithmetic
progression of step `h` each unit increment `δ_r^q` occurs in at most `h` of the
synchronized charges, so that

`∑_{k<K} Δ̂_h^q(T_0 + kh) ≤ h Δ_{T_0+1-h, T_0+Kh}^q`.

The proof is the bookkeeping the printed argument describes.  The charge at `T`
is the difference of two consecutive windows of `h` log-determinants,

`Δ̂_h^q(T) = ∑_{j=T+1-h}^{T} log det E_j^q - ∑_{j=T+1}^{T+h} log det E_j^q`,

because the increments telescope; summing over the progression telescopes once
more and leaves the two extreme windows.  Each of those windows has exactly `h`
terms, and the mean order makes the log-determinant nonincreasing in the scale,
so the left window is at most `h log det E_{T_0+1-h}^q` and the right window at
least `h log det E_{T_0+Kh}^q`.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The charge as a difference of two windows -/

/-- Shifting the summation index by the service length. -/
theorem sum_blockLogDet_shift (P : Measure (CoeffSpace d)) (q : Mat d) (h T : ℤ) :
    ∑ j ∈ Finset.Icc (T + 1) (T + h), blockLogDet (adaptedMean P q (j - h)) =
      ∑ j ∈ Finset.Icc (T + 1 - h) T, blockLogDet (adaptedMean P q j) := by
  have hmap : (Finset.Icc (T + 1 - h) T).map (addRightEmbedding h) =
      Finset.Icc (T + 1) (T + h) := by
    rw [Finset.map_add_right_Icc]
    congr 1
    ring
  rw [← hmap, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  simp [addRightEmbedding]

/-- **The synchronized charge is a difference of two windows of
log-determinants.** -/
theorem synchCharge_eq_window_sub (P : Measure (CoeffSpace d)) (q : Mat d) (h T : ℤ) :
    synchCharge P q h T =
      (∑ j ∈ Finset.Icc (T + 1 - h) T, blockLogDet (adaptedMean P q j)) -
        ∑ j ∈ Finset.Icc (T + h + 1 - h) (T + h), blockLogDet (adaptedMean P q j) := by
  have hidx : T + h + 1 - h = T + 1 := by ring
  rw [hidx]
  simp only [synchCharge, detIncrement, Finset.sum_sub_distrib]
  rw [sum_blockLogDet_shift]

/-! ## The window bounds -/

section Window

variable {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- A window of `h` log-determinants starting at `T + 1 - h` is at most `h`
times its first entry. -/
theorem sum_blockLogDet_window_le [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {h T : ℤ} (hh : 1 ≤ h) (hlow : jStar ≤ T + 1 - h) (hhigh : T ≤ TMax) :
    ∑ j ∈ Finset.Icc (T + 1 - h) T, blockLogDet (adaptedMean P q j) ≤
      (h : ℝ) * blockLogDet (adaptedMean P q (T + 1 - h)) := by
  have hcard : (Finset.Icc (T + 1 - h) T).card = h.toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have hbound : ∀ j ∈ Finset.Icc (T + 1 - h) T,
      blockLogDet (adaptedMean P q j) ≤ blockLogDet (adaptedMean P q (T + 1 - h)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hnn := Recurrence.detIncrement_nonneg hP hq (le_trans hlj hlow) hj.1
      (hfin (T + 1 - h) hlow (le_trans hj.1 (le_trans hj.2 hhigh)))
      (hfin j (le_trans hlow hj.1) (le_trans hj.2 hhigh))
    have : blockLogDet (adaptedMean P q (T + 1 - h)) - blockLogDet (adaptedMean P q j) =
        detIncrement P q (T + 1 - h) j := rfl
    linarith only [hnn, this]
  have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_trans zero_le_one hh)
  have hsum := Finset.sum_le_card_nsmul _ _ _ hbound
  rw [hcard, nsmul_eq_mul, hcast] at hsum
  exact hsum

/-- A window of `h` log-determinants ending at `T` is at least `h` times its
last entry. -/
theorem le_sum_blockLogDet_window [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {h T : ℤ} (hh : 1 ≤ h) (hlow : jStar ≤ T + 1 - h) (hhigh : T ≤ TMax) :
    (h : ℝ) * blockLogDet (adaptedMean P q T) ≤
      ∑ j ∈ Finset.Icc (T + 1 - h) T, blockLogDet (adaptedMean P q j) := by
  have hcard : (Finset.Icc (T + 1 - h) T).card = h.toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have hbound : ∀ j ∈ Finset.Icc (T + 1 - h) T,
      blockLogDet (adaptedMean P q T) ≤ blockLogDet (adaptedMean P q j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hnn := Recurrence.detIncrement_nonneg hP hq (le_trans hlj (le_trans hlow hj.1)) hj.2
      (hfin j (le_trans hlow hj.1) (le_trans hj.2 hhigh))
      (hfin T (le_trans hlow (le_trans hj.1 hj.2)) hhigh)
    have : blockLogDet (adaptedMean P q j) - blockLogDet (adaptedMean P q T) =
        detIncrement P q j T := rfl
    linarith only [hnn, this]
  have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (le_trans zero_le_one hh)
  have hsum := Finset.card_nsmul_le_sum _ _ _ hbound
  rw [hcard, nsmul_eq_mul, hcast] at hsum
  exact hsum

/-! ## The coverage of the charge -/

/-- **`e.scale.selection.synchronized.loss.lower`.**  The charge at `T` covers
every unit increment from `T + 1 - h` through `T + h - 1`, so it dominates the
increment across the whole span.  After the telescoping the two sides differ by
a window of `h - 1` log-determinants against its own translate by `h - 1`, and
the mean order compares them term by term. -/
theorem detIncrement_le_synchCharge [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {h T : ℤ} (hh : 1 ≤ h) (hlow : jStar ≤ T + 1 - h) (hhigh : T + h ≤ TMax) :
    detIncrement P q (T + 1 - h) (T + h) ≤ synchCharge P q h T := by
  have hbot : Finset.Icc (T + 1 - h) T = insert (T + 1 - h) (Finset.Icc (T + 2 - h) T) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hbotmem : (T + 1 - h) ∉ Finset.Icc (T + 2 - h) T := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  have htop : Finset.Icc (T + 1) (T + h) = insert (T + h) (Finset.Icc (T + 1) (T + h - 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have htopmem : (T + h) ∉ Finset.Icc (T + 1) (T + h - 1) := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  have hmap : (Finset.Icc (T + 2 - h) T).map (addRightEmbedding (h - 1)) =
      Finset.Icc (T + 1) (T + h - 1) := by
    rw [Finset.map_add_right_Icc]
    congr 1 <;> ring
  have hshift : ∑ j ∈ Finset.Icc (T + 1) (T + h - 1), blockLogDet (adaptedMean P q j) =
      ∑ j ∈ Finset.Icc (T + 2 - h) T, blockLogDet (adaptedMean P q (j + (h - 1))) := by
    rw [← hmap, Finset.sum_map]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
  have hmono : ∑ j ∈ Finset.Icc (T + 2 - h) T, blockLogDet (adaptedMean P q (j + (h - 1))) ≤
      ∑ j ∈ Finset.Icc (T + 2 - h) T, blockLogDet (adaptedMean P q j) := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hnn := Recurrence.detIncrement_nonneg (p := j + (h - 1)) hP hq
      (le_trans hlj (by omega)) (by omega)
      (hfin j (by omega) (by omega)) (hfin (j + (h - 1)) (by omega) (by omega))
    have heq : blockLogDet (adaptedMean P q j) -
        blockLogDet (adaptedMean P q (j + (h - 1))) = detIncrement P q j (j + (h - 1)) := rfl
    linarith only [hnn, heq]
  have hidx : T + h + 1 - h = T + 1 := by ring
  have hdet : detIncrement P q (T + 1 - h) (T + h) =
      blockLogDet (adaptedMean P q (T + 1 - h)) - blockLogDet (adaptedMean P q (T + h)) := rfl
  rw [synchCharge_eq_window_sub, hidx, hbot, htop, Finset.sum_insert hbotmem,
    Finset.sum_insert htopmem, hdet]
  linarith only [hshift, hmono]

/-! ## The multiplicity estimate -/

/-- **`e.fixed.geometry.synchronized.multiplicity`.**  Along the arithmetic progression
of step `h` the synchronized charges telescope, and the two extreme windows are
controlled by the mean order. -/
theorem sum_synchCharge_le [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {h : ℤ} (hh : 1 ≤ h) {T₀ : ℤ} (K : ℕ) (hT₀ : jStar + h ≤ T₀)
    (hKT : T₀ + (K : ℤ) * h ≤ TMax) :
    ∑ k ∈ Finset.range K, synchCharge P q h (T₀ + k * h) ≤
      (h : ℝ) * detIncrement P q (T₀ + 1 - h) (T₀ + K * h) := by
  have hK0 : (0 : ℤ) ≤ (K : ℤ) * h := mul_nonneg (Int.natCast_nonneg K) (le_trans zero_le_one hh)
  have hT₀TMax : T₀ ≤ TMax := le_trans (by linarith only [hK0]) hKT
  have hterm : ∀ k : ℕ, synchCharge P q h (T₀ + (k : ℤ) * h) =
      (∑ j ∈ Finset.Icc (T₀ + (k : ℤ) * h + 1 - h) (T₀ + (k : ℤ) * h),
          blockLogDet (adaptedMean P q j)) -
        ∑ j ∈ Finset.Icc (T₀ + ((k : ℤ) + 1) * h + 1 - h) (T₀ + ((k : ℤ) + 1) * h),
          blockLogDet (adaptedMean P q j) := by
    intro k
    rw [synchCharge_eq_window_sub]
    have hlo : T₀ + (k : ℤ) * h + h + 1 - h = T₀ + ((k : ℤ) + 1) * h + 1 - h := by ring
    have hhi : T₀ + (k : ℤ) * h + h = T₀ + ((k : ℤ) + 1) * h := by ring
    rw [hlo, hhi]
  have htel : ∑ k ∈ Finset.range K, synchCharge P q h (T₀ + (k : ℤ) * h) =
      (∑ j ∈ Finset.Icc (T₀ + 1 - h) T₀, blockLogDet (adaptedMean P q j)) -
        ∑ j ∈ Finset.Icc (T₀ + (K : ℤ) * h + 1 - h) (T₀ + (K : ℤ) * h),
          blockLogDet (adaptedMean P q j) := by
    have hsub := Finset.sum_range_sub'
      (fun k : ℕ => ∑ j ∈ Finset.Icc (T₀ + (k : ℤ) * h + 1 - h) (T₀ + (k : ℤ) * h),
        blockLogDet (adaptedMean P q j)) K
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    simpa using hsub
  have hleft := sum_blockLogDet_window_le hP hq hlj hfin (T := T₀) hh
    (by linarith only [hT₀]) hT₀TMax
  have hright := le_sum_blockLogDet_window hP hq hlj hfin (T := T₀ + (K : ℤ) * h) hh
    (by linarith only [hT₀, hK0]) hKT
  have hdet : detIncrement P q (T₀ + 1 - h) (T₀ + (K : ℤ) * h) =
      blockLogDet (adaptedMean P q (T₀ + 1 - h)) -
        blockLogDet (adaptedMean P q (T₀ + (K : ℤ) * h)) := rfl
  rw [htel, hdet, mul_sub]
  linarith only [hleft, hright]

end Window

end

end PortableHistory
end HighContrast
end Homogenization
