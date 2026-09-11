/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredSplit
import HCPoly.Provider.Transport.FiniteFamilyMaxMoment

/-!
# Splitting a finite family into three shared maxima

This variant of the centered-majorant split charges a pathwise maximum for
each of the inherited, fresh, and below-start pieces.  It therefore composes
directly with estimates which already control the fresh family maximum.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix

noncomputable section

variable {d : ℕ}

/-- A finite maximum of quantities dominated by three shared envelopes is
bounded by the sum of the three envelope moments. -/
theorem finite_max_shared_three_part_moment_le {iota alpha : Type*}
    [DecidableEq iota] [MeasurableSpace alpha]
    (P : Measure alpha) (s : Finset iota) (hs : s.Nonempty)
    {Q : ℝ} (hQ : 1 ≤ Q) {f : iota → alpha → ℝ≥0∞}
    {u v w : alpha → ℝ≥0∞} (C : ℝ≥0∞) (hC : C ^ Q ≠ ⊤)
    (hpoint : ∀ i ∈ s, ∀ᵐ x ∂P, f i x ≤ C * (u x + v x + w x))
    (humeas : AEMeasurable (fun x => u x ^ Q) P)
    (hvmeas : AEMeasurable (fun x => v x ^ Q) P) :
    ∫⁻ x, (s.sup' hs fun i => f i x) ^ Q ∂P ≤
      C ^ Q * ((2 : ℝ≥0∞) ^ (Q - 1)) ^ 2 *
        ((∫⁻ x, u x ^ Q ∂P) + (∫⁻ x, v x ^ Q ∂P) +
          ∫⁻ x, w x ^ Q ∂P) := by
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  set T : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (Q - 1) with hT
  have hT1 : 1 ≤ T := by
    rw [hT, ← ENNReal.one_rpow (Q - 1)]
    exact ENNReal.rpow_le_rpow (by norm_num) (by linarith only [hQ])
  have hpointAll : ∀ᵐ x ∂P, ∀ i ∈ s,
      f i x ≤ C * (u x + v x + w x) :=
    (s.eventually_all).2 hpoint
  have hpath : ∀ᵐ x ∂P,
      (s.sup' hs fun i => f i x) ^ Q ≤
        C ^ Q * T ^ 2 * (u x ^ Q + v x ^ Q + w x ^ Q) := by
    filter_upwards [hpointAll] with x hx
    have hsup : (s.sup' hs fun i => f i x) ≤
        C * (u x + v x + w x) :=
      Finset.sup'_le _ _ fun i hi => hx i hi
    have hadd1 := ENNReal.rpow_add_le_mul_rpow_add_rpow
      (u x + v x) (w x) hQ
    have hadd2 := ENNReal.rpow_add_le_mul_rpow_add_rpow (u x) (v x) hQ
    have hthree : (u x + v x + w x) ^ Q ≤
        T ^ 2 * (u x ^ Q + v x ^ Q + w x ^ Q) := by
      refine hadd1.trans ?_
      rw [show (2 : ℝ≥0∞) ^ (Q - 1) = T by rfl]
      calc
        T * ((u x + v x) ^ Q + w x ^ Q)
            ≤ T * (T * (u x ^ Q + v x ^ Q) + w x ^ Q) :=
              mul_le_mul' le_rfl (add_le_add hadd2 le_rfl)
        _ ≤ T * (T * (u x ^ Q + v x ^ Q) + T * w x ^ Q) :=
              mul_le_mul' le_rfl (add_le_add le_rfl (by
                calc
                  w x ^ Q = 1 * w x ^ Q := by rw [one_mul]
                  _ ≤ T * w x ^ Q := mul_le_mul' hT1 le_rfl))
        _ = T ^ 2 * (u x ^ Q + v x ^ Q + w x ^ Q) := by ring
    calc
      (s.sup' hs fun i => f i x) ^ Q
          ≤ (C * (u x + v x + w x)) ^ Q :=
            ENNReal.rpow_le_rpow hsup hQ0
      _ = C ^ Q * (u x + v x + w x) ^ Q :=
            ENNReal.mul_rpow_of_nonneg _ _ hQ0
      _ ≤ C ^ Q * (T ^ 2 * (u x ^ Q + v x ^ Q + w x ^ Q)) :=
            mul_le_mul' le_rfl hthree
      _ = C ^ Q * T ^ 2 * (u x ^ Q + v x ^ Q + w x ^ Q) := by ring
  have huv : AEMeasurable (fun x => u x ^ Q + v x ^ Q) P :=
    humeas.add hvmeas
  have hTtop : T ^ 2 ≠ ⊤ := by
    have hT' : T ≠ ⊤ := by
      rw [hT]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith only [hQ]) (by norm_num)
    exact ENNReal.pow_ne_top hT'
  have hconsttop : C ^ Q * T ^ 2 ≠ ⊤ := ENNReal.mul_ne_top hC hTtop
  calc
    ∫⁻ x, (s.sup' hs fun i => f i x) ^ Q ∂P
        ≤ ∫⁻ x, (C ^ Q * T ^ 2) *
            (u x ^ Q + v x ^ Q + w x ^ Q) ∂P :=
          lintegral_mono_ae hpath
    _ = (C ^ Q * T ^ 2) *
          ∫⁻ x, (u x ^ Q + v x ^ Q + w x ^ Q) ∂P := by
          rw [lintegral_const_mul' _ _ hconsttop]
    _ = (C ^ Q * T ^ 2) *
          ((∫⁻ x, u x ^ Q ∂P) + (∫⁻ x, v x ^ Q ∂P) +
            ∫⁻ x, w x ^ Q ∂P) := by
          rw [lintegral_add_left' huv, lintegral_add_left' humeas]
    _ = C ^ Q * ((2 : ℝ≥0∞) ^ (Q - 1)) ^ 2 *
          ((∫⁻ x, u x ^ Q ∂P) + (∫⁻ x, v x ^ Q ∂P) +
            ∫⁻ x, w x ^ Q ∂P) := by rw [hT]

/-- A finite family of centered block majorants is controlled by one maximum
for each of its inherited, fresh, and below-start pieces. -/
theorem finite_majorant_three_max_moment_le [NeZero d]
    {iota : Type*} [DecidableEq iota] {P : Measure (CoeffSpace d)}
    (s : Finset iota) (hs : s.Nonempty) {Q : ℕ} (hQ : 2 ≤ Q)
    (wt : iota → ℝ) (hwt : ∀ i ∈ s, 0 ≤ wt i)
    (A B C G : iota → CoeffSpace d → BlockMat d) (F : BlockMat d)
    (hA : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (A i x))
    (hB : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (B i x))
    (hC : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (C i x))
    (hG : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (G i x))
    (hsplit : ∀ i ∈ s, ∀ᵐ x ∂P,
      toFullBlockMat (G i x) =
        toFullBlockMat (A i x) + toFullBlockMat (B i x) +
          toFullBlockMat (C i x))
    {u v w : CoeffSpace d → ℝ≥0∞}
    (hu : ∀ i ∈ s, ∀ x,
      ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (A i x) F) ≤ u x)
    (hv : ∀ i ∈ s, ∀ x,
      ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (B i x) F) ≤ v x)
    (hw : ∀ i ∈ s, ∀ x,
      ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (C i x) F) ≤ w x)
    (humeas : AEMeasurable (fun x => u x ^ (Q : ℝ)) P)
    (hvmeas : AEMeasurable (fun x => v x ^ (Q : ℝ)) P) :
    ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i =>
        wt i * schattenSize (Q : ℝ) (G i x) F) ^ (Q : ℝ) ∂P ≤
      ENNReal.ofReal ((2 * (d : ℝ)) ^ 2) ^ (Q : ℝ) *
        ((2 : ℝ≥0∞) ^ ((Q : ℝ) - 1)) ^ 2 *
          ((∫⁻ x, u x ^ (Q : ℝ) ∂P) +
            (∫⁻ x, v x ^ (Q : ℝ) ∂P) +
            ∫⁻ x, w x ^ (Q : ℝ) ∂P) := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdR1 : (1 : ℝ) ≤ 2 * (d : ℝ) := by
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    linarith only [this]
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hpointReal : ∀ i ∈ s, ∀ᵐ x ∂P,
      schattenSize (Q : ℝ) (G i x) F ≤
        (2 * (d : ℝ)) ^ 2 *
          (schattenSize (Q : ℝ) (A i x) F +
            schattenSize (Q : ℝ) (B i x) F +
            schattenSize (Q : ℝ) (C i x) F) := by
    intro i hi
    filter_upwards [hsplit i hi] with x hx
    let AB : BlockMat d := ofFullBlockMat
      (toFullBlockMat (A i x) + toFullBlockMat (B i x))
    have hAB : IsSymmetricBlockMat AB := by
      simp only [AB]
      refine isSymmetricBlockMat_of_isSymm ?_
      exact (isSymm_toFullBlockMat_of_isSymmetricBlockMat (hA i hi x)).add
        (isSymm_toFullBlockMat_of_isSymmetricBlockMat (hB i hi x))
    have hABeq : toFullBlockMat AB =
        toFullBlockMat (A i x) + toFullBlockMat (B i x) := by
      simp only [AB, toFullBlockMat_ofFullBlockMat]
    have h1 := schattenSize_add_le (F := F) hQR hAB (hC i hi x) (hG i hi x)
      (by rw [hABeq, hx])
    have h2 := schattenSize_add_le (F := F) hQR (hA i hi x) (hB i hi x) hAB hABeq
    have hA0 := Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock (F := F) (hA i hi x)) (Q : ℝ)
    have hB0 := Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock (F := F) (hB i hi x)) (Q : ℝ)
    have hC0 := Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock (F := F) (hC i hi x)) (Q : ℝ)
    have hfac : 0 ≤ 2 * (d : ℝ) := by positivity
    have htail : (2 * (d : ℝ)) * schattenSize (Q : ℝ) (C i x) F ≤
        (2 * (d : ℝ)) ^ 2 * schattenSize (Q : ℝ) (C i x) F := by
      have hKle : 2 * (d : ℝ) ≤ (2 * (d : ℝ)) ^ 2 := by
        nlinarith only [hdR1, hfac]
      exact mul_le_mul_of_nonneg_right hKle hC0
    have hstep := mul_le_mul_of_nonneg_left h2 hfac
    nlinarith only [h1, hstep, htail, hA0, hB0, hC0, hfac]
  have hpoint : ∀ i ∈ s, ∀ᵐ x ∂P,
      ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (G i x) F) ≤
        ENNReal.ofReal ((2 * (d : ℝ)) ^ 2) * (u x + v x + w x) := by
    intro i hi
    filter_upwards [hpointReal i hi] with x hx
    have hw0 := hwt i hi
    have hfac0 : 0 ≤ (2 * (d : ℝ)) ^ 2 := sq_nonneg _
    have hraw := mul_le_mul_of_nonneg_left hx hw0
    have hrearrange : wt i * ((2 * (d : ℝ)) ^ 2 *
        (schattenSize (Q : ℝ) (A i x) F + schattenSize (Q : ℝ) (B i x) F +
          schattenSize (Q : ℝ) (C i x) F)) =
        (2 * (d : ℝ)) ^ 2 *
          (wt i * schattenSize (Q : ℝ) (A i x) F +
            wt i * schattenSize (Q : ℝ) (B i x) F +
            wt i * schattenSize (Q : ℝ) (C i x) F) := by ring
    rw [hrearrange] at hraw
    refine (ENNReal.ofReal_le_ofReal hraw).trans ?_
    rw [ENNReal.ofReal_mul hfac0]
    refine mul_le_mul' le_rfl ?_
    have ha0 : 0 ≤ wt i * schattenSize (Q : ℝ) (A i x) F :=
      mul_nonneg hw0 (Recurrence.zero_le_schattenNorm
        (isSymmetricBlockMat_normalizedBlock (F := F) (hA i hi x)) _)
    have hb0 : 0 ≤ wt i * schattenSize (Q : ℝ) (B i x) F :=
      mul_nonneg hw0 (Recurrence.zero_le_schattenNorm
        (isSymmetricBlockMat_normalizedBlock (F := F) (hB i hi x)) _)
    have hc0 : 0 ≤ wt i * schattenSize (Q : ℝ) (C i x) F :=
      mul_nonneg hw0 (Recurrence.zero_le_schattenNorm
        (isSymmetricBlockMat_normalizedBlock (F := F) (hC i hi x)) _)
    calc
      ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (A i x) F +
            wt i * schattenSize (Q : ℝ) (B i x) F +
            wt i * schattenSize (Q : ℝ) (C i x) F) =
          ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (A i x) F) +
            ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (B i x) F) +
            ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (C i x) F) := by
              rw [ENNReal.ofReal_add (add_nonneg ha0 hb0) hc0,
                ENNReal.ofReal_add ha0 hb0]
      _ ≤ u x + v x + w x :=
            add_le_add (add_le_add (hu i hi x) (hv i hi x)) (hw i hi x)
  have htop : ENNReal.ofReal ((2 * (d : ℝ)) ^ 2) ^ (Q : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hmain := finite_max_shared_three_part_moment_le P s hs
    (le_trans one_le_two hQR) (C := ENNReal.ofReal ((2 * (d : ℝ)) ^ 2))
      htop hpoint humeas hvmeas
  refine (le_of_eq ?_).trans hmain
  apply lintegral_congr
  intro x
  congr 1
  obtain ⟨i, hi, hmax⟩ := s.exists_mem_eq_sup' hs fun k =>
    wt k * schattenSize (Q : ℝ) (G k x) F
  rw [hmax]
  apply le_antisymm
  · exact Finset.le_sup' (fun k =>
      ENNReal.ofReal (wt k * schattenSize (Q : ℝ) (G k x) F)) hi
  · refine Finset.sup'_le _ _ fun k hk => ENNReal.ofReal_le_ofReal ?_
    rw [← hmax]
    exact Finset.le_sup' (fun z => wt z * schattenSize (Q : ℝ) (G z x) F) hk

end

end Transport
end HighContrast
end Homogenization
