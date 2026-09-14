/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.SuccessorDiscrete


namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory _root_.Filter
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

private theorem measureReal_iUnion_nat_le_tsum_sharp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {A : ℕ → Set Ω} (hA : Summable fun q => μ.real (A q)) :
    μ.real (⋃ q, A q) ≤ ∑' q, μ.real (A q) := by
  let ν : FiniteMeasure Ω := ⟨μ, inferInstance⟩
  have hAnn : Summable fun q => ν (A q) := by
    rw [← NNReal.summable_coe]
    simpa only [ν, Measure.real] using! hA
  have hν := FiniteMeasure.apply_iUnion_le (μ := ν) (f := A) hAnn
  have hνr : (ν (⋃ q, A q) : ℝ) ≤ ∑' q, (ν (A q) : ℝ) := by
    exact_mod_cast hν
  simpa only [ν, Measure.real] using! hνr

private theorem zpow_tail_split_sharp (n h : ℤ) (q : ℕ) :
    (3 : ℝ) ^ (-(n + (q : ℤ) - h)) =
      (3 : ℝ) ^ (-(n - h)) * ((1 : ℝ) / 3) ^ q := by
  rw [show -(n + (q : ℤ) - h) = -(n - h) + -(q : ℤ) by omega,
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  simp only [zpow_neg, zpow_natCast]
  field_simp
  rw [← mul_pow]
  norm_num

private theorem growthBar_pos_sharp (K : ℝ) : 0 < growthBar K := by
  rw [growthBar]
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The unabsorbed geometric sum in the strict-successor estimate. -/
theorem tsum_measureReal_badScaleEvent_le_sharp [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M n : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hn : M ≤ n) :
    (∑' q : ℕ, P.real {a : CoeffSpace d |
      badScaleEvent g E (M - jStar) (n + (q : ℤ)) a}) ≤
        (3 / 2 : ℝ) * (3 : ℝ) ^ (-(n - (M - jStar))) *
          (Ψ ((growthBar K ^ (4 * (d + 1)))⁻¹ *
            (3 : ℝ) ^ (n - (M - jStar))))⁻¹ := by
  let h : ℤ := M - jStar
  let x : ℝ := (growthBar K ^ (4 * (d + 1)))⁻¹ * (3 : ℝ) ^ (n - h)
  let c : ℝ := (3 : ℝ) ^ (-(n - h)) * (Ψ x)⁻¹
  have hBinv : 0 ≤ (growthBar K ^ (4 * (d + 1)))⁻¹ :=
    inv_nonneg.mpr (pow_pos (growthBar_pos_sharp K) _).le
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact mul_nonneg hBinv (by positivity)
  have hs := badScaleEvent_tail_summable hstat hdag hQ hw hn
  have hbound : ∀ q : ℕ,
      P.real {a : CoeffSpace d | badScaleEvent g E h (n + (q : ℤ)) a} ≤
        c * ((1 : ℝ) / 3) ^ q := by
    intro q
    have hmq : M ≤ n + (q : ℤ) := by omega
    have hb := measureReal_badScaleEvent_le_geometric hstat hdag hQ hw hmq
    have hpow : (3 : ℝ) ^ (n - h) ≤ (3 : ℝ) ^ (n + (q : ℤ) - h) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hxq0 : 0 ≤ (growthBar K ^ (4 * (d + 1)))⁻¹ *
        (3 : ℝ) ^ (n + (q : ℤ) - h) := mul_nonneg hBinv (by positivity)
    have hψle := hdag.gauge_admissible.1 hx0 hxq0
      (mul_le_mul_of_nonneg_left hpow hBinv)
    have hinv := (inv_le_inv₀ (lt_of_lt_of_le zero_lt_one
      (hdag.gauge_admissible.2 hxq0))
      (lt_of_lt_of_le zero_lt_one (hdag.gauge_admissible.2 hx0))).2 hψle
    calc
      P.real {a : CoeffSpace d | badScaleEvent g E h (n + (q : ℤ)) a}
          ≤ (3 : ℝ) ^ (-(n + (q : ℤ) - h)) *
            (Ψ ((growthBar K ^ (4 * (d + 1)))⁻¹ *
              (3 : ℝ) ^ (n + (q : ℤ) - h)))⁻¹ := by
                simpa only [h] using hb
      _ ≤ (3 : ℝ) ^ (-(n + (q : ℤ) - h)) * (Ψ x)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = c * ((1 : ℝ) / 3) ^ q := by
        rw [zpow_tail_split_sharp]
        dsimp only [c]
        ring
  have hgeom : Summable fun q : ℕ => c * ((1 : ℝ) / 3) ^ q :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c
  have hsum := hs.tsum_le_tsum hbound hgeom
  calc
    (∑' q : ℕ, P.real {a : CoeffSpace d |
      badScaleEvent g E h (n + (q : ℤ)) a})
        ≤ ∑' q : ℕ, c * ((1 : ℝ) / 3) ^ q := hsum
    _ = c * (1 - (1 : ℝ) / 3)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (3 / 2 : ℝ) * (3 : ℝ) ^ (-(n - h)) * (Ψ x)⁻¹ := by
      dsimp only [c]
      ring
    _ = (3 / 2 : ℝ) * (3 : ℝ) ^ (-(n - (M - jStar))) *
          (Ψ ((growthBar K ^ (4 * (d + 1)))⁻¹ *
            (3 : ℝ) ^ (n - (M - jStar))))⁻¹ := by rfl

private theorem successor_event_subset_bad_tail_sharp {g : ℝ} {E : BlockMat d}
    {h n : ℤ} :
    {a : CoeffSpace d | ENNReal.ofReal ((3 : ℝ) ^ n) < successorScale g E h a} ⊆
      ⋃ q : ℕ, {a : CoeffSpace d | badScaleEvent g E h (n + (q : ℤ)) a} := by
  intro a ha
  by_contra hmem
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hmem
  have hall : ∀ m : ℤ, badScaleEvent g E h m a → m ≤ n - 1 := by
    intro m hm
    by_contra hmn
    have hnm : n ≤ m := by omega
    let q : ℕ := (m - n).toNat
    have hmq : m = n + (q : ℤ) := by dsimp only [q]; omega
    exact hmem q (by rwa [← hmq])
  have hsup : (⨆ (m : ℤ) (_ : badScaleEvent g E h m a),
      ENNReal.ofReal ((3 : ℝ) ^ m)) ≤ ENNReal.ofReal ((3 : ℝ) ^ (n - 1)) :=
    iSup_le fun m => iSup_le fun hm => ENNReal.ofReal_le_ofReal
      (zpow_le_zpow_right₀ (by norm_num) (hall m hm))
  have hs : successorScale g E h a ≤ ENNReal.ofReal ((3 : ℝ) ^ n) := by
    rw [successorScale]
    calc
      3 * (⨆ (m : ℤ) (_ : badScaleEvent g E h m a),
          ENNReal.ofReal ((3 : ℝ) ^ m))
          ≤ 3 * ENNReal.ofReal ((3 : ℝ) ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left hsup (by positivity)
      _ = ENNReal.ofReal ((3 : ℝ) ^ n) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        calc
          (3 : ℝ) * (3 : ℝ) ^ (n - 1) =
              (3 : ℝ) ^ (1 : ℤ) * (3 : ℝ) ^ (n - 1) := by norm_num
          _ = (3 : ℝ) ^ ((1 : ℤ) + (n - 1)) :=
            (zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) 1 (n - 1)).symm
          _ = (3 : ℝ) ^ n := by congr 1; omega
  exact (not_lt_of_ge hs) ha

/-- The strict successor retains the geometric prefactor at each generation. -/
theorem measureReal_successorScale_gt_zpow_le_sharp [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M n : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hn : M ≤ n) :
    P.real {a : CoeffSpace d |
        ENNReal.ofReal ((3 : ℝ) ^ n) < successorScale g E (M - jStar) a} ≤
      (3 / 2 : ℝ) * (3 : ℝ) ^ (-(n - (M - jStar))) *
        (Ψ ((growthBar K ^ (4 * (d + 1)))⁻¹ *
          (3 : ℝ) ^ (n - (M - jStar))))⁻¹ := by
  let A : ℕ → Set (CoeffSpace d) := fun q =>
    {a | badScaleEvent g E (M - jStar) (n + (q : ℤ)) a}
  have hsummable := badScaleEvent_tail_summable hstat hdag hQ hw hn
  have hsub := successor_event_subset_bad_tail_sharp
    (g := g) (E := E) (h := M - jStar) (n := n)
  calc
    P.real {a : CoeffSpace d |
        ENNReal.ofReal ((3 : ℝ) ^ n) < successorScale g E (M - jStar) a}
        ≤ P.real (⋃ q, A q) := measureReal_mono hsub
    _ ≤ ∑' q, P.real (A q) := measureReal_iUnion_nat_le_tsum_sharp hsummable
    _ ≤ (3 / 2 : ℝ) * (3 : ℝ) ^ (-(n - (M - jStar))) *
        (Ψ ((growthBar K ^ (4 * (d + 1)))⁻¹ *
          (3 : ℝ) ^ (n - (M - jStar))))⁻¹ :=
      tsum_measureReal_badScaleEvent_le_sharp hstat hdag hQ hw hn

end
end Window
end HighContrast
end Homogenization

