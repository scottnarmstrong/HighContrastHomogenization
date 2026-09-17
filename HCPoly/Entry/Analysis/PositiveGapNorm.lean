import HCPoly.Entry.Analysis.SchattenMeasurable
import HCPoly.Entry.Analysis.SchattenTriangle
import HCPoly.Entry.Analysis.ScalarMomentInequalities

/-!
# Real mixed Schatten norm bridges for the PositiveGap assembly

This file contains only the random-norm consequences needed for the
PositiveGap result: the coefficient-one subtraction estimate and the exact
constant-field readback on a probability law.
-/

open Homogenization.HighContrast (CoeffSpace blockSub)
namespace Homogenization.HighContrast.Analysis

open MeasureTheory

noncomputable section

/-- Sharp random-field subtraction for the real Schatten mixed norm. -/
theorem lqSchattenNorm_sub_le {d : ℕ} {P : Measure (CoeffSpace d)}
    {N : ℝ} (hN : 1 ≤ N) {F G : CoeffSpace d → BlockMat d}
    (hF : MemLqSchatten P N F) (hG : MemLqSchatten P N G) :
    lqSchattenNorm P N (fun a => blockSub (F a) (G a)) ≤
      lqSchattenNorm P N F + lqSchattenNorm P N G := by
  have hD : MemLqSchatten P N (fun a => blockSub (F a) (G a)) := hF.sub hG hN
  have hFmem := hF.memLp_absSchattenNorm hN
  have hGmem := hG.memLp_absSchattenNorm hN
  have hDread := hD.lqSchattenNorm_eq_eLpNorm_toReal hN
  have hFread := hF.lqSchattenNorm_eq_eLpNorm_toReal hN
  have hGread := hG.lqSchattenNorm_eq_eLpNorm_toReal hN
  have hsum := scalar_minkowski_toReal hN hFmem hGmem
  have hpoint :
      ∀ᵐ a ∂P,
        ‖absSchattenNorm N (blockSub (F a) (G a))‖ ≤
          ‖absSchattenNorm N (F a) + absSchattenNorm N (G a)‖ := by
    filter_upwards [hF.symmetric, hG.symmetric, hD.symmetric] with a hFa hGa hDa
    have hFH := (toFullBlockMat_isHermitian_iff (F a)).2 hFa
    have hGH := (toFullBlockMat_isHermitian_iff (G a)).2 hGa
    have hDH := (toFullBlockMat_isHermitian_iff (blockSub (F a) (G a))).2 hDa
    have hle := absSchattenNorm_sub_le hFH hGH hN
    have hDnn := absSchattenNorm_nonneg hDH hN
    have hFnn := absSchattenNorm_nonneg hFH hN
    have hGnn := absSchattenNorm_nonneg hGH hN
    rw [Real.norm_eq_abs, abs_of_nonneg hDnn, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hFnn hGnn)]
    exact hle
  have hmono :
      (eLpNorm (fun a => absSchattenNorm N (blockSub (F a) (G a)))
          (ENNReal.ofReal N) P).toReal ≤
        (eLpNorm (fun a => absSchattenNorm N (F a) + absSchattenNorm N (G a))
          (ENNReal.ofReal N) P).toReal :=
    ENNReal.toReal_mono hsum.1.eLpNorm_ne_top (eLpNorm_mono_ae hpoint)
  calc
    lqSchattenNorm P N (fun a => blockSub (F a) (G a))
        = (eLpNorm (fun a => absSchattenNorm N (blockSub (F a) (G a)))
            (ENNReal.ofReal N) P).toReal := hDread.2.2
    _ ≤ (eLpNorm (fun a => absSchattenNorm N (F a) + absSchattenNorm N (G a))
          (ENNReal.ofReal N) P).toReal := hmono
    _ ≤ (eLpNorm (fun a => absSchattenNorm N (F a)) (ENNReal.ofReal N) P).toReal +
          (eLpNorm (fun a => absSchattenNorm N (G a)) (ENNReal.ofReal N) P).toReal := hsum.2
    _ = lqSchattenNorm P N F + lqSchattenNorm P N G := by
      rw [hFread.2.2, hGread.2.2]

/-- On a probability law, the mixed norm of a deterministic symmetric block is
its deterministic Schatten norm. -/
theorem lqSchattenNorm_const {d : ℕ} (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] {N : ℝ} (hN : 1 ≤ N)
    (B : BlockMat d) (hB : IsSymmetricBlockMat B) :
    lqSchattenNorm P N (fun _ => B) = absSchattenNorm N B := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hBH := (toFullBlockMat_isHermitian_iff B).2 hB
  have hBnn : 0 ≤ absSchattenNorm N B := absSchattenNorm_nonneg hBH hN
  unfold lqSchattenNorm
  rw [integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  exact Real.rpow_rpow_inv hBnn hNpos.ne'

end

end Homogenization.HighContrast.Analysis
