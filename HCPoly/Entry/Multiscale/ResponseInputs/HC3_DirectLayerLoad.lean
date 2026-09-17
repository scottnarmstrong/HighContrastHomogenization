import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsGeomCS
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# The shifted descendant layers against the source load

The descendant sum of `p.response.transfer` meets the layer one generation below the scale-`s`
cells.  Shifting the generation index upward costs the single factor `3^{3/2}`, since every
summand is nonnegative and the dropped head is nonnegative; and the weighted square roots the
descendant Cauchy--Schwarz consumes are summable by the arithmetic--geometric mean inequality.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Summability of the weighted square roots of the descendant layers.**  If the load family
`3^{-3n/2} L n` is summable and every layer is nonnegative, then the family `3^{-n} √(L n)` that
the descendant Cauchy--Schwarz consumes is summable, because
`3^{-n} √(L n) ≤ ½ (3^{-n/2} + 3^{-3n/2} L n)`. -/
theorem summable_rpow_neg_mul_sqrt_of_summable (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) :
    Summable fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have h3nn : (0 : ℝ) ≤ 3 := by norm_num
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_rpow_neg_half.add hsum).mul_left (1 / 2))
  · exact mul_nonneg (Real.rpow_nonneg h3nn _) (Real.sqrt_nonneg _)
  · have hu_sq : ((3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))) ^ 2
        = (3 : ℝ) ^ (-((n : ℝ) / 2)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul h3nn]
      rw [show (-(1 : ℝ) / 4 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -((n : ℝ) / 2) by ring]
    have hv_sq : ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n)) ^ 2
        = (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n := by
      rw [← Real.rpow_natCast]
      rw [Real.mul_rpow (Real.rpow_nonneg h3nn _) (Real.sqrt_nonneg _)]
      rw [← Real.rpow_mul h3nn]
      rw [Real.rpow_natCast, Real.sq_sqrt (hL n)]
      rw [show (-(3 : ℝ) / 4 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -((3 : ℝ) / 2) * (n : ℝ) by ring]
    have huv : (3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ))
        * ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n))
        = (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n) := by
      rw [← mul_assoc, ← Real.rpow_add h3pos]
      rw [show (-(1 : ℝ) / 4 * (n : ℝ)) + (-(3 : ℝ) / 4 * (n : ℝ)) = -(n : ℝ) by ring]
    rw [← huv, ← hu_sq, ← hv_sq]
    nlinarith [two_mul_le_add_sq ((3 : ℝ) ^ (-(1 : ℝ) / 4 * (n : ℝ)))
      ((3 : ℝ) ^ (-(3 : ℝ) / 4 * (n : ℝ)) * Real.sqrt (L n))]

/-- **The shifted descendant layers are dominated by the source load.**  Summing the layers from
depth one, with the weights of depth zero, costs at most the factor `3^{3/2}` against the source
load `𝓛_s` of `p.response.transfer`. -/
theorem tsum_succ_layer_le_respSourceLoad {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d))
    (jStar : ℕ) (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (hsum : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2))) :
    (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        ((((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2))
      ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y := by
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have _hd : d ≠ 0 := NeZero.ne d
  let g : ℕ → ℝ := fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
    ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
              Y.2))) ^ 2)
  have hg : Summable g := hsum
  have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := fun n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun z _ => sq_nonneg _))
  have hshift : (∑' n : ℕ, g (n + 1)) ≤ ∑' n : ℕ, g n := by
    have h := hg.tsum_eq_zero_add
    linarith [hg_nonneg 0]
  have hterm : ∀ n : ℕ,
      (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        ((((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2)
        = (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1) := by
    intro n
    have hweight : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
        = (3 : ℝ) ^ ((3 : ℝ) / 2)
          * (3 : ℝ) ^ (-((3 : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add h3pos]
      congr 1
      push_cast
      ring
    rw [hweight, mul_assoc]
  calc
    (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        ((((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2))
        = ∑' n : ℕ, (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1) :=
          tsum_congr hterm
    _ = (3 : ℝ) ^ ((3 : ℝ) / 2) * ∑' n : ℕ, g (n + 1) := by rw [tsum_mul_left]
    _ ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) * ∑' n : ℕ, g n :=
          mul_le_mul_of_nonneg_left hshift (le_of_lt (Real.rpow_pos_of_pos h3pos _))
    _ = (3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y := rfl

end

end Homogenization.HighContrast.Multiscale
