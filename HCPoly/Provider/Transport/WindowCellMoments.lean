/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowCellBounds

/-!
# The universal cell moments and their mixed source tails

The first clause of `e.source.adapted.bound` turns the pathwise cell bound
into two statements about the law: the moment bounds for the coarse block and
for the dual block on an adapted cell, which say that the scalar
normalization of the response of any adapted cell inside the window has `L^p`
norm at most `B_{\mathbf s}‖Y_P‖_{L^p}3^{g(j_*-a)_+}`; and the source-tail bound
for the coarse block on a cell, which says that the same
scalar quantity is below `B_{\mathbf s}3^{g(j_*-a)_+}` up to a remainder with the
source gauge's weak-Orlicz tail at the remainder scale.

Both are read off the pathwise bound and the two fields of the window multiplier
that are statements about the law.  The moment display is monotonicity of the
`L^p` norm against `B_{\mathbf s}3^{g(j_*-a)_+}Y_P`, and needs no restriction on
`p`: the restriction `p\in[1,Q]` in the printed clause is what makes the right
side finite, not what makes the inequality true.  The tail display is the
decomposition `Y_P = 1 + (Y_P - 1)`, the excess carrying the gauge's tail by
hypothesis, multiplied by the nonnegative constant — a weak-Orlicz tail scales
with the variable.

Nothing distinguishes the two orientations: the adjoint quantity is the scalar
normalization of the reflected response against the reflected reference block,
and the reflection is an order isomorphism.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-! ## From a pathwise bound by a multiple of the multiplier -/

/-- **A pathwise bound by a multiple of the multiplier is an `L^p` bound.**  The
scalar quantity is nonnegative and below `cY_P` along almost every realization,
so its `L^p` norm is below `c‖Y_P‖_{L^p}`, at every exponent. -/
theorem lqNorm_le_of_ae_le_mul {X : CoeffSpace d → ℝ} (hX : ∀ a, 0 ≤ X a)
    (hone : ∀ a, 1 ≤ Y a) {c : ℝ} (hc : 0 ≤ c) (hle : ∀ᵐ a ∂P, X a ≤ c * Y a)
    (p : ℝ) : lqNorm P p X ≤ ENNReal.ofReal c * lqNorm P p Y := by
  have hmono : lqNorm P p X ≤ eLpNorm (c • Y) (ENNReal.ofReal p) P := by
    refine eLpNorm_mono_ae ?_
    filter_upwards [hle] with a ha
    show ‖X a‖ ≤ ‖c * Y a‖
    rw [Real.norm_of_nonneg (hX a),
      Real.norm_of_nonneg (mul_nonneg hc (le_trans zero_le_one (hone a)))]
    exact ha
  rwa [eLpNorm_const_smul, Real.enorm_eq_ofReal hc] at hmono

/-- **A pathwise bound by a multiple of the multiplier is a mixed source-tail
bound.**  Writing `Y_P = 1 + (Y_P - 1)` exhibits the remainder `c(Y_P - 1)`,
which is nonnegative and carries the gauge's tail at the scale `c` times the
remainder scale. -/
theorem isShiftedBigOWith_of_ae_le_mul {X : CoeffSpace d → ℝ} (hone : ∀ a, 1 ≤ Y a)
    (horlicz : IndependentSums.IsBigOWith P Ψ (fun a => Y a - 1)
      (sourceRemainderScale d jStar K))
    {c : ℝ} (hc : 0 ≤ c) (hle : ∀ᵐ a ∂P, X a ≤ c * Y a) :
    IsShiftedBigOWith P Ψ X c (c * sourceRemainderScale d jStar K) := by
  refine ⟨fun a => c * (Y a - 1), fun a => mul_nonneg hc (by linarith only [hone a]), ?_,
    horlicz.const_mul hc⟩
  filter_upwards [hle] with a ha
  calc X a ≤ c * Y a := ha
    _ = c + c * (Y a - 1) := by ring

/-! ## The two moment displays -/

/-- **The moment bound for the coarse block on an adapted cell**: the scalar
normalization `|𝐄^{-1/2}𝐀(V)𝐄^{-1/2}|` of any adapted cell of any deterministic
rounded grid inside the window has `L^p` norm at most
`B_{\mathbf s}‖Y_P‖_{L^p}3^{g(j_*-a)_+}`. -/
theorem lqNorm_blockSize_coarseBlock_le (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M)
    (p : ℝ) :
    lqNorm P p (fun a => blockSize
        (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) r y) a) E) ≤
      ENNReal.ofReal (boundaryConst Cd g nu * burnDiscount g jStar r) * lqNorm P p Y :=
  lqNorm_le_of_ae_le_mul
    (fun a => PortableHistory.blockSize_nonneg (isSymmetricBlockMat_coarseBlock _ a) hE hEpd)
    hY.one_le (zero_le_boundaryConst_mul_burnDiscount hCd hg nu jStar r)
    (ae_blockSize_coarseBlock_adaptedCellTranslate_le hCd hg hE hEpd hY hnu hq r y hcont) p

/-- **The moment bound for the dual block on an adapted cell**: the same bound
for the sharp adjoint normalization `|𝐄_*^{1/2}𝐀_*^{-1}(V)𝐄_*^{1/2}|`. -/
theorem lqNorm_blockSize_coarseStarInv_le (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M)
    (p : ℝ) :
    lqNorm P p (fun a => blockSize
        (coarseStarInv (adaptedCellTranslate (roundedGrid jStar nu) r y) a)
        (blockReflect E)) ≤
      ENNReal.ofReal (boundaryConst Cd g nu * burnDiscount g jStar r) * lqNorm P p Y :=
  lqNorm_le_of_ae_le_mul
    (fun a => PortableHistory.blockSize_nonneg (isSymmetricBlockMat_coarseStarInv _ a)
      (isSymmetricBlockMat_blockReflect hE) (blockPosDef_blockReflect hEpd))
    hY.one_le (zero_le_boundaryConst_mul_burnDiscount hCd hg nu jStar r)
    (ae_blockSize_coarseStarInv_adaptedCellTranslate_le hCd hg hE hEpd hY hnu hq r y hcont) p

/-! ## The two mixed source-tail displays -/

/-- **The source-tail bound for the coarse block on a cell**: the scalar
normalization of the response of a cell of the window is below
`B_{\mathbf s}3^{g(j_*-a)_+}` up to a remainder with the source gauge's tail at
`B_{\mathbf s}a_{j_*}^{\mathcal S}3^{g(j_*-a)_+}`. -/
theorem isShiftedBigOWith_blockSize_coarseBlock (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    IsShiftedBigOWith P Ψ
      (fun a => blockSize
        (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) r y) a) E)
      (boundaryConst Cd g nu * burnDiscount g jStar r)
      (boundaryConst Cd g nu * sourceRemainderScale d jStar K *
        burnDiscount g jStar r) := by
  have h := isShiftedBigOWith_of_ae_le_mul (Ψ := Ψ) (K := K) hY.one_le hY.orlicz
    (zero_le_boundaryConst_mul_burnDiscount hCd hg nu jStar r)
    (ae_blockSize_coarseBlock_adaptedCellTranslate_le hCd hg hE hEpd hY hnu hq r y hcont)
  rwa [mul_right_comm (boundaryConst Cd g nu) (burnDiscount g jStar r)] at h

/-- **The adjoint cell tail**, the same display for the sharp adjoint
normalization. -/
theorem isShiftedBigOWith_blockSize_coarseStarInv (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    IsShiftedBigOWith P Ψ
      (fun a => blockSize
        (coarseStarInv (adaptedCellTranslate (roundedGrid jStar nu) r y) a)
        (blockReflect E))
      (boundaryConst Cd g nu * burnDiscount g jStar r)
      (boundaryConst Cd g nu * sourceRemainderScale d jStar K *
        burnDiscount g jStar r) := by
  have h := isShiftedBigOWith_of_ae_le_mul (Ψ := Ψ) (K := K) hY.one_le hY.orlicz
    (zero_le_boundaryConst_mul_burnDiscount hCd hg nu jStar r)
    (ae_blockSize_coarseStarInv_adaptedCellTranslate_le hCd hg hE hEpd hY hnu hq r y hcont)
  rwa [mul_right_comm (boundaryConst Cd g nu) (burnDiscount g jStar r)] at h

/-! ## The clause -/

/-- **The universal cell moments and their mixed source tails**, the first clause
of `e.source.adapted.bound`, proved from the window multiplier alone.  The
four displays hold simultaneously for every deterministic rounded grid, every
scale and every translate of an adapted cell contained in the window. -/
theorem cell_moments_of_isWindowMultiplier (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    (∀ p : ℝ,
        lqNorm P p (fun a => blockSize
            (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) r y) a) E) ≤
          ENNReal.ofReal (boundaryConst Cd g nu * burnDiscount g jStar r) *
            lqNorm P p Y) ∧
      (∀ p : ℝ,
        lqNorm P p (fun a => blockSize
            (coarseStarInv (adaptedCellTranslate (roundedGrid jStar nu) r y) a)
            (blockReflect E)) ≤
          ENNReal.ofReal (boundaryConst Cd g nu * burnDiscount g jStar r) *
            lqNorm P p Y) ∧
      IsShiftedBigOWith P Ψ
        (fun a => blockSize
          (coarseBlock (adaptedCellTranslate (roundedGrid jStar nu) r y) a) E)
        (boundaryConst Cd g nu * burnDiscount g jStar r)
        (boundaryConst Cd g nu * sourceRemainderScale d jStar K *
          burnDiscount g jStar r) ∧
      IsShiftedBigOWith P Ψ
        (fun a => blockSize
          (coarseStarInv (adaptedCellTranslate (roundedGrid jStar nu) r y) a)
          (blockReflect E))
        (boundaryConst Cd g nu * burnDiscount g jStar r)
        (boundaryConst Cd g nu * sourceRemainderScale d jStar K *
          burnDiscount g jStar r) :=
  ⟨lqNorm_blockSize_coarseBlock_le hCd hg hE hEpd hY hnu hq r y hcont,
    lqNorm_blockSize_coarseStarInv_le hCd hg hE hEpd hY hnu hq r y hcont,
    isShiftedBigOWith_blockSize_coarseBlock hCd hg hE hEpd hY hnu hq r y hcont,
    isShiftedBigOWith_blockSize_coarseStarInv hCd hg hE hEpd hY hnu hq r y hcont⟩

end

end Transport
end HighContrast
end Homogenization
