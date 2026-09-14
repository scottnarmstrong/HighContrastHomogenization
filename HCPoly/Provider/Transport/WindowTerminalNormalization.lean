/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowCellBounds
import HCPoly.Geometry.AnnealedBlockBridge
import HCPoly.Provider.Sharp.CoarseBlockOrder

/-!
# The terminal mean, its comparison, and the bridged normalization

The terminal clause of `e.source.adapted.bound` compares the annealed block
of the terminal cell with the reference block from both sides,
`b_{\mathbf r}^{-1}𝐄_* ≤ F_0 ≤ b_{\mathbf r}𝐄` with
`b_{\mathbf r} = B_{\mathbf r}\E[Y_P]`
(`e.two.grid.source.normalization`), and reads the resulting
normalization `Λ(F_0;𝐄) ≤ κ_𝐄b_{\mathbf r}` and its bridged form
`Λ(F;𝐄) ≤ κ_𝐄b_{\mathbf r}/(1-η)`.

The upper comparison is the primal cell bound of the window integrated: the
expectation is monotone and the multiplier's mean is the printed factor.  The
lower comparison needs no operator Jensen once the sharp involution is
available.  The sharp reverses the Loewner order and is homogeneous of degree
minus one, so the upper comparison gives `b_{\mathbf r}^{-1}𝐄_* ≤ F_0^♯`; and the
annealed primal-adjoint order gives `F_0^♯ ≤ F_0`.  The
two together are the printed lower bound, and they also give positivity of
`F_0` a second time.

The normalization is then a change of reference block: the reference ratio
`κ_𝐄 = Λ(𝐄_*;𝐄)` is by definition the cost of
measuring `𝐄` against its own dual, and the lower comparison converts that into
the cost of measuring `𝐄` against `F_0`.  One more change of reference, by the
lower bridge, gives the bridged form; the upper bridge is not used.

The agreement of the primal and adjoint normalizations is an identity, not an
estimate: the reflection carries the defining set of one
scalar size onto the defining set of the other.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## Strict positivity of the printed constant -/

/-- The witness eccentricity `𝔢_{\mathbf q} = (|m||m^{-1}|)^{1/2}` of a positive
witness is positive in positive dimension: a positive definite matrix is a unit,
hence nonzero, and so is its inverse. -/
theorem zero_lt_witnessEccentricity [NeZero d] {m : Mat d} (hm : m.PosDef) :
    0 < witnessEccentricity m := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have h1 : 0 < ‖m‖ := norm_pos_iff.mpr hm.isUnit.ne_zero
  have h2 : 0 < ‖m⁻¹‖ := norm_pos_iff.mpr hm.inv.isUnit.ne_zero
  rw [witnessEccentricity, Real.sqrt_pos, specBound_eq_norm hm.posSemidef,
    specBound_eq_norm hm.inv.posSemidef]
  exact mul_pos h1 h2

/-- The boundary constant is positive in positive dimension, at a positive
dimensional constant and below the critical growth exponent. -/
theorem zero_lt_boundaryConst [NeZero d] {Cd g : ℝ} (hCd : 0 < Cd) (hg : g < 1)
    {m : Mat d} (hm : m.PosDef) : 0 < boundaryConst Cd g m :=
  mul_pos (mul_pos hCd (zero_lt_witnessEccentricity hm)) (zero_lt_zetaG hg)

/-- A positive dilation of a positive definite block is positive definite. -/
theorem blockPosDef_blockScale {A : BlockMat d} {c : ℝ} (hc : 0 < c)
    (h : Book.Ch02.BlockPosDef A) : Book.Ch02.BlockPosDef (blockScale c A) := by
  intro X hX
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale]
  exact mul_pos hc (h X hX)

/-! ## The adjoint normalization is an identity -/

/-- **The two scalar normalizations agree.**  The reflection commutes
with scalar dilation and preserves the Loewner order in both directions, so the
two scalar sizes are infima of the same set of reals. -/
theorem blockSize_blockReflect (H F : BlockMat d) :
    blockSize (blockReflect H) (blockReflect F) = blockSize H F := by
  have hset : {t : ℝ | 0 ≤ t ∧
      BlockMatLoewnerLE (blockReflect H) (blockScale t (blockReflect F)) ∧
        BlockMatLoewnerLE (blockScale (-t) (blockReflect F)) (blockReflect H)} =
      {t : ℝ | 0 ≤ t ∧ BlockMatLoewnerLE H (blockScale t F) ∧
        BlockMatLoewnerLE (blockScale (-t) F) H} := by
    ext t
    simp only [Set.mem_ofPred_eq, blockScale_blockReflect,
      blockMatLoewnerLE_blockReflect_iff]
  simp only [blockSize, hset]

/-! ## The terminal comparison -/

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- The multiplier has mean at least one: it is at least one pathwise and the law
is a probability measure. -/
theorem one_le_integral_of_isWindowMultiplier [IsProbabilityMeasure P]
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) : (1 : ℝ) ≤ ∫ a, Y a ∂P := by
  have h := integral_mono (integrable_const (1 : ℝ))
    (integrable_of_isWindowMultiplier hY) hY.one_le
  rwa [integral_const, probReal_univ, smul_eq_mul, mul_one] at h

/-- **The upper comparison on a cell of the window** `\E[\bfA(V)] ≤ B\E[Y_P]𝐄`:
the primal cell bound, integrated. -/
theorem annealedBlock_le_blockScale (hE : IsSymmetricBlockMat E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {r : ℤ} (hr : jStar ≤ r) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    BlockMatLoewnerLE
      (annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu) r y))
      (blockScale (boundaryConst Cd g nu * ∫ a, Y a ∂P) E) := by
  have hint := hasIntegrableCoarseBlock_adaptedCellTranslate hY hnu hq r y hcont
  have hYconst : Integrable (fun a => boundaryConst Cd g nu * Y a) P :=
    (integrable_of_isWindowMultiplier hY).const_mul _
  have hrhsInt : Integrable
      (fun a => (boundaryConst Cd g nu * Y a) • toFullBlockMat E) P :=
    integrable_of_entries fun i j => by
      simpa only [Matrix.smul_apply, smul_eq_mul] using
        hYconst.mul_const (toFullBlockMat E i j)
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_annealedBlock hint, toFullBlockMat_blockScale,
    show (boundaryConst Cd g nu * ∫ a, Y a ∂P) • toFullBlockMat E =
      ∫ a, (boundaryConst Cd g nu * Y a) • toFullBlockMat E ∂P by
      rw [integral_smul_const, integral_const_mul]]
  refine integral_mono' (integrable_toFullBlockMat hint) hrhsInt ?_
  filter_upwards [ae_blockMatLoewnerLE_coarseBlock_adaptedCellTranslate hY hnu r y hcont]
    with a ha
  rw [burnDiscount_eq_one g hr, mul_one] at ha
  have h := le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock _ a)
    (isSymmetricBlockMat_blockScale _ hE) ha
  rwa [toFullBlockMat_blockScale] at h

/-- **The upper terminal comparison** `F_0 ≤ b_{\mathbf r}𝐄`, the centered cell
of the terminal scale being the translate of itself by zero. -/
theorem adaptedMean_le_blockScale (hE : IsSymmetricBlockMat E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {t : ℤ} (ht : jStar ≤ t)
    (hcont : adaptedCell (roundedGrid jStar nu) t ⊆ centeredCube d M) :
    BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar nu) t)
      (blockScale (boundaryConst Cd g nu * ∫ a, Y a ∂P) E) := by
  have hzero : adaptedCellTranslate (roundedGrid jStar nu) t 0 =
      adaptedCell (roundedGrid jStar nu) t := by
    simp [adaptedCellTranslate]
  have h := annealedBlock_le_blockScale hE hY hnu hq ht 0 (by rw [hzero]; exact hcont)
  rwa [hzero] at h

/-- **The lower terminal comparison** `b_{\mathbf r}^{-1}𝐄_* ≤ F_0`: the sharp
involution reverses the upper comparison, and the annealed block dominates its
own sharp. -/
theorem blockScale_inv_blockSharp_le_adaptedMean [NeZero d] [IsProbabilityMeasure P]
    (hCd : 0 < Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {t : ℤ} (ht : jStar ≤ t)
    (hcont : adaptedCell (roundedGrid jStar nu) t ⊆ centeredCube d M) :
    BlockMatLoewnerLE
      (blockScale (boundaryConst Cd g nu * ∫ a, Y a ∂P)⁻¹ (blockSharp E))
      (adaptedMean P (roundedGrid jStar nu) t) := by
  have hb : 0 < boundaryConst Cd g nu * ∫ a, Y a ∂P :=
    mul_pos (zero_lt_boundaryConst hCd hg hnu)
      (lt_of_lt_of_le zero_lt_one (one_le_integral_of_isWindowMultiplier hY))
  have hint := hasFiniteAdaptedMean_of_isWindowMultiplier hY hnu hq ht hcont
  have hmeanpd := blockPosDef_adaptedMean_of_isWindowMultiplier hY hnu hq ht hcont
  have hrev := blockMatLoewnerLE_blockSharp_of_le
    (Recurrence.isSymmetricBlockMat_adaptedMean P _ t) (isSymmetricBlockMat_blockScale _ hE)
    hmeanpd (blockPosDef_blockScale hb hEpd)
    (adaptedMean_le_blockScale hE hY hnu hq ht hcont)
  rw [blockSharp_blockScale hE hEpd hb] at hrev
  refine hrev.trans (blockSharp_annealedBlock_le hint ?_ ?_)
  · exact fun a => Recurrence.blockPosDef_coarseBlock_adaptedCell_of_isRoundedGrid hq t a
  · exact fun a => Sharp.blockMatLoewnerLE_blockSharp_coarseBlock_of_nonempty
      (Recurrence.isOpenBoundedConvexDomain_adaptedCell (Recurrence.posDef_of_isRoundedGrid hq) t)
      (Recurrence.adaptedCell_nonempty _ t) a

/-! ## The terminal normalization -/

/-- **The terminal normalization** `Λ(F_0;𝐄) ≤ κ_𝐄b_{\mathbf r}`: the reference
ratio is the cost of measuring the reference block against its own dual, and the
lower terminal comparison converts it into the cost of measuring the reference
block against the terminal mean. -/
theorem blockSize_adaptedMean_le [NeZero d] [IsProbabilityMeasure P] (hCd : 0 < Cd)
    (hg : g < 1) (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {t : ℤ} (ht : jStar ≤ t)
    (hcont : adaptedCell (roundedGrid jStar nu) t ⊆ centeredCube d M) :
    blockSize E (adaptedMean P (roundedGrid jStar nu) t) ≤
      kappaRef E * (boundaryConst Cd g nu * ∫ a, Y a ∂P) := by
  set b : ℝ := boundaryConst Cd g nu * ∫ a, Y a ∂P with hbdef
  have hb : 0 < b := by
    rw [hbdef]
    exact mul_pos (zero_lt_boundaryConst hCd hg hnu)
      (lt_of_lt_of_le zero_lt_one (one_le_integral_of_isWindowMultiplier hY))
  have hsharpsym : IsSymmetricBlockMat (blockSharp E) := isSymmetricBlockMat_blockSharp hE hEpd
  have hsharppd : Book.Ch02.BlockPosDef (blockSharp E) := by
    refine (blockPosDef_iff_posDef hsharpsym).mpr ?_
    rw [toFullBlockMat_blockSharp]
    exact posDef_fullBlockSharp (posDef_toFullBlockMat hE hEpd)
  have hlow := le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockScale b⁻¹ hsharpsym)
    (Recurrence.isSymmetricBlockMat_adaptedMean P _ t)
    (blockScale_inv_blockSharp_le_adaptedMean hCd hg hE hEpd hY hnu hq ht hcont)
  rw [toFullBlockMat_blockScale] at hlow
  have hscaled : toFullBlockMat (blockSharp E) ≤
      b • toFullBlockMat (adaptedMean P (roundedGrid jStar nu) t) := by
    have h := smul_le_smul_of_le hb.le hlow
    rwa [smul_smul, mul_inv_cancel₀ hb.ne', one_smul] at h
  have hstep := PortableHistory.blockSize_le_mul_blockSize hE hsharpsym hsharppd
    (Recurrence.isSymmetricBlockMat_adaptedMean P _ t)
    (blockPosDef_adaptedMean_of_isWindowMultiplier hY hnu hq ht hcont) hb.le hscaled
  rw [mul_comm (kappaRef E) b]
  exact hstep

/-- **The bridged normalization** `Λ(F;𝐄) ≤ κ_𝐄b_{\mathbf r}/(1-η)`, the first
half of the clause read through a bridged terminal normalization
(`e.two.grid.source.normalization`).  Only the lower half of
the bridge `(1-η)F_0 ≤ F ≤ (1+η)F_0` is used. -/
theorem blockSize_le_div_of_bridge [NeZero d] [IsProbabilityMeasure P] (hCd : 0 < Cd)
    (hg : g < 1) (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {t : ℤ} (ht : jStar ≤ t)
    (hcont : adaptedCell (roundedGrid jStar nu) t ⊆ centeredCube d M) {eta : ℝ}
    (heta : eta < 1) {F : BlockMat d} (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    (hbridge : BlockMatLoewnerLE
      (blockScale (1 - eta) (adaptedMean P (roundedGrid jStar nu) t)) F) :
    blockSize E F ≤
      kappaRef E * (boundaryConst Cd g nu * ∫ a, Y a ∂P) / (1 - eta) := by
  have heta0 : 0 < 1 - eta := by linarith only [heta]
  have hmeanpd := blockPosDef_adaptedMean_of_isWindowMultiplier hY hnu hq ht hcont
  have hlow := le_of_blockMatLoewnerLE
    (isSymmetricBlockMat_blockScale (1 - eta) (Recurrence.isSymmetricBlockMat_adaptedMean P _ t))
    hF hbridge
  rw [toFullBlockMat_blockScale] at hlow
  have hscaled : toFullBlockMat (adaptedMean P (roundedGrid jStar nu) t) ≤
      (1 - eta)⁻¹ • toFullBlockMat F := by
    have h := smul_le_smul_of_le (inv_nonneg.mpr heta0.le) hlow
    rwa [smul_smul, inv_mul_cancel₀ heta0.ne', one_smul] at h
  have hstep := PortableHistory.blockSize_le_mul_blockSize hE
    (Recurrence.isSymmetricBlockMat_adaptedMean P _ t) hmeanpd hF hFpd
    (inv_nonneg.mpr heta0.le) hscaled
  refine hstep.trans ?_
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left
    (blockSize_adaptedMean_le hCd hg hE hEpd hY hnu hq ht hcont) (inv_nonneg.mpr heta0.le)

/-! ## The terminal loss -/

/-- **The terminal loss** `\E[Y_P]‖Y_P‖_{L^Q} ≤ ‖Y_P‖_{L^Q}^2`, the cost of the
source multiplier in the normalized moments: on a probability space the mean of
a nonnegative variable is below its `L^Q` norm for every `Q ≥ 1`. -/
theorem ofReal_integral_le_lqNorm [IsProbabilityMeasure P]
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {Q : ℝ} (hQ : 1 ≤ Q) :
    ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y := by
  have hint := integrable_of_isWindowMultiplier hY
  have h1 : ENNReal.ofReal (∫ a, Y a ∂P) = eLpNorm Y 1 P := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hint]
    exact congrArg ENNReal.ofReal (integral_congr_ae (_root_.Filter.Eventually.of_forall
      fun a => (Real.norm_of_nonneg (le_trans zero_le_one (hY.one_le a))).symm))
  rw [h1, lqNorm]
  exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.one_le_ofReal.mpr hQ)
    hint.aestronglyMeasurable

/-- The terminal loss in the printed product form. -/
theorem ofReal_integral_mul_lqNorm_le [IsProbabilityMeasure P]
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {Q : ℝ} (hQ : 1 ≤ Q) :
    ENNReal.ofReal (∫ a, Y a ∂P) * lqNorm P Q Y ≤ lqNorm P Q Y ^ 2 := by
  rw [pow_two]
  exact mul_le_mul_left (ofReal_integral_le_lqNorm hY hQ) _

end

end Transport
end HighContrast
end Homogenization
