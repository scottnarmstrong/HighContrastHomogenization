import HCPoly.Entry.Setup.Attainment
import HCPoly.Entry.Setup.BlockCalculus
import HCPoly.Entry.Analysis.SchattenSpectral
import HCPoly.Entry.Multiscale.DriftAdvance

/-!
# Reference block comparison

These are deterministic bounds for the block carriers and reference constants.
The source statements are near `e.reference.aspect.ratio` and `e.two.grid.whitney.source`,
`p.initial.fixed.grid.scale` and `p.global.selection`.
The source argument is Lemma `l.bfE.bounds` of the companion paper HC.

Reference order remains an explicit premise; this module does not derive it from the dagger.
Schur factorization identifies the inverse flux block, giving `1 ≤ refContrast E`.
An attained skew minimizer gives `refContrast E ≤ aspectRatio E` and strictly positive
reference constants. For the comparison, positive block quadratic forms give domination by
twice the scalar diagonal bounds after a skew shear. Inversion and reflection then give a
`4 * aspectRatio E` bound, which implies the exported, literal `6 * aspectRatio E` bound.
This is the direct route: the sharper HC excess estimate `e.grok`
with coefficient `1 + 6 * (refContrast E - 1)` is not delivered.

The determinant is the ordinary determinant of the full `2d` matrix. Its comparison with the
reciprocal determinant first bounds its square and therefore gives the printed exponent `d`.
The weaker exponent `2 * d` is recorded separately.
No probability law, quantitative ellipticity constant, or annealed premise enters these bounds.
-/

open Homogenization.HighContrast (IsSkewMat aspectRatio bigLambdaRef blockContrast
  blockContrast_le blockScale blockVecDot_inr exists_isSkewMat_bigLambdaRef_eq
  exists_isSkewMat_blockContrast_eq isUnit_det_lowerRight lambdaRef matLoewnerLE_smul_iff_conj
  matLoewnerLE_specBound_smul_one matSqrt matSqrt_lowerRight_spec posDef_lowerRight refContrast
  schurSigma schurSigmaStar schurSkew skewCorrectedForm specBound)
namespace Homogenization.HighContrast.Analysis

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section
variable {d : ℕ}

private theorem hermitian_smul {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : M.IsHermitian) (c : ℝ) : (c • M).IsHermitian := by
  change (c • M)ᴴ = c • M
  rw [Matrix.conjTranspose_smul, star_trivial, hM.eq]

private theorem full_eq (E : BlockMat d) :
    toFullBlockMat E = Matrix.fromBlocks E.upperLeft E.upperRight E.lowerLeft E.lowerRight := by
  ext (i | i) (j | j) <;> rfl

private theorem full_pos {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) : (toFullBlockMat E).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ((toFullBlockMat_isHermitian_iff E).2 hs) ?_
  intro x hx
  have hn : ofFullBlockVec x ≠ 0 := by
    intro h
    apply hx
    have hz := congrArg toFullBlockVec h
    rw [toFullBlockVec_ofFullBlockVec] at hz
    funext i
    have hi := congrFun hz i
    cases i <;> simpa [toFullBlockVec] using hi
  simpa only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockVec_ofFullBlockVec, star_trivial] using hp (ofFullBlockVec x) hn

private theorem full_le_iff {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian) :
    toFullBlockMat A ≤ toFullBlockMat B ↔ BlockMatLoewnerLE A B := by
  constructor
  · intro h X
    have hn := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg (toFullBlockVec X)
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hn
    have heA := dotProduct_toFullBlockVec X (blockMatVecMul A X)
    have heB := dotProduct_toFullBlockVec X (blockMatVecMul B X)
    rw [toFullBlockVec_blockMatVecMul] at heA heB
    rw [heA, heB] at hn
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hn) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · intro h
    apply Matrix.le_iff.mpr
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
    intro x
    have hx := h (ofFullBlockVec x)
    simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
      toFullBlockVec_ofFullBlockVec] at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith only [hx]

private theorem matrix_inv_antitone {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) (hle : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  have hD : (A⁻¹ - B⁻¹).IsHermitian := hA.inv.isHermitian.sub hB.inv.isHermitian
  have h₁ := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  have h₂ := (Matrix.le_iff.mp hle).conjTranspose_mul_mul_same B⁻¹
  rw [hD.eq] at h₁
  rw [hB.inv.isHermitian.eq] at h₂
  apply Matrix.le_iff.mpr
  convert h₁.add h₂ using 1 <;> try rfl
  have hAiA := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hAAi := Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hBiB := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit)
  simp only [mul_sub, sub_mul, hAiA, hBiB, one_mul]
  rw [mul_assoc B⁻¹ A A⁻¹, hAAi, mul_one]
  abel

/-- The reflection block is symmetric. -/
theorem isSymmetricBlockMat_blockSwap (d : ℕ) : IsSymmetricBlockMat (blockSwap d) := by
  intro a b
  cases a <;> cases b <;>
    simp [blockSwap, Book.Ch02.blockR, blockMatEntry, Matrix.one_apply, eq_comm]

private theorem swap_full (d : ℕ) :
    toFullBlockMat (blockSwap d) = Matrix.fromBlocks (0 : Mat d) 1 1 0 := by
  rw [full_eq]
  rfl

/-- The reflection block is an involution. -/
theorem toFullBlockMat_blockSwap_mul_self (d : ℕ) :
    toFullBlockMat (blockSwap d) * toFullBlockMat (blockSwap d) = 1 := by
  rw [swap_full, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, one_mul, zero_add, add_zero, Matrix.fromBlocks_one]

/-- Literal reflection products agree with the CG block reflection. -/
theorem swapConj_eq_blockReflect (F : BlockMat d) :
    ofFullBlockMat (toFullBlockMat (blockSwap d) * toFullBlockMat F *
      toFullBlockMat (blockSwap d)) = blockReflect F := by
  rw [swap_full, full_eq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
  rfl

/-- The inverse instance of the reflection identity. -/
theorem swapConj_inv_eq_blockReflect (F : BlockMat d) :
    ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat F)⁻¹ *
      toFullBlockMat (blockSwap d)) = blockReflect (ofFullBlockMat (toFullBlockMat F)⁻¹) := by
  simpa only [toFullBlockMat_ofFullBlockMat] using
    swapConj_eq_blockReflect (ofFullBlockMat (toFullBlockMat F)⁻¹)

private theorem swap_fromBlocks (A B C D : Mat d) :
    toFullBlockMat (blockSwap d) * Matrix.fromBlocks A B C D *
      toFullBlockMat (blockSwap d) = Matrix.fromBlocks D C B A := by
  have h := congrArg toFullBlockMat
    (swapConj_eq_blockReflect (ofFullBlockMat (Matrix.fromBlocks A B C D)))
  calc
    _ = toFullBlockMat (blockReflect (ofFullBlockMat (Matrix.fromBlocks A B C D))) := by
      simpa only [toFullBlockMat_ofFullBlockMat] using h
    _ = _ := by ext (i | i) (j | j) <;> rfl

private theorem swap_hermitian (d : ℕ) : (toFullBlockMat (blockSwap d)).IsHermitian :=
  (toFullBlockMat_isHermitian_iff _).2 (isSymmetricBlockMat_blockSwap d)

/-- The adjoint reference block is positive definite in the full matrix carrier. -/
theorem swapConj_posDef {F : BlockMat d} (hp : (toFullBlockMat F).PosDef) :
    (toFullBlockMat (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat F)⁻¹ * toFullBlockMat (blockSwap d)))).PosDef := by
  rw [toFullBlockMat_ofFullBlockMat]
  have hu : IsUnit (toFullBlockMat (blockSwap d)) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (Matrix.isUnit_det_of_right_inverse (toFullBlockMat_blockSwap_mul_self d))
  simpa only [(swap_hermitian d).eq] using
    (Matrix.posDef_inv_iff.2 hp).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hu)

private theorem shear_full (h : Mat d) :
    toFullBlockMat (Book.Ch02.blockG h) = Matrix.fromBlocks (1 : Mat d) 0 h 1 := by
  rw [full_eq]
  rfl

private theorem shear_mul_neg (h : Mat d) :
    toFullBlockMat (Book.Ch02.blockG h) * toFullBlockMat (Book.Ch02.blockG (-h)) = 1 := by
  rw [shear_full, shear_full, Matrix.fromBlocks_multiply]
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add,
    add_neg_cancel, Matrix.fromBlocks_one]

private theorem shear_unit (h : Mat d) : IsUnit (toFullBlockMat (Book.Ch02.blockG h)) :=
  (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (shear_mul_neg h))

private theorem shear_inv (h : Mat d) :
    (toFullBlockMat (Book.Ch02.blockG h))⁻¹ = toFullBlockMat (Book.Ch02.blockG (-h)) :=
  Matrix.inv_eq_right_inv (shear_mul_neg h)

private theorem shear_swapConj (E : BlockMat d) (h : Mat d) (hh : IsSkewMat h) :
    (toFullBlockMat (Book.Ch02.blockG h))ᴴ *
      (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)) *
      toFullBlockMat (Book.Ch02.blockG h) =
    toFullBlockMat (blockSwap d) *
      ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
        toFullBlockMat (Book.Ch02.blockG h))⁻¹ * toFullBlockMat (blockSwap d) := by
  have hleft : (toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat (blockSwap d) =
      toFullBlockMat (blockSwap d) * (toFullBlockMat (Book.Ch02.blockG h))⁻¹ := by
    rw [shear_inv]
    rw [shear_full, shear_full, swap_full, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    have hh' : hᴴ = -h := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! hh
    simp only [hh', Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add]
  have hright := congrArg Matrix.conjTranspose hleft
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (swap_hermitian d).eq, Matrix.conjTranspose_nonsing_inv] at hright
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  calc
    _ = ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat (blockSwap d)) *
        (toFullBlockMat E)⁻¹ * (toFullBlockMat (blockSwap d) *
          toFullBlockMat (Book.Ch02.blockG h)) := by simp only [mul_assoc]
    _ = _ := by rw [hleft, hright]; simp only [mul_assoc]

private theorem schur_cancel {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) :
    E.lowerRight * schurSkew E = -E.lowerLeft ∧
      (schurSkew E)ᴴ * E.lowerRight = -E.upperRight := by
  have hD : E.lowerRightᴴ = E.lowerRight := (posDef_lowerRight hs hp).isHermitian.eq
  have hC : E.lowerLeftᴴ = E.upperRight := by
    ext i j
    exact hs (Sum.inr j) (Sum.inl i)
  have hk : E.lowerRight * schurSkew E = -E.lowerLeft := by
    rw [schurSkew, mul_neg, ← mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_det_lowerRight hp), one_mul]
  have hk' : (schurSkew E)ᴴ * E.lowerRight = -E.upperRight := by
    have hkt := congrArg Matrix.conjTranspose hk
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, hD, hC] using hkt
  exact ⟨hk, hk'⟩

private theorem skewCorrectedForm_eq {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    skewCorrectedForm E h = E.upperLeft + E.upperRight * h +
      hᴴ * E.lowerLeft + hᴴ * E.lowerRight * h := by
  obtain ⟨hk, hk'⟩ := schur_cancel hs hp
  change E.upperLeft - (schurSkew E)ᵀ * E.lowerRight * schurSkew E +
    (schurSkew E - h)ᵀ * E.lowerRight * (schurSkew E - h) = _
  simp only [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.conjTranspose_sub,
    mul_sub, sub_mul]
  rw [hk', mul_assoc hᴴ E.lowerRight, hk]
  simp only [neg_mul, mul_neg]
  abel

private theorem shear_blocks {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    (toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
      toFullBlockMat (Book.Ch02.blockG h) =
    Matrix.fromBlocks (skewCorrectedForm E h) (E.upperRight + hᴴ * E.lowerRight)
      (E.lowerLeft + E.lowerRight * h) E.lowerRight := by
  rw [shear_full, full_eq, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, skewCorrectedForm_eq hs hp]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, one_mul, mul_one,
    zero_mul, mul_zero, zero_add, add_mul]
  congr 1
  abel

private theorem shear_pos {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    ((toFullBlockMat (Book.Ch02.blockG h))ᴴ * toFullBlockMat E *
      toFullBlockMat (Book.Ch02.blockG h)).PosDef :=
  (full_pos hs hp).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (shear_unit h))

private theorem mat_le_iff {A B : Mat d} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    A ≤ B ↔ MatLoewnerLE A B := by
  constructor
  · intro h x
    have ht := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at ht
    exact mul_le_mul_of_nonneg_left (sub_nonneg.mp ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · intro h
    refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_)
    intro x
    have hx := h x
    change 1 / 2 * (x ⬝ᵥ A.mulVec x) ≤ 1 / 2 * (x ⬝ᵥ B.mulVec x) at hx
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
    linarith only [hx]

private theorem upper_pos {A B C D : Mat d} (hp : (Matrix.fromBlocks A B C D).PosDef) :
    A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hp.isHermitian.submatrix Sum.inl) ?_
  intro x hx
  have hx' : Sum.elim x (0 : Vec d) ≠ 0 := by
    intro he
    exact hx (congrArg (fun f => f ∘ Sum.inl) he)
  have h := hp.dotProduct_mulVec_pos hx'
  simpa only [star_trivial, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Matrix.mulVec_zero, add_zero, sumElim_dotProduct_sumElim,
    zero_dotProduct] using h

private theorem corrected_pos {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) : (skewCorrectedForm E h).PosDef := by
  have he := shear_pos hs hp h
  rw [shear_blocks hs hp] at he
  exact upper_pos he

private theorem specBound_pos [NeZero d] {A : Mat d} (hp : A.PosDef) : 0 < specBound A := by
  let i : Fin d := ⟨0, NeZero.pos d⟩
  have ht := (matLoewnerLE_smul_one_iff A (specBound A)).1
    (matLoewnerLE_specBound_smul_one A) (Pi.single i 1)
  have ht' : A i i ≤ specBound A := by
    simpa [vecDot, vecNormSq, matVecMul, Pi.single_apply, mul_ite,
      Finset.sum_ite_eq'] using ht
  exact hp.diag_pos.trans_le ht'

/-- The reference lower ellipticity constant is strictly positive. -/
theorem lambdaRef_pos [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) : 0 < lambdaRef E :=
  inv_pos.mpr (specBound_pos (posDef_lowerRight hsymm hpos))

/-- The attained reference upper ellipticity constant is strictly positive. -/
theorem bigLambdaRef_pos [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) : 0 < bigLambdaRef E := by
  obtain ⟨h, _, he⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  rw [he]
  exact specBound_pos (corrected_pos hsymm hpos h)

private theorem scalar_inv (c : ℝ) (hc : c ≠ 0) :
    (c • (1 : Mat d))⁻¹ = c⁻¹ • (1 : Mat d) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, one_mul]

/-- Minimizing the intrinsic contrast is bounded by the product of the two reference norms. -/
theorem refContrast_le_aspectRatio [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E) :
    refContrast E ≤ aspectRatio E := by
  obtain ⟨h, hh, hΛ⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  have hD := posDef_lowerRight hsymm hpos
  have hL := specBound_pos hD
  have hΛpos := bigLambdaRef_pos hsymm hpos
  have hDle : E.lowerRight ≤ specBound E.lowerRight • (1 : Mat d) :=
    (mat_le_iff hD.isHermitian (hermitian_smul Matrix.isHermitian_one _)).2
      (matLoewnerLE_specBound_smul_one E.lowerRight)
  have hDi := matrix_inv_antitone hD (Matrix.PosDef.one.smul hL) hDle
  rw [scalar_inv _ hL.ne'] at hDi
  have hstep := smul_le_smul_of_nonneg_left hDi (mul_nonneg hΛpos.le hL.le)
  have hcancel : (bigLambdaRef E * specBound E.lowerRight) •
      ((specBound E.lowerRight)⁻¹ • (1 : Mat d)) = bigLambdaRef E • (1 : Mat d) := by
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hL.ne', mul_one]
  rw [hcancel] at hstep
  have hKle : skewCorrectedForm E h ≤ bigLambdaRef E • (1 : Mat d) := by
    apply (mat_le_iff (corrected_pos hsymm hpos h).isHermitian
      (hermitian_smul Matrix.isHermitian_one _)).2
    rw [hΛ]
    exact matLoewnerLE_specBound_smul_one _
  change blockContrast E ≤ bigLambdaRef E / (specBound E.lowerRight)⁻¹
  rw [div_inv_eq_mul]
  exact blockContrast_le (mul_nonneg hΛpos.le hL.le) hh
    ((mat_le_iff (corrected_pos hsymm hpos h).isHermitian
      (hermitian_smul hD.inv.isHermitian _)).1 (hKle.trans hstep))

private theorem schur_factorization {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) :
    toFullBlockMat E = (toFullBlockMat (Book.Ch02.blockG (-schurSkew E)))ᴴ *
      Matrix.fromBlocks (schurSigma E) 0 0 E.lowerRight *
        toFullBlockMat (Book.Ch02.blockG (-schurSkew E)) := by
  obtain ⟨hk, hk'⟩ := schur_cancel hs hp
  rw [full_eq, shear_full, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.conjTranspose_neg, one_mul, mul_one, zero_mul, mul_zero,
    add_zero, zero_add, neg_mul, mul_neg, neg_neg, hk, hk']
  congr 1
  change E.upperLeft = E.upperLeft - (schurSkew E)ᵀ * E.lowerRight * schurSkew E +
    -(E.upperRight * schurSkew E)
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hk']
  simp only [neg_mul]
  abel

private theorem schur_pos {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) : (schurSigma E).PosDef := by
  simpa only [skewCorrectedForm, sub_self, matTranspose, Matrix.transpose_zero, zero_mul, add_zero]
    using corrected_pos hs hp (schurSkew E)

private theorem diagonal_inv {A D : Mat d} (hA : A.PosDef) (hD : D.PosDef) :
    (Matrix.fromBlocks A 0 0 D)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul, mul_zero, add_zero, zero_add,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),
    Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det _).mp hD.isUnit),
    Matrix.fromBlocks_one]

/-- The lower-right block of the swap-conjugated inverse is the inverse Schur complement
`(schurSigma E)⁻¹`.  This is the Schur factorization read off the reflected inverse. -/
theorem swapConj_lowerRight {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) :
    (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
      toFullBlockMat (blockSwap d))).lowerRight = (schurSigma E)⁻¹ := by
  rw [swapConj_inv_eq_blockReflect, blockReflect_lowerRight]
  rw [schur_factorization hs hp, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← Matrix.conjTranspose_nonsing_inv, shear_inv, neg_neg,
    diagonal_inv (schur_pos hs hp) (posDef_lowerRight hs hp)]
  rw [shear_full, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, one_mul, mul_one,
    zero_mul, mul_zero, add_zero, zero_add]
  rfl

private theorem schurSigmaStar_le_schurSigma {E : BlockMat d}
    (hs : IsSymmetricBlockMat E) (hp : Book.Ch02.BlockPosDef E)
    (ho : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    schurSigmaStar E ≤ schurSigma E := by
  have hflux : MatLoewnerLE ((schurSigma E)⁻¹) E.lowerRight := by
    intro x
    have h := ho (0, x)
    simp only [blockVecDot_inr] at h
    rw [swapConj_lowerRight hs hp] at h
    exact h
  have hi := matrix_inv_antitone (schur_pos hs hp).inv (posDef_lowerRight hs hp)
    ((mat_le_iff (schur_pos hs hp).inv.isHermitian
      (posDef_lowerRight hs hp).isHermitian).2 hflux)
  simpa only [Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (schur_pos hs hp).isUnit), schurSigmaStar] using hi

/-- The Schur complement is dominated in the Loewner order by every skew-corrected form:
`schurSigma E ≤ skewCorrectedForm E h` for an arbitrary skew correction `h`. -/
theorem schurSigma_le_corrected {E : BlockMat d} (hs : IsSymmetricBlockMat E)
    (hp : Book.Ch02.BlockPosDef E) (h : Mat d) :
    schurSigma E ≤ skewCorrectedForm E h := by
  apply Matrix.le_iff.mpr
  have hq := (posDef_lowerRight hs hp).posSemidef.conjTranspose_mul_mul_same (schurSkew E - h)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, skewCorrectedForm,
    add_sub_cancel_left] using! hq

/-- Reference order forces the attained intrinsic contrast to be at least one. -/
theorem one_le_refContrast [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    1 ≤ refContrast E := by
  obtain ⟨h, _, he⟩ := exists_isSkewMat_blockContrast_eq hsymm hpos
  obtain ⟨hRs, hRdet, hRR⟩ := matSqrt_lowerRight_spec hsymm hpos
  have htconj := matLoewnerLE_specBound_smul_one
    (matSqrt E.lowerRight * skewCorrectedForm E h * matSqrt E.lowerRight)
  rw [← he] at htconj
  have ht : MatLoewnerLE (skewCorrectedForm E h) (refContrast E • schurSigmaStar E) :=
    (matLoewnerLE_smul_iff_conj hRs hRR hRdet (refContrast E)).2 htconj
  have hl := (schurSigmaStar_le_schurSigma hsymm hpos horder).trans
    (schurSigma_le_corrected hsymm hpos h)
  have hu := (mat_le_iff (corrected_pos hsymm hpos h).isHermitian
    (hermitian_smul (posDef_lowerRight hsymm hpos).inv.isHermitian _)).2 ht
  have hboth := Matrix.le_iff.mp (hl.trans hu)
  let x : Vec d := Pi.single ⟨0, NeZero.pos d⟩ 1
  have hx : x ≠ 0 := by simp [x]
  have hq := (posDef_lowerRight hsymm hpos).inv.dotProduct_mulVec_pos hx
  have htq := hboth.dotProduct_mulVec_nonneg x
  simp only [star_trivial, schurSigmaStar, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at htq hq
  nlinarith only [htq, hq]

/-- The printed aspect ratio lower bound, under reference order. -/
theorem one_le_aspectRatio [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    1 ≤ aspectRatio E :=
  (one_le_refContrast hsymm hpos horder).trans (refContrast_le_aspectRatio hsymm hpos)

/-- Positivity and the lower bound for the logarithmic argument used downstream. -/
theorem aspectRatio_pos_and_three_le [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    0 < aspectRatio E ∧ 3 ≤ 2 + aspectRatio E := by
  have h := one_le_aspectRatio hsymm hpos horder
  constructor <;> linarith only [h]

private theorem scalar_diag_eq (a b : ℝ) :
    Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin d => a) (fun _ : Fin d => b)) := by
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.diagonal, Matrix.one_apply]

private theorem scalar_diag_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d))).PosDef := by
  rw [scalar_diag_eq]
  exact Matrix.PosDef.diagonal (fun i => by cases i <;> assumption)

private theorem scalar_diag_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Matrix.fromBlocks (a • (1 : Mat d)) 0 0 (b • (1 : Mat d)))⁻¹ =
      Matrix.fromBlocks (a⁻¹ • (1 : Mat d)) 0 0 (b⁻¹ • (1 : Mat d)) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha, inv_mul_cancel₀ hb,
    one_smul, one_mul, Matrix.fromBlocks_one]

private theorem two_diag_bound {A B C D : Mat d}
    (hp : (Matrix.fromBlocks A B C D).PosSemidef) {a b : ℝ}
    (ha : A ≤ a • (1 : Mat d)) (hb : D ≤ b • (1 : Mat d)) :
    Matrix.fromBlocks A B C D ≤
      Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)) := by
  have hdiag : (Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0
      ((2 * b) • (1 : Mat d))).IsHermitian := by
    rw [scalar_diag_eq]
    exact Matrix.isHermitian_diagonal _
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hdiag.sub hp.isHermitian) ?_)
  intro x
  have h0 := hp.dotProduct_mulVec_nonneg (Sum.elim (x ∘ Sum.inl) (-(x ∘ Sum.inr)))
  have h1 := (Matrix.le_iff.mp ha).dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h2 := (Matrix.le_iff.mp hb).dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h1 h2
  rw [← Sum.elim_comp_inl_inr x]
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg, Matrix.zero_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, zero_add, add_zero,
    sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_sub,
    dotProduct_neg, neg_dotProduct, dotProduct_smul, smul_eq_mul] at h0 ⊢
  linarith only [h0, h1, h2]

private theorem four_product_bound {A B C D : Mat d}
    (hp : (Matrix.fromBlocks A B C D).PosDef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : A ≤ a • (1 : Mat d)) (hD : D ≤ b • (1 : Mat d)) :
    Matrix.fromBlocks A B C D ≤ (4 * a * b) •
      (toFullBlockMat (blockSwap d) * (Matrix.fromBlocks A B C D)⁻¹ *
        toFullBlockMat (blockSwap d)) := by
  have ha2 : 0 < 2 * a := mul_pos (by norm_num) ha
  have hb2 : 0 < 2 * b := mul_pos (by norm_num) hb
  have hu := two_diag_bound hp.posSemidef hA hD
  have hi := matrix_inv_antitone hp (scalar_diag_pos ha2 hb2) hu
  have hr := star_left_conjugate_le_conjugate hi (toFullBlockMat (blockSwap d))
  rw [show star (toFullBlockMat (blockSwap d)) = toFullBlockMat (blockSwap d)
    from (swap_hermitian d).eq] at hr
  have hscale := smul_le_smul_of_nonneg_left hr (by positivity : 0 ≤ 4 * a * b)
  have heq : (4 * a * b) • (toFullBlockMat (blockSwap d) *
      (Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)))⁻¹ *
        toFullBlockMat (blockSwap d)) =
      Matrix.fromBlocks ((2 * a) • (1 : Mat d)) 0 0 ((2 * b) • (1 : Mat d)) := by
    rw [scalar_diag_inv ha2.ne' hb2.ne', swap_fromBlocks]
    simp only [Matrix.fromBlocks_smul, smul_zero, smul_smul]
    congr 2 <;> field_simp [ha.ne', hb.ne'] <;> ring
  rw [heq] at hscale
  exact hu.trans hscale

private theorem full_scale (c : ℝ) (E : BlockMat d) :
    toFullBlockMat (blockScale c E) = c • toFullBlockMat E := by
  ext (i | i) (j | j) <;> rfl

/-- The printed factor-six comparison. The proof uses diagonal domination after an attained
skew shear, directly; the sharper HC excess estimate `e.grok` is not asserted here. -/
theorem refBlock_le_six_aspectRatio_smul_swapConj [NeZero d] {E : BlockMat d}
    (hsymm : IsSymmetricBlockMat E) (hpos : Book.Ch02.BlockPosDef E)
    (horder : BlockMatLoewnerLE (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d))) E) :
    BlockMatLoewnerLE E (blockScale (6 * aspectRatio E)
      (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
        toFullBlockMat (blockSwap d)))) := by
  obtain ⟨h, hh, hΛ⟩ := exists_isSkewMat_bigLambdaRef_eq hpos
  have hp := full_pos hsymm hpos
  have hD := posDef_lowerRight hsymm hpos
  have hΛpos := bigLambdaRef_pos hsymm hpos
  have hLpos := specBound_pos hD
  have hA : skewCorrectedForm E h ≤ bigLambdaRef E • (1 : Mat d) := by
    apply (mat_le_iff (corrected_pos hsymm hpos h).isHermitian
      (hermitian_smul Matrix.isHermitian_one _)).2
    rw [hΛ]
    exact matLoewnerLE_specBound_smul_one _
  have hDle : E.lowerRight ≤ specBound E.lowerRight • (1 : Mat d) :=
    (mat_le_iff hD.isHermitian (hermitian_smul Matrix.isHermitian_one _)).2
      (matLoewnerLE_specBound_smul_one _)
  have hsp := shear_pos hsymm hpos h
  rw [shear_blocks hsymm hpos] at hsp
  have hfour := four_product_bound hsp hΛpos hLpos hA hDle
  rw [← shear_blocks hsymm hpos, ← shear_swapConj E h hh] at hfour
  have hπ : aspectRatio E = bigLambdaRef E * specBound E.lowerRight := by
    simp only [aspectRatio, lambdaRef, div_inv_eq_mul]
  have hfull : toFullBlockMat E ≤ (4 * aspectRatio E) •
      (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)) := by
    apply Matrix.le_iff.mpr
    apply (shear_unit h).posSemidef_star_left_conjugate_iff.mp
    have hs := Matrix.le_iff.mp hfour
    simpa only [Matrix.star_eq_conjTranspose, mul_sub, sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hπ, mul_assoc] using hs
  have hπ0 := (aspectRatio_pos_and_three_le hsymm hpos horder).1.le
  have hspos := swapConj_posDef hp
  have hlast := smul_le_smul_of_nonneg_right
    (by linarith only [hπ0] : 4 * aspectRatio E ≤ 6 * aspectRatio E)
    (by simpa only [toFullBlockMat_ofFullBlockMat] using hspos.posSemidef.nonneg)
  apply (full_le_iff hp.isHermitian (by
    rw [full_scale]; exact hermitian_smul hspos.isHermitian _)).1
  simpa only [full_scale, toFullBlockMat_ofFullBlockMat] using hfull.trans hlast

/-- Reflection preserves the inverse determinant; no normalized determinant convention is used. -/
theorem det_swapConj (E : BlockMat d) :
    (toFullBlockMat (ofFullBlockMat (toFullBlockMat (blockSwap d) *
      (toFullBlockMat E)⁻¹ * toFullBlockMat (blockSwap d)))).det = (toFullBlockMat E).det⁻¹ := by
  have hR := congrArg Matrix.det (toFullBlockMat_blockSwap_mul_self d)
  rw [Matrix.det_mul, Matrix.det_one] at hR
  simp only [toFullBlockMat_ofFullBlockMat, Matrix.det_mul, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv]
  calc
    _ = ((toFullBlockMat (blockSwap d)).det * (toFullBlockMat (blockSwap d)).det) *
      (toFullBlockMat E).det⁻¹ := by ring
    _ = _ := by rw [hR, one_mul]

end
end Homogenization.HighContrast.Analysis
