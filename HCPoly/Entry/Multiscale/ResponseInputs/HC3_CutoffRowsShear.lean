import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportRowsPort
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeOptimizerMean

/-!
# The centred response under the recentring shear

The recentring of the coefficient by a constant skew matrix `g` is the shear congruence `Gᵀ A G`
of the doubled block with `G = ((1, 0), (g, 1))`.  The block response energy of the shear
congruence at the load `(p, r)` is the response energy of the original block at the load
`(p, r - g p)`, and the constant `p. r` of that energy is unchanged because `p. (g p) = 0`.

This file records the corresponding statements for the doubled block-vector multiplication and for
the two terms of the centred response: the block mean of the shear congruence is the block mean of
the original block at the shifted load, with its two slots related by `Y₂ ↦ Y₂ - g Y₁`, so the
centring pairing is shear-invariant because `Y₁. (g Y₁) = 0`.  The centred response therefore
transforms exactly as the block response energy does, which puts the centred responses on the
recentred blocks of `e.response.cutoff.estimate`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The shear congruence `Gᵀ A G` with `G = ((1, 0), (g, 1))` acts on a doubled vector by the
triangular change of variables `(X₁, X₂) ↦ (X₁, g X₁ + X₂)` in the second slot, and then adds the
first slot `gᵀ` times the second slot of the image: the first component of the image is
`(A (X₁, g X₁ + X₂))₁ + gᵀ (A (X₁, g X₁ + X₂))₂` and the second component is
`(A (X₁, g X₁ + X₂))₂`. -/
theorem blockMatVecMul_blockCongr_shear {d : ℕ} (A : BlockMat d) (g : Mat d) (X : BlockVec d) :
    blockMatVecMul (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) X
      = ((blockMatVecMul A (X.1, matVecMul g X.1 + X.2)).1
            + matVecMul (matTranspose g) (blockMatVecMul A (X.1, matVecMul g X.1 + X.2)).2,
         (blockMatVecMul A (X.1, matVecMul g X.1 + X.2)).2) := by
  rcases X with ⟨x1, x2⟩
  rw [blockCongr_shear]
  refine Prod.ext ?_ ?_
  · simp only [blockMatVecMul_fst, blockMatVecMul_snd, add_matVecMul, matVecMul_add,
      ← matVecMul_mul]
    abel
  · simp only [blockMatVecMul_snd, add_matVecMul, matVecMul_add, ← matVecMul_mul]
    abel

/-- The centring pairing of the block mean is invariant under the shear congruence
`G = ((1, 0), (g, 1))` with `g` skew.  Writing `Z = A (-p, r - g p)`, the mean of the shear
congruence at the load `(-p, r)` has slots `(-p + Z₂, r + Z₁ + gᵀ Z₂)` while the mean of `A` at the
shifted load `(-p, r - g p)` has slots `(-p + Z₂, r - g p + Z₁)`, and the second slots differ by
`-g (-p + Z₂)`, whose pairing against `-p + Z₂` vanishes because `g` is skew.  This is the
centring half of the recentring of Step 4 of the response argument
(`e.response.cutoff.estimate`). -/
theorem vecDot_blockResponseMean_blockCongr_shear {d : ℕ} (A : BlockMat d) {g : Mat d}
    (hg : matTranspose g = -g) (p r : Vec d) :
    vecDot (blockResponseMean (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) (-p, r)).1
        (blockResponseMean (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) (-p, r)).2
      = vecDot (blockResponseMean A (-p, r - matVecMul g p)).1
          (blockResponseMean A (-p, r - matVecMul g p)).2 := by
  set Z : BlockVec d := blockMatVecMul A (-p, r - matVecMul g p) with hZ
  have harg : (matVecMul g (-p) + r : Vec d) = r - matVecMul g p := by
    rw [matVecMul_neg]
    abel
  have hW : blockMatVecMul (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) (-p, r)
      = (Z.1 + matVecMul (matTranspose g) Z.2, Z.2) := by
    rw [blockMatVecMul_blockCongr_shear]
    simp only [harg, ← hZ]
  have hmeanL : blockResponseMean (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) (-p, r)
      = (-p + Z.2, r + Z.1 + matVecMul (matTranspose g) Z.2) := by
    unfold blockResponseMean
    rw [hW]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, blockMatVecMul_blockSwap_fst]
    · simp only [Prod.snd_add, blockMatVecMul_blockSwap_snd, add_assoc]
  have hmeanR : blockResponseMean A (-p, r - matVecMul g p)
      = (-p + Z.2, r - matVecMul g p + Z.1) := by
    unfold blockResponseMean
    rw [← hZ]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, blockMatVecMul_blockSwap_fst]
    · simp only [Prod.snd_add, blockMatVecMul_blockSwap_snd]
  have hskew : ∀ v : Vec d, vecDot v (matVecMul g v) = 0 := by
    intro v
    have h1 : vecDot v (matVecMul (matTranspose g) v) = vecDot (matVecMul g v) v :=
      _root_.Homogenization.vecDot_matVecMul_transpose v v g
    rw [hg, neg_matVecMul, vecDot_neg_right, vecDot_comm (matVecMul g v) v] at h1
    linarith only [h1]
  have hM2 : (r + Z.1 + matVecMul (matTranspose g) Z.2 : Vec d)
      = (r - matVecMul g p + Z.1) - matVecMul g ((-p) + Z.2) := by
    rw [hg, neg_matVecMul, matVecMul_add, matVecMul_neg]
    abel
  rw [hmeanL, hmeanR]
  dsimp only
  simp only [hM2, sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, hskew, neg_zero, add_zero]

/-- The centred response is invariant under the shear recentring:
`blockCenteredResponse (Gᵀ A G) p r = blockCenteredResponse A p (r - g p)` for the constant shear
`G = ((1, 0), (g, 1))` with `g` skew.  The energy term transforms by
`blockResponseEnergy_blockCongr_shear` and the centring pairing by shear invariance, so the centred
responses on the recentred blocks and on the original blocks are the same scalar.  This is the
passage from the centred responses to the annealed energies of
`e.response.cutoff.estimate`. -/
theorem blockCenteredResponse_blockCongr_shear {d : ℕ} (A : BlockMat d) {g : Mat d}
    (hg : matTranspose g = -g) (p r : Vec d) :
    blockCenteredResponse (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) p r
      = blockCenteredResponse A p (r - matVecMul g p) := by
  unfold blockCenteredResponse
  rw [blockResponseEnergy_blockCongr_shear A hg p r,
    vecDot_blockResponseMean_blockCongr_shear A hg p r]

end

end Homogenization.HighContrast.Multiscale
