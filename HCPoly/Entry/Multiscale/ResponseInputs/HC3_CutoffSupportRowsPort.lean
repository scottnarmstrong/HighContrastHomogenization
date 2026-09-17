import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportEnergies
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportEnergiesPlus
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# The shear form of the annealed energies of the cutoff rows

The cutoff rows of the response estimate bound the centred response `Jtilde^±(e)` by expressions
in the expectation of the recentred pathwise response, its scale defect, and the source load
(`e.response.cutoff.estimate`, AK.HC (3.45)–(3.54)).  The centred response itself is defined on the
annealed block `E_t` of the original coefficient, while the two energy scalars are the block
energies of the recentred blocks `Ehat_t^∓`.  The two objects are compared only after the algebraic
step recorded here.

The recentring `a_∓ = a ∓ g` is the constant shear `G^t A G` of the doubled block, and the shear
moves the flux load: the block response energy of the shear congruence at a load `(p, r)` is the
response energy of the original block at the load `(p, r - g p)`.  Since `g` is skew, the pairing
`p. g p` vanishes, so the constant `p. q'` of the energy is unchanged and the identity is exact.
This is the algebraic half of the recentring of Step 4 of the response argument, and the first step
that puts the recentred block energies on the same footing as the centred response.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- An auxiliary identity: the quadratic form of a skew matrix vanishes, `ξ. (g ξ) = 0` whenever
`gᵀ = -g`.  This is what makes the shear shift load-independent. -/
private theorem vecDot_matVecMul_skew_self {d : ℕ} {g : Mat d}
    (hg : matTranspose g = -g) (ξ : Vec d) : vecDot ξ (matVecMul g ξ) = 0 := by
  have h1 := vecDot_matVecMul_transpose ξ ξ g
  rw [hg] at h1
  have hneg : matVecMul (-g) ξ = -matVecMul g ξ := neg_matVecMul g ξ
  rw [hneg, vecDot_neg_right, vecDot_comm (matVecMul g ξ) ξ] at h1
  linarith only [h1]

/-- **The shear congruence shifts the flux load in the block response energy.**  For the constant
shear `G = ((1, 0), (g, 1))` with `g` skew and any doubled block `A`, the response energy of the
shear congruence at the load `(p, r)` is the response energy of `A` at the load
`(p, r - g p)`:
`blockResponseEnergy (Gᵀ A G) p r = blockResponseEnergy A p (r - matVecMul g p)`.
The constant `p. r` of the energy is unchanged because `p. (g p) = 0`.  This is the algebraic
content of the recentring of the coefficient in Step 4 of the response argument
(`e.response.cutoff.estimate`). -/
theorem blockResponseEnergy_blockCongr_shear {d : ℕ} (A : BlockMat d) {g : Mat d}
    (hg : matTranspose g = -g) (p r : Vec d) :
    blockResponseEnergy (blockCongr (⟨1, 0, g, 1⟩ : BlockMat d) A) p r
      = blockResponseEnergy A p (r - matVecMul g p) := by
  have hpg : vecDot p (matVecMul g p) = 0 := vecDot_matVecMul_skew_self hg p
  have hGx : blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) (-p, r)
      = (-p, r - matVecMul g p) := by
    refine Prod.ext ?_ ?_
    · funext i
      rw [blockMatVecMul_fst]
      change ((1 : Mat d).mulVec (-p) + (0 : Mat d).mulVec r) i = (-p) i
      rw [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    · funext i
      rw [blockMatVecMul_snd]
      change (matVecMul g (-p) + (1 : Mat d).mulVec r) i = (r - matVecMul g p) i
      rw [matVecMul_neg, Matrix.one_mulVec]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      ring
  unfold blockResponseEnergy
  rw [blockVecDot_blockCongr, hGx]
  rw [show vecDot p r = vecDot p (r - matVecMul g p) by
    rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right, hpg, neg_zero, add_zero]]

end

end Homogenization.HighContrast.Multiscale
