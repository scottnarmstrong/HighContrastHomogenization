import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Setup.BlockAlgebra
import HCPoly.Entry.Setup.BlockCalculus
import Homogenization.Ambient.CoefficientField
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra

/-!
# Deterministic glue facts for the weak-quantity bound

Four independent algebraic facts used to propagate the quadratic-form bounds of the coarse
blocks through the recentring and normalization steps of the weak-quantity bound.

* `qform_blockCongr_le` transports a quadratic-form bound through the congruence
  `Gᵀ A G`, using that the flattened quadratic form of `blockCongr G A` is the form of `A`
  evaluated on `G X`.
* `qform_le_of_loewner` turns a Loewner comparison against a scalar multiple `c E` into a
  scalar multiple of the quadratic-form bound of `E`.
* `qform_add_blockSwap_le` adds the swap block `𝐑` to a bounded block and pays exactly one
  unit of the identity form, by the arithmetic-geometric inequality `2 x · y ≤ x · x + y · y`.
* `volumeAverage_vecDot_optimizerField_eq` identifies the doubled energy of the optimizer
  state with the symmetric part of the coefficient: `ξ · (M ξ) = ξ · (symmPart M) ξ`.

Paper: the response quadratic form `AK.HC (2.15)`.
-/

open Homogenization.HighContrast (blockScale)
namespace Homogenization.HighContrast.Multiscale

noncomputable section

/-- The quadratic form of a scalar dilation of a doubled block:
`X ⬝ (c A) X = c (X ⬝ A X)`. -/
private theorem qform_blockScale {d : ℕ} (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  simp only [blockScale, blockMatVecMul, smul_matVecMul, vecDot_add_right,
    vecDot_smul_right, blockVecDot]
  ring

/-- The quadratic form of a sum of two blocks presented through `ofFullBlockMat` splits into
the sum of the two quadratic forms. -/
private theorem qform_ofFullBlockMat_add {d : ℕ} (A B : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) X) =
      blockVecDot X (blockMatVecMul A X) + blockVecDot X (blockMatVecMul B X) := by
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_ofFullBlockMat, Matrix.add_mulVec, dotProduct_add]

/-- A congruence `Gᵀ A G` transports a quadratic-form bound: if `A` is bounded by `K` and `G`
is bounded by `kG`, then `blockCongr G A` is bounded by `K kG`.  The proof evaluates the
congruence form on `G X` and composes the two bounds.  Paper: `AK.HC (2.15)`. -/
theorem qform_blockCongr_le {d : ℕ} (G A : BlockMat d) (K kG : ℝ) (hK : 0 ≤ K)
    (hA : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul A X) ≤ K * blockVecDot X X)
    (hG : ∀ X : BlockVec d, blockVecDot (blockMatVecMul G X) (blockMatVecMul G X)
        ≤ kG * blockVecDot X X) :
    ∀ X : BlockVec d, blockVecDot X (blockMatVecMul (blockCongr G A) X)
      ≤ (K * kG) * blockVecDot X X := by
  intro X
  rw [blockVecDot_blockCongr]
  calc
    blockVecDot (blockMatVecMul G X) (blockMatVecMul A (blockMatVecMul G X))
        ≤ K * blockVecDot (blockMatVecMul G X) (blockMatVecMul G X) := hA (blockMatVecMul G X)
    _ ≤ K * (kG * blockVecDot X X) :=
          mul_le_mul_of_nonneg_left (hG X) hK
    _ = (K * kG) * blockVecDot X X := by ring

/-- A Loewner comparison `A ≤ c E` combines with a quadratic-form bound `E ≤ kE` on `E` into
the bound `A ≤ c kE` on the identity form.  Paper: `AK.HC (2.15)`. -/
theorem qform_le_of_loewner {d : ℕ} {A E : BlockMat d} {c kE : ℝ} (hc : 0 ≤ c)
    (hA : BlockMatLoewnerLE A (blockScale c E))
    (hE : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul E X) ≤ kE * blockVecDot X X) :
    ∀ X : BlockVec d, blockVecDot X (blockMatVecMul A X) ≤ (c * kE) * blockVecDot X X := by
  intro X
  have hX := hA X
  rw [qform_blockScale] at hX
  calc
    blockVecDot X (blockMatVecMul A X) ≤ c * blockVecDot X (blockMatVecMul E X) := by
          linarith only [hX]
    _ ≤ c * (kE * blockVecDot X X) := mul_le_mul_of_nonneg_left (hE X) hc
    _ = (c * kE) * blockVecDot X X := by ring

/-- Adding the swap block `𝐑` to a quadratically bounded block costs exactly one unit of the
identity form: `X ⬝ (A + 𝐑) X ≤ (K + 1) (X ⬝ X)`.  The swap contributes the off-diagonal
pairing `2 x · y`, which the arithmetic-geometric inequality bounds by `x · x + y · y`.
Paper: `AK.HC (2.15)`. -/
theorem qform_add_blockSwap_le {d : ℕ} {A : BlockMat d} {K : ℝ}
    (hA : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul A X) ≤ K * blockVecDot X X) :
    ∀ X : BlockVec d, blockVecDot X (blockMatVecMul
        (ofFullBlockMat (toFullBlockMat A + toFullBlockMat (blockSwap d))) X)
      ≤ (K + 1) * blockVecDot X X := by
  intro X
  rw [qform_ofFullBlockMat_add]
  have hswap : blockVecDot X (blockMatVecMul (blockSwap d) X) ≤ blockVecDot X X := by
    have hb := abs_vecDot_le_add_halves_vecNormSq X.1 X.2
    have h1 : vecDot X.1 X.2 ≤ vecDot X.1 X.1 / 2 + vecDot X.2 X.2 / 2 := by
      simpa only [vecNormSq] using le_trans (le_abs_self (vecDot X.1 X.2)) hb
    have h2 : vecDot X.2 X.1 ≤ vecDot X.1 X.1 / 2 + vecDot X.2 X.2 / 2 := by
      rw [vecDot_comm]
      simpa only [vecNormSq] using le_trans (le_abs_self (vecDot X.1 X.2)) hb
    simp only [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd]
    linarith only [h1, h2]
  calc
    blockVecDot X (blockMatVecMul A X) + blockVecDot X (blockMatVecMul (blockSwap d) X)
        ≤ K * blockVecDot X X + blockVecDot X X := add_le_add (hA X) hswap
    _ = (K + 1) * blockVecDot X X := by ring

/-- The doubled energy of the optimizer state is the symmetric energy: pointwise,
`ξ · (b x ξ) = ξ · (symmPart (b x) ξ)` because the antisymmetric part contributes nothing to
the quadratic form.  The optimizer field is `(∇v, b ∇v)` and the variation energy integrand
is `∇v · (symmPart b) ∇v`, so the two volume averages agree. -/
theorem volumeAverage_vecDot_optimizerField_eq {d : ℕ} [NeZero d] (V : Set (Vec d))
    (b : CoeffField d) (v : AHarmonicFunction b V) :
    volumeAverage V (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = volumeAverage V (scalarVariationEnergyIntegrand b v) := by
  have _ : NeZero d := ‹NeZero d›
  have h : (fun x => vecDot (optimizerField b v x).1 (optimizerField b v x).2)
      = scalarVariationEnergyIntegrand b v := by
    funext x
    simp only [optimizerField, scalarVariationEnergyIntegrand]
    exact (vecDot_matVecMul_symmPart (b x) (v.toH1.grad x)).symm
  rw [h]

end

end Homogenization.HighContrast.Multiscale
