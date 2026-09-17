import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import HCPoly.Entry.CG.Proofs.AdaptedDomainRecovery
import HCPoly.Entry.Setup.BlockCalculus
import Homogenization.Ambient.BlockMatrix
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Ellipticity

/-!
# The cell-average energy bound

The cell-average half of AK.HC (2.15): the doubled cell average of a `b`-harmonic field on a cell
`V` is controlled by the pathwise symmetric energy of the field, with the constant supplied by the
quadratic form of the coarse block of `b` on `V` augmented by the swap block `𝐑`.  The proof
combines the variational (Fenchel) inequality satisfied by every admissible field with the
canonical response--coarse-block identity on a bounded open convex domain.
-/

open Homogenization.HighContrast.CG

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Fenchel's algebraic core of the cell-average energy bound.  A vector `W` that satisfies the
variational inequality for the quadratic form of `B` is controlled by `E` as soon as `B` is
bounded above by `K` times the identity form.  This is the algebraic step of the cell-average half
of AK.HC (2.15). -/
theorem blockVecDot_self_le_of_forall_dot_le {d : ℕ} (W : BlockVec d) (B : BlockMat d)
    (E K : ℝ) (hK : 0 < K)
    (hB : ∀ X : BlockVec d, blockVecDot X (blockMatVecMul B X) ≤ K * blockVecDot X X)
    (hvar : ∀ X : BlockVec d, blockVecDot X W ≤
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul B X) + (1 / 2 : ℝ) * E) :
    blockVecDot W W ≤ K * E := by
  have hKinv : 0 < K⁻¹ := inv_pos.mpr hK
  have hvar' := hvar (K⁻¹ • W)
  have h1 : blockVecDot (K⁻¹ • W) W = K⁻¹ * blockVecDot W W := by
    rw [blockVecDot_smul_left]
  have h2 : blockVecDot (K⁻¹ • W) (blockMatVecMul B (K⁻¹ • W)) =
      (K⁻¹ * K⁻¹) * blockVecDot W (blockMatVecMul B W) := by
    rw [blockMatVecMul_smul, blockVecDot_smul_right, blockVecDot_smul_left]
    ring
  rw [h1, h2] at hvar'
  have hcoef : 0 ≤ K⁻¹ * K⁻¹ := mul_nonneg (le_of_lt hKinv) (le_of_lt hKinv)
  have hsimp : (K⁻¹ * K⁻¹) * (K * blockVecDot W W) = K⁻¹ * blockVecDot W W := by
    field_simp
  have hP : (K⁻¹ * K⁻¹) * blockVecDot W (blockMatVecMul B W) ≤
      K⁻¹ * blockVecDot W W := by
    have hmono := mul_le_mul_of_nonneg_left (hB W) hcoef
    rwa [hsimp] at hmono
  have hstep : K⁻¹ * blockVecDot W W ≤
      (1 / 2 : ℝ) * (K⁻¹ * blockVecDot W W) + (1 / 2 : ℝ) * E := by
    have hhalf := mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith [hvar']
  have hfin : K⁻¹ * blockVecDot W W ≤ E := by linarith [hstep]
  have hmul := mul_le_mul_of_nonneg_left hfin (le_of_lt hK)
  have hleft : K * (K⁻¹ * blockVecDot W W) = blockVecDot W W := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hK), one_mul]
  rwa [hleft] at hmul

/-- The first slot of the swap block `𝐑` acting on a doubled vector is its second slot. -/
private theorem blockMatVecMul_blockSwap_fst {d : ℕ} (Y : BlockVec d) :
    (blockMatVecMul (blockSwap d) Y).1 = Y.2 := by
  funext i
  simp [blockMatVecMul, blockSwap, Book.Ch02.blockR, matVecMul, Matrix.one_apply]

/-- The second slot of the swap block `𝐑` acting on a doubled vector is its first slot. -/
private theorem blockMatVecMul_blockSwap_snd {d : ℕ} (Y : BlockVec d) :
    (blockMatVecMul (blockSwap d) Y).2 = Y.1 := by
  funext i
  simp [blockMatVecMul, blockSwap, Book.Ch02.blockR, matVecMul, Matrix.one_apply]

/-- The quadratic form of a componentwise sum of doubled blocks is the sum of their quadratic
forms on a common doubled probe. -/
private theorem blockVecDot_blockMatVecMul_ofFullBlockMat_add {d : ℕ} (A B : BlockMat d)
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) X) =
      blockVecDot X (blockMatVecMul A X) + blockVecDot X (blockMatVecMul B X) := by
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul,
    toFullBlockMat_ofFullBlockMat, Matrix.add_mulVec, dotProduct_add]

/-- The volume average of the scalar response integrand of a `b`-harmonic field on a cell is
minus one half of its pathwise symmetric energy, plus the pairing of `(-p, r)` with the
slot-swapped cell average of the optimizer field.  This is the algebraic expansion behind the
cell-average half of AK.HC (2.15). -/
private theorem volumeAverage_scalarResponseIntegrand_eq_blockVecDot {d : ℕ} {V : Set (Vec d)}
    {b : CoeffField d} (hInt : ResponseLinearIntegrabilityData V b)
    (p r : Vec d) (v : AHarmonicFunction b V) :
    volumeAverage V (scalarResponseIntegrand V b p r v) =
      - (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v)
        + blockVecDot (-p, r)
            (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))) := by
  have hE : MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand b v) V := hInt.energy v
  have hF : MeasureTheory.IntegrableOn
      (fun x => vecDot p (matVecMul (b x) (v.toH1.grad x))) V := hInt.flux p v
  have hG : MeasureTheory.IntegrableOn (fun x => vecDot r (v.toH1.grad x)) V := hInt.grad r v
  have hA : MeasureTheory.IntegrableOn
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v)) V :=
    hE.integrable.smul (-(1 / 2 : ℝ))
  have hAB : MeasureTheory.IntegrableOn
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v) -
        fun x => vecDot p (matVecMul (b x) (v.toH1.grad x))) V :=
    hA.integrable.sub hF.integrable
  have hcompF : ∀ i, MeasureTheory.IntegrableOn
      (fun x => matVecMul (b x) (v.toH1.grad x) i) V :=
    fun i => by simpa [vecDot_single_left] using hInt.flux (Pi.single i 1) v
  have hcompG : ∀ i, MeasureTheory.IntegrableOn (fun x => v.toH1.grad x i) V :=
    fun i => by simpa [vecDot_single_left] using hInt.grad (Pi.single i 1) v
  have hdecomp : scalarResponseIntegrand V b p r v =
      (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand b v) -
        (fun x => vecDot p (matVecMul (b x) (v.toH1.grad x)))) +
        (fun x => vecDot r (v.toH1.grad x)) := by
    funext x
    simp only [scalarResponseIntegrand, scalarVariationEnergyIntegrand, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdecomp, volumeAverage_add hAB hG, volumeAverage_sub hA hF, volumeAverage_smul]
  rw [volumeAverage_vecDot_left p (fun x => matVecMul (b x) (v.toH1.grad x)) hcompF,
    volumeAverage_vecDot_left r (fun x => v.toH1.grad x) hcompG]
  have hZ1 : (cellAverage V (optimizerField b v)).1
      = fun i => volumeAverage V (fun x => v.toH1.grad x i) := rfl
  have hZ2 : (cellAverage V (optimizerField b v)).2
      = fun i => volumeAverage V (fun x => matVecMul (b x) (v.toH1.grad x) i) := rfl
  have hs1 : (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))).1
      = (cellAverage V (optimizerField b v)).2 := blockMatVecMul_blockSwap_fst _
  have hs2 : (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))).2
      = (cellAverage V (optimizerField b v)).1 := blockMatVecMul_blockSwap_snd _
  rw [blockVecDot, hs1, hs2, hZ1, hZ2, vecDot_neg_left]
  ring

/-- The variational (Fenchel) inequality for the doubled cell average of a `b`-harmonic field on
a cell `V`: for every doubled probe `X`, the pairing of `X` with the slot-swapped cell average of
the optimizer field is bounded by half the quadratic form of the coarse block of `b` augmented by
the swap block `𝐑`, plus half the pathwise symmetric energy of the field.  This is the
variational step of the cell-average half of AK.HC (2.15), stated with the hypotheses of the
canonical response--coarse-block identity on a bounded open convex domain. -/
theorem forall_blockVecDot_cellAverage_optimizerField_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) :
    ∀ X : BlockVec d,
      blockVecDot X (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))) ≤
        (1 / 2 : ℝ) * blockVecDot X
            (blockMatVecMul
              (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix V b) +
                toFullBlockMat (blockSwap d))) X)
          + (1 / 2 : ℝ) * volumeAverage V (scalarVariationEnergyIntegrand b v) := by
  intro X
  let : IsFiniteMeasure (volumeMeasureOn V) := hConv.isFiniteMeasure_restrict_volume
  have hInt : ResponseLinearIntegrabilityData V b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hscalar : volumeAverage V (scalarResponseIntegrand V b (-X.1) X.2 v) ≤
      ResponseJ V (-X.1) X.2 b :=
    le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn hEll (ne_of_gt hvol)
      (-X.1) X.2 (responseJValueSet_mem V (-X.1) X.2 b v)
  rw [responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain hConv hEll hvol (-X.1) X.2,
    volumeAverage_scalarResponseIntegrand_eq_blockVecDot hInt (-X.1) X.2 v] at hscalar
  have hpair : (-(-X.1), X.2) = X := by
    ext <;> simp
  rw [hpair] at hscalar
  have hneg : - vecDot (-X.1) X.2 =
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (blockSwap d) X) := by
    rw [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd,
      vecDot_neg_left, neg_neg, vecDot_comm X.2 X.1]
    ring
  have hrhs : (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul (coarseBlockMatrix V b) X)
        - vecDot (-X.1) X.2 =
      (1 / 2 : ℝ) * blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix V b) +
            toFullBlockMat (blockSwap d))) X) := by
    rw [sub_eq_add_neg, hneg, ← mul_add, ← blockVecDot_blockMatVecMul_ofFullBlockMat_add]
  rw [hrhs] at hscalar
  linarith

/-- The cell-average energy bound: the squared doubled cell average of a `b`-harmonic field on a
cell `V` is bounded by the pathwise symmetric energy of the field times any positive constant `K`
that bounds above the quadratic form of the coarse block of `b` on `V` augmented by the swap block
`𝐑`.  This is the cell-average half of AK.HC (2.15). -/
theorem blockVecDot_cellAverage_optimizerField_self_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V)
    (K : ℝ) (hK : 0 < K)
    (hB : ∀ X : BlockVec d,
      blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix V b) +
            toFullBlockMat (blockSwap d))) X) ≤ K * blockVecDot X X) :
    blockVecDot (cellAverage V (optimizerField b v)) (cellAverage V (optimizerField b v)) ≤
      K * volumeAverage V (scalarVariationEnergyIntegrand b v) := by
  have hvar := forall_blockVecDot_cellAverage_optimizerField_le hConv hEll hvol v
  have h := blockVecDot_self_le_of_forall_dot_le
    (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v)))
    (ofFullBlockMat (toFullBlockMat (coarseBlockMatrix V b) + toFullBlockMat (blockSwap d)))
    (volumeAverage V (scalarVariationEnergyIntegrand b v)) K hK hB hvar
  have hWW : blockVecDot
        (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v)))
        (blockMatVecMul (blockSwap d) (cellAverage V (optimizerField b v))) =
      blockVecDot (cellAverage V (optimizerField b v)) (cellAverage V (optimizerField b v)) := by
    rw [blockVecDot, blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, blockVecDot]
    ring
  rw [hWW] at h
  exact h

end

end Homogenization.HighContrast.Multiscale
