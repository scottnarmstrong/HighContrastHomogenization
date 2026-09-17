import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCellEnergyBound

/-!
# The direct full-dual pairing of a cell average against a state

The direct Fenchel pairing of AK.HC, Lemma A.1, display (A.4): the cell average of the doubled
optimizer field, paired across its two slots with a state `Y = (P, Q)`, is controlled by the square
root of the cell's own coarse-block energy of `Y` — read through the two diagonal blocks of the
coarse block, `b` in the gradient slot and `S_*^{-1}` in the flux slot, exactly the two blocks from
which the source load `L_s^{±}` is built — times the square root of the pathwise symmetric energy of
the field.  The pairing is `Y.2` against the cell-average gradient plus `Y.1` against the
cell-average flux, the full-dual form consumed by the cutoff-mean rows.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

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

/-- The quadratic form of a doubled block with a vanishing first slot: only the lower-right
block acts, on the second slot. -/
private theorem blockVecDot_fstZero_blockMatVecMul {d : ℕ} (C : BlockMat d) (y : Vec d) :
    blockVecDot (0, y) (blockMatVecMul C (0, y)) =
      vecDot y (matVecMul C.lowerRight y) := by
  change vecDot 0 (matVecMul C.upperLeft 0 + matVecMul C.upperRight y) +
      vecDot y (matVecMul C.lowerLeft 0 + matVecMul C.lowerRight y) =
    vecDot y (matVecMul C.lowerRight y)
  simp only [matVecMul_zero, zero_add, vecDot_zero_left]

/-- The quadratic form of a doubled block with a vanishing second slot: only the upper-left
block acts, on the first slot. -/
private theorem blockVecDot_sndZero_blockMatVecMul {d : ℕ} (C : BlockMat d) (y : Vec d) :
    blockVecDot (y, 0) (blockMatVecMul C (y, 0)) =
      vecDot y (matVecMul C.upperLeft y) := by
  change vecDot y (matVecMul C.upperLeft y + matVecMul C.upperRight 0) +
      vecDot 0 (matVecMul C.lowerLeft y + matVecMul C.lowerRight 0) =
    vecDot y (matVecMul C.upperLeft y)
  simp only [matVecMul_zero, add_zero, vecDot_zero_left]

/-- Pairing a doubled vector whose first slot is zero with the slot-swapped image of `Z` leaves
only the first slot of `Z`, tested against the second slot of the probe. -/
private theorem blockVecDot_fstZero_blockSwap {d : ℕ} (y : Vec d) (Z : BlockVec d) :
    blockVecDot (0, y) (blockMatVecMul (blockSwap d) Z) = vecDot y Z.1 := by
  change vecDot 0 (blockMatVecMul (blockSwap d) Z).1 +
      vecDot y (blockMatVecMul (blockSwap d) Z).2 = vecDot y Z.1
  rw [blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, vecDot_zero_left, zero_add]

/-- Pairing a doubled vector whose second slot is zero with the slot-swapped image of `Z` leaves
only the second slot of `Z`, tested against the first slot of the probe. -/
private theorem blockVecDot_sndZero_blockSwap {d : ℕ} (y : Vec d) (Z : BlockVec d) :
    blockVecDot (y, 0) (blockMatVecMul (blockSwap d) Z) = vecDot y Z.2 := by
  change vecDot y (blockMatVecMul (blockSwap d) Z).1 +
      vecDot 0 (blockMatVecMul (blockSwap d) Z).2 = vecDot y Z.2
  rw [blockMatVecMul_blockSwap_fst, blockMatVecMul_blockSwap_snd, vecDot_zero_left, add_zero]

/-- The swap block contributes nothing to the quadratic form of a doubled vector whose first
slot vanishes. -/
private theorem blockVecDot_fstZero_blockSwap_self {d : ℕ} (y : Vec d) :
    blockVecDot (0, y) (blockMatVecMul (blockSwap d) (0, y)) = 0 := by
  have h : ((0 : Vec d), y).1 = 0 := rfl
  rw [blockVecDot_fstZero_blockSwap, h, vecDot_zero_right]

/-- The swap block contributes nothing to the quadratic form of a doubled vector whose second
slot vanishes. -/
private theorem blockVecDot_sndZero_blockSwap_self {d : ℕ} (y : Vec d) :
    blockVecDot (y, 0) (blockMatVecMul (blockSwap d) (y, 0)) = 0 := by
  have h : (y, (0 : Vec d)).2 = 0 := rfl
  rw [blockVecDot_sndZero_blockSwap, h, vecDot_zero_right]

/-- The quadratic form of a scalar dilation of a matrix: `(c x) · A (c x) = c^2 (x · A x)`. -/
private theorem vecDot_smul_matVecMul_smul {d : ℕ} (c : ℝ) (A : Mat d) (x : Vec d) :
    vecDot (c • x) (matVecMul A (c • x)) = c ^ 2 * vecDot x (matVecMul A x) := by
  rw [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  ring

/-- The quadratic form of the coarse block augmented by the swap block, with the probe's first
slot vanishing, is the lower-right block form of the coarse block on the second slot. -/
private theorem qform_fstZero_add_swap {d : ℕ} (C : BlockMat d) (y : Vec d) :
    blockVecDot (0, y)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat C + toFullBlockMat (blockSwap d)))
          (0, y)) =
      vecDot y (matVecMul C.lowerRight y) := by
  rw [blockVecDot_blockMatVecMul_ofFullBlockMat_add, blockVecDot_fstZero_blockMatVecMul,
    blockVecDot_fstZero_blockSwap_self, add_zero]

/-- The quadratic form of the coarse block augmented by the swap block, with the probe's second
slot vanishing, is the upper-left block form of the coarse block on the first slot. -/
private theorem qform_sndZero_add_swap {d : ℕ} (C : BlockMat d) (y : Vec d) :
    blockVecDot (y, 0)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat C + toFullBlockMat (blockSwap d)))
          (y, 0)) =
      vecDot y (matVecMul C.upperLeft y) := by
  rw [blockVecDot_blockMatVecMul_ofFullBlockMat_add, blockVecDot_sndZero_blockMatVecMul,
    blockVecDot_sndZero_blockSwap_self, add_zero]

/-- Scaled form of `qform_fstZero_add_swap`. -/
private theorem qform_fstZero_add_swap_smul {d : ℕ} (C : BlockMat d) (c : ℝ) (y : Vec d) :
    blockVecDot (0, c • y)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat C + toFullBlockMat (blockSwap d)))
          (0, c • y)) =
      c ^ 2 * vecDot y (matVecMul C.lowerRight y) := by
  rw [qform_fstZero_add_swap, vecDot_smul_matVecMul_smul]

/-- Scaled form of `qform_sndZero_add_swap`. -/
private theorem qform_sndZero_add_swap_smul {d : ℕ} (C : BlockMat d) (c : ℝ) (y : Vec d) :
    blockVecDot (c • y, 0)
        (blockMatVecMul (ofFullBlockMat (toFullBlockMat C + toFullBlockMat (blockSwap d)))
          (c • y, 0)) =
      c ^ 2 * vecDot y (matVecMul C.upperLeft y) := by
  rw [qform_sndZero_add_swap, vecDot_smul_matVecMul_smul]

/-- Algebraic core of the full-dual pairing AK.HC (A.4): a real number `X` satisfying the Fenchel
inequality `lam * X ≤ lam^2 A / 2 + E / 2` for every real `lam`, with `A ≥ 0`, obeys
`X^2 ≤ A E`. -/
theorem sq_le_mul_of_forall_quadratic_le {X A E : ℝ} (hA : 0 ≤ A)
    (h : ∀ lam : ℝ, lam * X ≤ (lam ^ 2 / 2) * A + E / 2) :
    X ^ 2 ≤ A * E := by
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have hX : X = 0 := by
      by_contra hXne
      have h1 := h ((E / 2 + 1) / X)
      have h2 : ((E / 2 + 1) / X) * X = E / 2 + 1 :=
        div_mul_cancel₀ (E / 2 + 1) hXne
      rw [h2] at h1
      rw [← hA0] at h1
      linarith
    rw [hX, ← hA0]
    norm_num
  · have h1 := h (X / A)
    have hAne : A ≠ 0 := ne_of_gt hApos
    have h2A : (0 : ℝ) ≤ 2 * A := by positivity
    have hmul := mul_le_mul_of_nonneg_left h1 h2A
    have hL : (2 * A) * ((X / A) * X) = 2 * X ^ 2 := by
      field_simp
    have hR : (2 * A) * (((X / A) ^ 2 / 2) * A + E / 2) = X ^ 2 + A * E := by
      field_simp
    rw [hL, hR] at hmul
    linarith

/-- Square-root form of `sq_le_mul_of_forall_quadratic_le`: the same Fenchel hypothesis yields
`|X| ≤ sqrt A * sqrt E`. -/
theorem abs_le_sqrt_mul_sqrt_of_forall_quadratic_le {X A E : ℝ} (hA : 0 ≤ A)
    (h : ∀ lam : ℝ, lam * X ≤ (lam ^ 2 / 2) * A + E / 2) :
    |X| ≤ Real.sqrt A * Real.sqrt E := by
  have h1 : X ^ 2 ≤ A * E := sq_le_mul_of_forall_quadratic_le hA h
  calc
    |X| = Real.sqrt (X ^ 2) := (Real.sqrt_sq_eq_abs X).symm
    _ ≤ Real.sqrt (A * E) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt A * Real.sqrt E := Real.sqrt_mul hA E

/-- Gradient half of the direct full-dual pairing AK.HC (A.4): the cell average of the gradient of
a `b`-harmonic field, tested against `r`, is bounded by the square root of the lower-right coarse
block form of `r` times the square root of the pathwise symmetric energy of the field. -/
theorem abs_vecDot_cellAverage_grad_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (r : Vec d)
    (hA : 0 ≤ vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r)) :
    |vecDot r (cellAverage V (optimizerField b v)).1|
      ≤ Real.sqrt (vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r))
        * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := by
  have hvar := forall_blockVecDot_cellAverage_optimizerField_le hConv hEll hvol v
  have hquad : ∀ t : ℝ,
      t * vecDot r (cellAverage V (optimizerField b v)).1 ≤
        (t ^ 2 / 2) * vecDot r (matVecMul (coarseBlockMatrix V b).lowerRight r)
          + volumeAverage V (scalarVariationEnergyIntegrand b v) / 2 := by
    intro t
    have h := hvar (0, t • r)
    rw [blockVecDot_fstZero_blockSwap, vecDot_smul_left, qform_fstZero_add_swap_smul] at h
    linarith
  exact abs_le_sqrt_mul_sqrt_of_forall_quadratic_le hA hquad

/-- Flux half of the direct full-dual pairing AK.HC (A.4): the cell average of the flux of a
`b`-harmonic field, tested against `p`, is bounded by the square root of the upper-left coarse
block form of `p` times the square root of the pathwise symmetric energy of the field. -/
theorem abs_vecDot_cellAverage_flux_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (p : Vec d)
    (hA : 0 ≤ vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p)) :
    |vecDot p (cellAverage V (optimizerField b v)).2|
      ≤ Real.sqrt (vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p))
        * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := by
  have hvar := forall_blockVecDot_cellAverage_optimizerField_le hConv hEll hvol v
  have hquad : ∀ t : ℝ,
      t * vecDot p (cellAverage V (optimizerField b v)).2 ≤
        (t ^ 2 / 2) * vecDot p (matVecMul (coarseBlockMatrix V b).upperLeft p)
          + volumeAverage V (scalarVariationEnergyIntegrand b v) / 2 := by
    intro t
    have h := hvar (t • p, 0)
    rw [blockVecDot_sndZero_blockSwap, vecDot_smul_left, qform_sndZero_add_swap_smul] at h
    linarith
  exact abs_le_sqrt_mul_sqrt_of_forall_quadratic_le hA hquad

/-- The direct full-dual pairing AK.HC (A.4): the cell average of the doubled optimizer field,
paired across the two slots with a state `Y = (P, Q)`, is bounded by the sum of the square roots
of the two diagonal coarse-block forms of `Y` times the square root of the pathwise symmetric
energy of the field. -/
theorem abs_dualPairing_cellAverage_le {d : ℕ} [NeZero d]
    {V : Set (Vec d)} {lam Lam : ℝ} {b : CoeffField d}
    (hConv : IsOpenBoundedConvexDomain V) (hEll : IsEllipticFieldOn lam Lam V b)
    (hvol : 0 < (volume V).toReal) (v : AHarmonicFunction b V) (Y : BlockVec d)
    (hA1 : 0 ≤ vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
    (hA2 : 0 ≤ vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)) :
    |vecDot Y.2 (cellAverage V (optimizerField b v)).1
        + vecDot Y.1 (cellAverage V (optimizerField b v)).2|
      ≤ (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
        * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := by
  have hgrad := abs_vecDot_cellAverage_grad_le hConv hEll hvol v Y.2 hA2
  have hflux := abs_vecDot_cellAverage_flux_le hConv hEll hvol v Y.1 hA1
  calc
    |vecDot Y.2 (cellAverage V (optimizerField b v)).1
        + vecDot Y.1 (cellAverage V (optimizerField b v)).2|
        ≤ |vecDot Y.2 (cellAverage V (optimizerField b v)).1|
            + |vecDot Y.1 (cellAverage V (optimizerField b v)).2| := abs_add_le _ _
    _ ≤ Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2))
            * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v))
          + Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
            * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) :=
        add_le_add hgrad hflux
    _ = (Real.sqrt (vecDot Y.1 (matVecMul (coarseBlockMatrix V b).upperLeft Y.1))
          + Real.sqrt (vecDot Y.2 (matVecMul (coarseBlockMatrix V b).lowerRight Y.2)))
        * Real.sqrt (volumeAverage V (scalarVariationEnergyIntegrand b v)) := by ring

end

end Homogenization.HighContrast.Multiscale
