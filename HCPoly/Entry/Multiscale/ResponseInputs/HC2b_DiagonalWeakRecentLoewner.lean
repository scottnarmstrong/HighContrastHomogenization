import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentDecomp

/-!
# The Loewner / operator-norm layer, on the block-matrix carrier

`L-1 … L-5`, proved here.  Nothing restates or weakens any existing declaration, and the target
`diagonalWeakNorm_primal_le` is untouched.

## Why this module exists

`h6a_quadratic_le_norm_normalizedBlock` below — the quadratic half of the estimate — needs the
Loewner envelope `N ≤ |N| · I_{2d}` of a doubled block by its operator norm.  The proof of that
step in `AdaptedWeakRoute.lean` (`b130_blockSpecBound_attained`) is `private` and strictly
downstream of this module, so it cannot be used here.

This module re-proves the step where it can be used: it imports only
`HC2b_DiagonalWeakRecentDecomp`, and is imported by `HC2b_DiagonalWeakRecentScaleInput`, so it
sits strictly upstream of `AdaptedWeakRoute`.  The original declarations are neither deleted nor
made public.

## Two corrections to the diagnosis

1. The step actually needed is NOT `b130_blockSpecBound_attained`.  That lemma concludes
   `N ≤ blockSpecBound N · I` and is about the `sInf` carrier; what is needed is the bound by
  the OPERATOR NORM, `x · N x ≤ |N| (x · x)`, for an ARBITRARY (in particular not positive
  semidefinite — the averaged defect is a difference of coarse blocks) matrix.  That is `L-1`
  and `L-2` here.
2. `b130_blockSpecBound_attained` is a duplicate: `h5rc_blockSpecBound_attained`
   (`AdaptedSwarm.lean`) is the same statement, and `AdaptedSwarm` is upstream of this
  chain.  It is `private` there too, so it is equally unusable, though its import direction is
  not the obstruction.

The analogous estimate is `diagonalWeak_recent_response_quadratic_le`.  Nothing is imported
from it and no file is copied; the proof is transcribed onto the block-matrix carriers, with its
`blockSize D (blockIdentity d)` replaced by `‖toFullBlockMat ·‖`, which is
what `weakAverageDefect` and `CH-3`'s `henergy` print.
-/

open Homogenization.HighContrast (blockScale matSqrt matSqrt_spec normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## Flat helpers -/

private theorem r22_dotProduct_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) :
    (0 : ℝ) ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private theorem r22_toFullBlockMat_blockIdentity :
    toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
  ext (i | i) (j | j) <;>
    simp [toFullBlockMat, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, Matrix.one_apply]

private theorem r22_qform_flat (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec X) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]

private theorem r22_qform_blockScale (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  rw [r22_qform_flat, r22_qform_flat, full_blockScale, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

private theorem r22_qform_identity (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Book.Ch02.blockIdentity d) X) =
      toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
  rw [r22_qform_flat, r22_toFullBlockMat_blockIdentity, Matrix.one_mulVec]

/-- Congruence by a symmetric matrix moves through the quadratic form. -/
private theorem r22_qform_conj {n : Type*} [Fintype n] [DecidableEq n]
    (Sm M : Matrix n n ℝ) (hS : Smᵀ = Sm) (v : n → ℝ) :
    v ⬝ᵥ ((Sm * M * Sm) *ᵥ v) = (Sm *ᵥ v) ⬝ᵥ (M *ᵥ (Sm *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, hS]

/-! ## L-1 … L-3: the Loewner / operator-norm layer -/

/-- **L-1.**  The quadratic form of an ARBITRARY square real matrix is bounded by its L2
operator norm: `v · N v ≤ |N| (v · v)`.  No positive semidefiniteness — the averaged response
defect is a difference of coarse blocks and carries no sign
(`p.response.transfer`).  The proof expands the nonnegative square `|‖N‖ v - N v|²`. -/
theorem h6a_dot_mulVec_le_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (v : n → ℝ) : v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ * (v ⬝ᵥ v) := by
  have hsq := vecSq_mulVec_le N v
  have hvv : (0 : ℝ) ≤ v ⬝ᵥ v := r22_dotProduct_self_nonneg v
  rcases eq_or_lt_of_le (norm_nonneg N) with h0 | hpos
  · have hN : N = 0 := norm_eq_zero.mp h0.symm
    subst hN
    simp
  · have hexp : (0 : ℝ) ≤ (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) :=
      r22_dotProduct_self_nonneg _
    have hexpand : (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) =
        ‖N‖ * ‖N‖ * (v ⬝ᵥ v) - 2 * ‖N‖ * (v ⬝ᵥ (N *ᵥ v)) + (N *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm (N *ᵥ v) v]
      ring
    rw [hexpand] at hexp
    nlinarith [hexp, hsq, hpos]

/-- **L-2.**  The Loewner envelope of an arbitrary doubled block by its operator norm,
`N ≤ |N| · I_{2d}`.  It is proved here with no hypothesis on `N` at all. -/
theorem h6a_loewner_le_opNorm_identity (N : BlockMat d) :
    BlockMatLoewnerLE N
      (blockScale ‖toFullBlockMat N‖ (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := h6a_dot_mulVec_le_opNorm (toFullBlockMat N) (toFullBlockVec X)
  rw [r22_qform_flat, r22_qform_blockScale, r22_qform_identity]
  linarith only [h]

/-- **L-3.**  `blockSpecBound N` attains its defining infimum, UNCONDITIONALLY: the set
`{c ≥ 0 | N ≤ c I}` is never empty, because `L-2` puts `‖toFullBlockMat N‖` in it.  This re-proves
`b130_blockSpecBound_attained` (`AdaptedWeakRoute.lean`) and
`h5rc_blockSpecBound_attained` (`AdaptedSwarm.lean`), both `private`, and drops their
`(c : ℝ) (hc : 0 ≤ c) (h : BlockMatLoewnerLE N (blockScale c (blockIdentity d)))` witness
hypotheses, so it is strictly stronger than either. -/
theorem h6a_blockSpecBound_attained (N : BlockMat d) :
    BlockMatLoewnerLE N (blockScale (blockSpecBound N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have hid := r22_qform_identity X
  set q : ℝ := toFullBlockVec X ⬝ᵥ toFullBlockVec X with hqdef
  have hq0 : (0 : ℝ) ≤ q := r22_dotProduct_self_nonneg _
  set p : ℝ := blockVecDot X (blockMatVecMul N X) with hpdef
  have hmem : ∀ b ∈ {c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}, p ≤ b * q := by
    intro b hb
    have hbX := hb.2 X
    rw [r22_qform_blockScale, hid] at hbX
    linarith
  have hne : ({c : ℝ | 0 ≤ c ∧
      BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))}).Nonempty :=
    ⟨‖toFullBlockMat N‖, norm_nonneg _, h6a_loewner_le_opNorm_identity N⟩
  have hkey : p ≤ blockSpecBound N * q := by
    rcases eq_or_lt_of_le hq0 with h0 | hpos
    · obtain ⟨c, hc⟩ := hne
      have hc0 := hmem c hc
      rw [← h0] at hc0 ⊢
      simpa using hc0
    · have hdiv : p / q ≤ blockSpecBound N := by
        refine le_csInf hne fun b hb => ?_
        exact (div_le_iff₀ hpos).2 (hmem b hb)
      exact (div_le_iff₀ hpos).1 hdiv
  rw [r22_qform_blockScale, hid]
  linarith

/-- **L-4.**  The quadratic form of a block whose flat representative is positive semidefinite
is nonnegative.  Used to discharge `CH-3`'s `hLsq` side condition from its `hE`. -/
theorem h6a_blockVecDot_nonneg_of_posSemidef (A : BlockMat d)
    (hA : (toFullBlockMat A).PosSemidef) (X : BlockVec d) :
    0 ≤ blockVecDot X (blockMatVecMul A X) := by
  have h := hA.dotProduct_mulVec_nonneg (toFullBlockVec X)
  rw [r22_qform_flat]
  simpa only [star_trivial] using h

/-! ## The quadratic half -/

/-- **The quadratic half.**  The unnormalized quadratic form of `H` is controlled
by the operator norm of the `E`-NORMALIZED block times the `E`-quadratic form:

`x · H x ≤ |E^{-1/2} H E^{-1/2}| (x · E x)`.

The same estimate is `diagonalWeak_recent_response_quadratic_le`, whose proof is the same
three moves — congruence of the normalized block by `E^{1/2}` back to `H`, the change of variable
`y = E^{1/2} x`, and the Loewner envelope of the normalized block.  Two differences, both
STRENGTHENINGS:

* the carrier `blockSize D (blockIdentity d)` is replaced by
  `‖toFullBlockMat D‖`, which is what `weakAverageDefect` and `CH-3`'s `henergy` print; and
* the earlier statement assumes `IsSymmetricBlockMat E`/`H`; here NEITHER symmetry of `H` nor a
  separate symmetry hypothesis on `E` is needed, because `L-1` holds for arbitrary matrices and
  `(toFullBlockMat E).PosDef` already carries the symmetry of `E`. -/
theorem h6a_quadratic_le_norm_normalizedBlock (E H : BlockMat d)
    (hE : (toFullBlockMat E).PosDef) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul H X)
      ≤ ‖toFullBlockMat (normalizedBlock H E)‖ * blockVecDot X (blockMatVecMul E X) := by
  -- the two square-root cancellations, and the symmetry of the root
  have hSSI : matSqrt (toFullBlockMat E) * matSqrt (toFullBlockMat E)⁻¹ = 1 :=
    Annealed.matSqrt_mul_matSqrt_inv_full hE
  have hSIS : matSqrt (toFullBlockMat E)⁻¹ * matSqrt (toFullBlockMat E) = 1 :=
    Annealed.matSqrt_inv_mul_matSqrt_full hE
  have hSsymm : (matSqrt (toFullBlockMat E))ᵀ = matSqrt (toFullBlockMat E) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hE.posSemidef).1.isHermitian
  have hSS : matSqrt (toFullBlockMat E) * matSqrt (toFullBlockMat E) = toFullBlockMat E :=
    (matSqrt_spec hE.posSemidef).2
  -- the flat representative of the normalized block
  have hN : toFullBlockMat (normalizedBlock H E)
      = matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat H * matSqrt (toFullBlockMat E)⁻¹ := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  -- un-normalization: `E^{1/2} (E^{-1/2} H E^{-1/2}) E^{1/2} = H`
  have hfactor : matSqrt (toFullBlockMat E) * toFullBlockMat (normalizedBlock H E) *
      matSqrt (toFullBlockMat E) = toFullBlockMat H := by
    rw [hN]
    calc
      matSqrt (toFullBlockMat E) *
            (matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat H * matSqrt (toFullBlockMat E)⁻¹) *
            matSqrt (toFullBlockMat E)
          = matSqrt (toFullBlockMat E) * matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat H *
            (matSqrt (toFullBlockMat E)⁻¹ * matSqrt (toFullBlockMat E)) := by noncomm_ring
      _ = toFullBlockMat H := by rw [hSSI, hSIS, Matrix.one_mul, Matrix.mul_one]
  -- the change of variable `y = E^{1/2} x`
  have hquad : blockVecDot X (blockMatVecMul H X)
      = (matSqrt (toFullBlockMat E) *ᵥ toFullBlockVec X) ⬝ᵥ
          (toFullBlockMat (normalizedBlock H E) *ᵥ
            (matSqrt (toFullBlockMat E) *ᵥ toFullBlockVec X)) := by
    rw [r22_qform_flat, ← hfactor, r22_qform_conj _ _ hSsymm]
  have hy : (matSqrt (toFullBlockMat E) *ᵥ toFullBlockVec X) ⬝ᵥ
      (matSqrt (toFullBlockMat E) *ᵥ toFullBlockVec X)
      = blockVecDot X (blockMatVecMul E X) := by
    have h := r22_qform_conj (matSqrt (toFullBlockMat E)) (1 : FullBlockMat d) hSsymm
      (toFullBlockVec X)
    rw [Matrix.mul_one, hSS, Matrix.one_mulVec] at h
    rw [← h, r22_qform_flat]
  rw [hquad, ← hy]
  exact h6a_dot_mulVec_le_opNorm _ _

end

end Homogenization.HighContrast.Multiscale
