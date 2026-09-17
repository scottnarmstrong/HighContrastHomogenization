import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentSharpOrder

/-!
# The response field of a recentred difference, and its size

`diagonalWeakNorm_primal_le` (`HC2b_DiagonalWeakRecent.lean`) is untouched: nothing here
restates, weakens or deletes any existing declaration.

## What this module supplies

The metric size of a doubled cell average is reduced to the cell energy
(`HC2b_DiagonalWeakRecentSharpOrder.lean`), given a doubled RESPONSE FIELD `Y` and two size
inequalities.  That reduction leaves open exactly two inputs:

1. the `Y` CONSTRUCTION for the recentred DIFFERENCE field, `isDoubledResponseField_grad_sub`;
  and
2. the RESPONSE-SIZE step, the `hsize` bound of `diagonalWeak_recent_average_bound`, fed by
   `sqrt_blockSize_adaptedResponse_le_of_maximum_finite`.

Both `isDoubledResponseField_grad_sub` and `exists_restrict_solution_adaptedCellAtCenter` are supplied
here.

## The size inputs are Loewner bounds

`blockSize`, `adaptedResponse`, `metricBlockNormSq`, `relSize` and `blockSharp` are not defined
on this tree.  The block-size inequality `blockSize A E ≤ B²` is written here as the LOEWNER
inequality `toFullBlockMat A ≤ B² • toFullBlockMat E`, which is the shape the size input `hAE`
actually takes, and `blockExcess A E` is written as the block spectral bound
`blockSpecBound (blockSub (normalizedBlock A E) (blockIdentity d))` — the quantity
`respAllScaleMax` (`AdaptedDefs.lean`) is already built from.  That substitution removes the
`blockSize_le_one_add_blockExcess` step altogether, and with it the
`blockSpecBound`-subadditivity obstruction recorded in
`HC2b_DiagonalWeakRecentAvSum.lean`: the recentring bound `N ≤ (1 + β) I` is read
straight off `h6a_blockSpecBound_attained` (`HC2b_DiagonalWeakRecentLoewner.lean`), with no
operator norm anywhere.

**This module introduces exactly ONE definition, `adaptedDomainAt`, and it selects no
constant**: it is the per-`w` Chapter-2 domain whose carrier is `adaptedCellAtCenter q (t-n) w`, and
its two structure obligations are discharged inside the definition itself from
`isOpenBoundedConvexDomain_adaptedCellAtCenter` (`HC2b_DiagonalWeakRecentSupport.lean`) and
`volume_adaptedCellAtCenter_toReal_pos` (`…:293`).  Its satisfiability is nevertheless exhibited as an
explicit `∃` before any consumer statement.  Every other declaration below is a `theorem`.

## The `cellAverage`/`averageVec` bridge is definitional

`cellAverage V X` (`AdaptedDefs.lean`) and the pair
`(Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux)` are the same term:
`volumeAverage` (CG `CoarseGraining/Definitions.lean`) and `Book.Ch02.average`
(CG `Book/Ch02/Response.lean`) have identical bodies.  Two `rfl` lemmas record this, so the
response-size step costs two lines, not a lemma.
-/

open Homogenization.HighContrast (CoeffSpace blockScale blockSub coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix matSqrt matSqrt_spec normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open Homogenization.Book.Ch02 MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The doubled response field of a difference of solutions

The `Y` construction for the recentred difference field, transcribed onto `CoarseGraining`'s
carriers. -/

/-- The weak flux of a solution pairs integrably with every test gradient, on a domain
carrying a pointwise elliptic representative, as in `weakFluxIntegrable_of_isEllipticFieldOn`. -/
theorem h6a_weakFluxIntegrable_of_isEllipticFieldOn {U : Domain d} {lam Lam : ℝ} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Book.Ch02.Solution U a) :
    weakFluxIntegrable (U : Set (Vec d)) a.toCoeffField u := fun φ =>
  integrableOn_vecDot_of_memVectorL2
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2)
    φ.toH1Function.grad_memVectorL2

/-- The difference of two solutions on one domain is again a solution: the gradient
difference is `a`-harmonic.  This is `exists_solution_grad_sub`, through
`AHarmonicFunction.addSMulOfIntegrable` (CG `PDE/Harmonic.lean`) at `c = -1`. -/
theorem h6a_exists_solution_grad_sub {U : Domain d} {lam Lam : ℝ} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    (u v : Book.Ch02.Solution U a) :
    ∃ z : Book.Ch02.Solution U a,
      z.toH1.grad = fun x => u.toH1.grad x - v.toH1.grad x := by
  refine ⟨AHarmonicFunction.addSMulOfIntegrable u v
    (h6a_weakFluxIntegrable_of_isEllipticFieldOn hEll u)
    (h6a_weakFluxIntegrable_of_isEllipticFieldOn hEll v) (-1), ?_⟩
  rw [AHarmonicFunction.grad_addSMulOfIntegrable]
  funext x
  show u.toH1.grad x + (-1 : ℝ) • v.toH1.grad x = u.toH1.grad x - v.toH1.grad x
  rw [neg_one_smul, sub_eq_add_neg]

/-- The doubled state `X = (∇v, a∇v)` of a solution lies in the response space
`S(U;a)`: take the adjoint solution to be zero.  This is `isDoubledResponseField_gradFlux`,
through `doubledFieldOfSolutions_mem_responseField_of_isEllipticFieldOn`
(CG `Internal/Ch02/DoubledResponse/ResponseSpace.lean`) and `Book.Ch02.zeroSolution`
(CG `Book/Ch02/Setup.lean`). -/
theorem h6a_isDoubledResponseField_gradFlux {U : Domain d} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (v : Book.Ch02.Solution U a) :
    Book.Ch02.IsDoubledResponseField U a
      { potential := v.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x) } := by
  have h := Internal.Ch02.BookCh02.doubledFieldOfSolutions_mem_responseField_of_isEllipticFieldOn
    U a hEll v (Book.Ch02.zeroSolution U a.transpose)
  have hfield : Book.Ch02.doubledFieldOfSolutions a v (Book.Ch02.zeroSolution U a.transpose) =
      { potential := v.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (v.toH1.grad x) } := by
    unfold Book.Ch02.doubledFieldOfSolutions
    have hzero : (Book.Ch02.zeroSolution U a.transpose).toH1.grad = 0 := rfl
    rw [hzero]
    congr 1
    · funext x
      show v.toH1.grad x + (0 : Vec d → Vec d) x = v.toH1.grad x
      simp
    · funext x
      show matVecMul (a.toCoeffField x) (v.toH1.grad x) -
          matVecMul (a.transpose.toCoeffField x) ((0 : Vec d → Vec d) x) =
        matVecMul (a.toCoeffField x) (v.toH1.grad x)
      rw [show ((0 : Vec d → Vec d) x) = (0 : Vec d) from rfl, matVecMul_zero, sub_zero]
  rwa [hfield] at h

/-- **THE `Y` CONSTRUCTION.**  The doubled DIFFERENCE of two optimizer states lies in the
response space of the cell.  At `p.response.transfer` the cell-average argument splits the
recent-cell difference through the mean of that cell's optimizer and then applies the
gradient-solenoidal variational bound "to the difference of the two optimizer fields", a step
that presupposes exactly the membership proved here. -/
theorem h6a_isDoubledResponseField_grad_sub {U : Domain d} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u v : Book.Ch02.Solution U a) :
    Book.Ch02.IsDoubledResponseField U a
      { potential := fun x => u.toH1.grad x - v.toH1.grad x
        flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) -
          matVecMul (a.toCoeffField x) (v.toH1.grad x) } := by
  obtain ⟨z, hz⟩ := h6a_exists_solution_grad_sub hEll u v
  have h := h6a_isDoubledResponseField_gradFlux hEll z
  have hfield :
      ({ potential := z.toH1.grad
         flux := fun x => matVecMul (a.toCoeffField x) (z.toH1.grad x) } : DoubledField d) =
        { potential := fun x => u.toH1.grad x - v.toH1.grad x
          flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) -
            matVecMul (a.toCoeffField x) (v.toH1.grad x) } := by
    rw [hz]
    congr 1
    funext x
    show matVecMul (a.toCoeffField x) (u.toH1.grad x - v.toH1.grad x) =
      matVecMul (a.toCoeffField x) (u.toH1.grad x) -
        matVecMul (a.toCoeffField x) (v.toH1.grad x)
    rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, sub_eq_add_neg]
  rwa [hfield] at h

/-! ## The carrier bridge is definitional -/

/-! ## The recentred-difference energy map on this tree's carriers -/

/-- **The recentred-difference energy map.**  The `R`-metric size of the cell average of the
doubled difference of two optimizers is controlled by the cell energy of that difference, with
constant `k · e` given the two size inputs.

Three deliberate strengthenings:

* the domain is an ARBITRARY `U : Domain d`, not `adaptedDomainAt hq k w`, so the statement
  carries no geometry at all (the child cell can be supplied when a consumer wants it);
* `diagonalWeakMetricFactor m E ^ 2 * blockSize (adaptedResponse q k w a) E` is replaced by the
  two Loewner inputs `hEM`, `hAE` with arbitrary positive `k`, `e` — a BOUND on the size, not the
  size, which is the shape a consumer owns;
* the `Solution.ofAEEq`/`exists_pointwise_coeffOn_family_aeeq` preamble is NOT reproduced: it
  moves the sample `a` to an elliptic representative `c`, and this tree already carries that move
  separately (`cellAverage_optimizerField_respCoeffMinus_eq_at`,
  `HC2b_DiagonalWeakRecentSupport.lean`).  The statement below is at the representative, so
  the two moves compose without duplication. -/
theorem h6a_recent_difference_metric_le {U : Domain d} {a : CoeffOn U}
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u v : Book.Ch02.Solution U a)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) {k e : ℝ} (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat E ≤ k • toFullBlockMat (respM0 F))
    (hAE : toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) ≤ e • toFullBlockMat E) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (U : Set (Vec d)) (fun x =>
            optimizerField a.toCoeffField u x - optimizerField a.toCoeffField v x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (U : Set (Vec d)) (fun x =>
            optimizerField a.toCoeffField u x - optimizerField a.toCoeffField v x)))
      ≤ (k * e) *
        Book.Ch02.average U (fun x =>
          blockVecDot
            (optimizerField a.toCoeffField u x - optimizerField a.toCoeffField v x)
            (blockMatVecMul (Book.Ch02.blockMatrixField a x)
              (optimizerField a.toCoeffField u x - optimizerField a.toCoeffField v x))) :=
  h6a_energy_map_respM0_le_coarseStarred a hEll
    (h6a_isDoubledResponseField_grad_sub hEll u v) hm hE hk he hEM hAE

/-! ## The RESPONSE-SIZE step

The bound `blockSize (adaptedResponse q k w a) E ≤ B²`,
written as the Loewner inequality that the size input `hAE` actually takes. -/

private theorem r2a_toFullBlockMat_blockIdentity :
    toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
  ext (i | i) (j | j) <;>
    simp [toFullBlockMat, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, Matrix.one_apply]

private theorem r2a_toFullBlockMat_blockScale_identity (c : ℝ) :
    toFullBlockMat (blockScale c (Book.Ch02.blockIdentity d)) =
      c • (1 : FullBlockMat d) := by
  rw [full_blockScale, r2a_toFullBlockMat_blockIdentity]

private theorem r2a_toFullBlockMat_blockCongr (G A : BlockMat d) :
    toFullBlockMat (blockCongr G A) =
      (toFullBlockMat G)ᵀ * toFullBlockMat A * toFullBlockMat G := by
  rw [blockCongr, toFullBlockMat_ofFullBlockMat]

private theorem r2a_normalizedBlock_flat (P Q : BlockMat d) :
    toFullBlockMat (normalizedBlock P Q) =
      matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P * matSqrt (toFullBlockMat Q)⁻¹ := by
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]

private theorem r2a_qform_flat (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul A X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat A *ᵥ toFullBlockVec X) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]

private theorem r2a_qform_blockScale (c : ℝ) (A : BlockMat d) (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (blockScale c A) X) =
      c * blockVecDot X (blockMatVecMul A X) := by
  rw [r2a_qform_flat, r2a_qform_flat, full_blockScale, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

private theorem r2a_qform_identity (X : BlockVec d) :
    blockVecDot X (blockMatVecMul (Book.Ch02.blockIdentity d) X) =
      toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
  rw [r2a_qform_flat, r2a_toFullBlockMat_blockIdentity, Matrix.one_mulVec]

private theorem r2a_blockVecDot_sub_right (X Y Z : BlockVec d) :
    blockVecDot X (Y - Z) = blockVecDot X Y - blockVecDot X Z := by
  simp only [blockVecDot, vecDot, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]
  ring

private theorem r2a_smul_one_mono {c c' : ℝ} (h : c ≤ c') :
    (c • (1 : FullBlockMat d)) ≤ (c' • (1 : FullBlockMat d)) := by
  rw [Matrix.le_iff]
  have hsub : c' • (1 : FullBlockMat d) - c • (1 : FullBlockMat d) =
      (c' - c) • (1 : FullBlockMat d) := by rw [sub_smul]
  rw [hsub]
  exact (Matrix.PosSemidef.one).smul (by linarith only [h])

/-- `blockSpecBound` is nonnegative, UNCONDITIONALLY: its defining set is nonempty by
`h6a_loewner_le_opNorm_identity` (`HC2b_DiagonalWeakRecentLoewner.lean`) and every member is
`≥ 0` by construction.  This mirrors the `private` `blockSpecBound_nonneg'`
(`HC2b_DiagonalWeakRecentSupport.lean`), which is not reachable from here. -/
theorem h6a_blockSpecBound_nonneg (N : BlockMat d) : 0 ≤ blockSpecBound N :=
  le_csInf ⟨‖toFullBlockMat N‖, norm_nonneg _, h6a_loewner_le_opNorm_identity N⟩
    fun _ hb => hb.1

/-- The normalized block of a Hermitian block by a positive definite reference is
Hermitian.  `E^{-1/2}` is symmetric, so the congruence preserves symmetry. -/
theorem h6a_isHermitian_normalizedBlock {P Q : BlockMat d}
    (hP : (toFullBlockMat P).IsHermitian) (hQ : (toFullBlockMat Q).PosDef) :
    (toFullBlockMat (normalizedBlock P Q)).IsHermitian := by
  have hSIsymm : (matSqrt (toFullBlockMat Q)⁻¹)ᵀ = matSqrt (toFullBlockMat Q)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hQ.inv.posSemidef).1.isHermitian
  rw [r2a_normalizedBlock_flat, Matrix.IsHermitian,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.transpose_mul,
    hSIsymm,
    show (toFullBlockMat P)ᵀ = toFullBlockMat P by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using! hP,
    Matrix.mul_assoc]

/-- **The recentring step, with NO operator norm.**  A Hermitian doubled block is
dominated by `(1 + β) I`, where `β` is the spectral positive part of its recentring `N - I`:

`N ≤ (1 + β) · I_{2d}`,  `β = blockSpecBound (N - I)`.

This replaces `blockSize_le_one_add_blockExcess`, which goes through the norm and therefore needs
`blockSpecBound` subadditivity — the obstruction recorded at
`HC2b_DiagonalWeakRecentAvSum.lean`.  Here `h6a_blockSpecBound_attained`
(`HC2b_DiagonalWeakRecentLoewner.lean`) gives the Loewner
bound on `N - I` directly and the identity is added back on quadratic forms, so no norm and no
subadditivity is used. -/
theorem h6a_normalizedBlock_le_one_add_specBound {N : BlockMat d}
    (hN : (toFullBlockMat N).IsHermitian) :
    toFullBlockMat N ≤
      (1 + blockSpecBound (blockSub N (Book.Ch02.blockIdentity d))) • (1 : FullBlockMat d) := by
  set b : ℝ := blockSpecBound (blockSub N (Book.Ch02.blockIdentity d)) with hb
  have hloew : BlockMatLoewnerLE N (blockScale (1 + b) (Book.Ch02.blockIdentity d)) := by
    intro X
    have h := h6a_blockSpecBound_attained (blockSub N (Book.Ch02.blockIdentity d)) X
    rw [r2a_qform_blockScale, r2a_qform_identity, ← hb] at h
    have hs : blockVecDot X (blockMatVecMul (blockSub N (Book.Ch02.blockIdentity d)) X)
        = blockVecDot X (blockMatVecMul N X) - toFullBlockVec X ⬝ᵥ toFullBlockVec X := by
      rw [blockMatVecMul_blockSub, r2a_blockVecDot_sub_right, r2a_qform_identity]
    rw [hs] at h
    rw [r2a_qform_blockScale, r2a_qform_identity]
    linarith only [h]
  have hH : (toFullBlockMat (blockScale (1 + b) (Book.Ch02.blockIdentity d))).IsHermitian := by
    rw [r2a_toFullBlockMat_blockScale_identity]
    simp [Matrix.IsHermitian]
  have hres := Analysis.matrixOrder_of_blockMatLoewnerLE hN hH hloew
  rwa [r2a_toFullBlockMat_blockScale_identity] at hres

/-- A bound on the normalized block against the identity lifts back to a bound of the
block against its reference: `E^{-1/2} P E^{-1/2} ≤ c I  ⟹  P ≤ c E`.  This is the tail of
`HC2b_DiagonalWeakRecentSharpOrder.lean` with the operator norm replaced by an arbitrary
constant, which is what a consumer owning only a BOUND has. -/
theorem h6a_le_smul_of_normalizedBlock_le {P Q : BlockMat d} {c : ℝ}
    (hQ : (toFullBlockMat Q).PosDef)
    (hc : toFullBlockMat (normalizedBlock P Q) ≤ c • (1 : FullBlockMat d)) :
    toFullBlockMat P ≤ c • toFullBlockMat Q := by
  have hSsymm : (matSqrt (toFullBlockMat Q))ᵀ = matSqrt (toFullBlockMat Q) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using!
      (matSqrt_spec hQ.posSemidef).1.isHermitian
  have hSS : matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q) = toFullBlockMat Q :=
    (matSqrt_spec hQ.posSemidef).2
  have hSSI : matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q)⁻¹ = 1 :=
    Annealed.matSqrt_mul_matSqrt_inv_full hQ
  have hSIS : matSqrt (toFullBlockMat Q)⁻¹ * matSqrt (toFullBlockMat Q) = 1 :=
    Annealed.matSqrt_inv_mul_matSqrt_full hQ
  have hcongr := Analysis.matrix_congr_le hc (matSqrt (toFullBlockMat Q))
  rw [hSsymm] at hcongr
  have hleft : matSqrt (toFullBlockMat Q) * toFullBlockMat (normalizedBlock P Q) *
      matSqrt (toFullBlockMat Q) = toFullBlockMat P := by
    rw [r2a_normalizedBlock_flat]
    calc
      matSqrt (toFullBlockMat Q) *
            (matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P * matSqrt (toFullBlockMat Q)⁻¹) *
            matSqrt (toFullBlockMat Q)
          = matSqrt (toFullBlockMat Q) * matSqrt (toFullBlockMat Q)⁻¹ * toFullBlockMat P *
            (matSqrt (toFullBlockMat Q)⁻¹ * matSqrt (toFullBlockMat Q)) := by noncomm_ring
      _ = toFullBlockMat P := by rw [hSSI, hSIS, Matrix.one_mul, Matrix.mul_one]
  have hright : matSqrt (toFullBlockMat Q) * (c • (1 : FullBlockMat d)) *
      matSqrt (toFullBlockMat Q) = c • toFullBlockMat Q := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hSS]
  rwa [hleft, hright] at hcongr

/-- **The size step, carrier-free.**  `Z ≤ c E` as soon as `c` dominates
`1 + blockSpecBound (normalizedBlock Z E - I)`.  This is exactly the bound
`blockSize A E ≤ B²` once `blockSize` is read as a Loewner bound rather than as a norm. -/
theorem h6a_le_smul_of_specBound_le {Z E : BlockMat d} {c : ℝ}
    (hZ : (toFullBlockMat Z).IsHermitian) (hE : (toFullBlockMat E).PosDef)
    (hc : 1 + blockSpecBound (blockSub (normalizedBlock Z E) (Book.Ch02.blockIdentity d)) ≤ c) :
    toFullBlockMat Z ≤ c • toFullBlockMat E :=
  h6a_le_smul_of_normalizedBlock_le hE
    ((h6a_normalizedBlock_le_one_add_specBound
      (h6a_isHermitian_normalizedBlock hZ hE)).trans (r2a_smul_one_mono hc))

/-- `1 + x ≤ B²` whenever `√x ≤ B - 1`.  The squaring bookkeeping of the response-size
step, on bare reals. -/
theorem h6a_one_add_le_sq {x B : ℝ} (hx : 0 ≤ x) (hB : Real.sqrt x ≤ B - 1) :
    1 + x ≤ B ^ 2 := by
  have h0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hxs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  nlinarith [hB, h0, hxs]

/-- **Congruence transfer of a Loewner size bound.**  `Z ≤ c E` gives
`GᵀZG ≤ c GᵀEG` for ANY `G`: no positive definiteness, no invertibility, no symmetry.

This is the step that carries a bound stated in the `respMean` picture, which is where
`respAllScaleMax` (`AdaptedDefs.lean`) lives, into the `respEhatMinus` picture, which is
where the size input `hAE` lives, since `respEhatMinus = blockCongr (respG F) (respMean …)`
(`AdaptedDefs.lean`).  The equality
`h6a_blockOpNorm_recentred_blockCongr_eq` (`HC2b_DiagonalWeakRecentCongr.lean`) CANNOT be
used for this transfer, because it is an equality of OPERATOR NORMS while `respAllScaleMax`
carries a `blockSpecBound`, and `blockSpecBound ≤ ‖·‖` points the wrong way. -/
theorem h6a_blockCongr_le_smul {Z E : BlockMat d} (G : BlockMat d) {c : ℝ}
    (h : toFullBlockMat Z ≤ c • toFullBlockMat E) :
    toFullBlockMat (blockCongr G Z) ≤ c • toFullBlockMat (blockCongr G E) := by
  have hc := Analysis.matrix_congr_le h (toFullBlockMat G)
  rw [r2a_toFullBlockMat_blockCongr, r2a_toFullBlockMat_blockCongr]
  have hsm : (toFullBlockMat G)ᵀ * (c • toFullBlockMat E) * toFullBlockMat G =
      c • ((toFullBlockMat G)ᵀ * toFullBlockMat E * toFullBlockMat G) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rwa [hsm] at hc

/-- Every weighted cell excess is bounded by the all-scale maximum, on the branch
where that supremum is finite.  This is `weighted_excess_le_diagonalWeakMaximum_toReal`, whose
finiteness hypothesis `hfinite : diagonalWeakMaximum … ≠ ⊤` is here the real-valued `BddAbove` of
the same set (this tree's `respAllScaleMax` is an `sSup` in `ℝ`, not in `ℝ≥0∞`). -/
theorem h6a_weighted_specBound_le_respAllScaleMax [NeZero d] (P : Measure (CoeffSpace d))
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) (n : ℕ) {w : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d n)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
      ≤ respAllScaleMax P γ jStar F t a := by
  rw [respAllScaleMax]
  exact le_csSup hbdd ⟨n, w, hw, rfl⟩

/-! ## The response-size step, assembled on the tree's own carriers -/

/-- **THE RESPONSE-SIZE STEP, in the `respMean` picture.**  The coarse response of an
aligned child cell sits below the scale-`t` reference mean, dilated by the square of the printed
geometric weight:

`𝐀(z + U_{t-n}; a) ≤ (1 + √M · 3^{ρn/2})² · E_t`,  `M = respAllScaleMax P γ jStar F t a`.

This is the `hsize` bound of `diagonalWeak_recent_average_bound`, fed by
`sqrt_blockSize_adaptedResponse_le_of_maximum_finite`.  The bound
`blockSize (adaptedResponse q k w a) E` is the Loewner statement here; `blockExcess` is the
`blockSpecBound` of the recentred normalized block, the very quantity `respAllScaleMax`
(`AdaptedDefs.lean`) is built from, so no excess carrier is needed either.
`h6a_sqrt_le_sqrt_mul_rpow_of_weighted_le` (`HC2b_DiagonalWeakRecentAvSum.lean`) supplies
the geometric-weight arithmetic, already in this tree. -/
theorem h6a_coarseBlock_le_sq_smul_respMean [NeZero d] (P : Measure (CoeffSpace d))
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) (n : ℕ) {w : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d n)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hE : (toFullBlockMat (respMean P jStar F t)).PosDef) :
    toFullBlockMat (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a)
      ≤ (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2
        • toFullBlockMat (respMean P jStar F t) := by
  set Z : BlockMat d :=
    coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a with hZdef
  set b : ℝ := blockSpecBound (blockSub (normalizedBlock Z (respMean P jStar F t))
    (Book.Ch02.blockIdentity d)) with hbdef
  have hb0 : 0 ≤ b := h6a_blockSpecBound_nonneg _
  have hwt : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) * b ≤ respAllScaleMax P γ jStar F t a :=
    h6a_weighted_specBound_le_respAllScaleMax P γ jStar F t a n hw hbdd
  have hfac0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hM0 : 0 ≤ respAllScaleMax P γ jStar F t a :=
    le_trans (mul_nonneg hfac0 hb0) hwt
  have hsq : Real.sqrt b ≤ Real.sqrt (respAllScaleMax P γ jStar F t a) *
      (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) :=
    h6a_sqrt_le_sqrt_mul_rpow_of_weighted_le n hM0 hwt
  have hZherm : (toFullBlockMat Z).IsHermitian :=
    (Analysis.toFullBlockMat_isHermitian_iff Z).mpr
      (isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1))
  exact h6a_le_smul_of_specBound_le hZherm hE
    (h6a_one_add_le_sq hb0 (by linarith only [hsq]))

/-- **THE RESPONSE-SIZE STEP, in the `Ehat^-` picture.**  The previous bound,
conjugated by the shear `G(F)`, which is exactly the passage from `respMean` to
`respEhatMinus = blockCongr (respG F) (respMean …)` (`AdaptedDefs.lean`).

A consumer closes the size input `hAE` from this by identifying its numerator: the coarse block of
the recentred field, `Book.Ch02.coarseBlockMatrix U (respCoeffMinus F a)`, is
`blockCongr (respG F) (coarseBlock U a)` — the shear identity
`h7_coarseBlockMatrix_sub_skew_eq_blockCongr` (`AdaptedSwarm.lean`, `private` there and not
restated here). -/
theorem h6a_coarseBlock_congr_le_sq_smul_respEhatMinus [NeZero d] (P : Measure (CoeffSpace d))
    (γ : ℝ) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) (n : ℕ) {w : Fin d → ℤ}
    (hw : w ∈ triadicIndexBox d n)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (hE : (toFullBlockMat (respMean P jStar F t)).PosDef) :
    toFullBlockMat (blockCongr (respG F)
        (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) a))
      ≤ (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) ^ 2
        • toFullBlockMat (respEhatMinus P jStar F t) := by
  rw [respEhatMinus]
  exact h6a_blockCongr_le_smul (respG F)
    (h6a_coarseBlock_le_sq_smul_respMean P γ jStar F t a n hw hbdd hE)

/-! ## The restriction step, and the per-`w` child cell as a Chapter-2 domain

The restriction step supplies `exists_restrict_solution` and
`exists_restrict_solution_adaptedCellAtCenter`.  A consumer needs them to
produce the SECOND argument of the recentred-difference energy map: the parent optimizer,
restricted to the child cell. -/

/-- An aligned adapted cell is nonempty.  This is proved from the PUBLIC
`volume_adaptedCellAtCenter_toReal_pos` (`HC2b_DiagonalWeakRecentSupport.lean`), mirroring the
`private` `adaptedCellAtCenter_nonempty` (`…:366`). -/
theorem h6a_adaptedCellAtCenter_nonempty [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) : (adaptedCellAtCenter q k w).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hpos := volume_adaptedCellAtCenter_toReal_pos q hq k w
  rw [h] at hpos
  simp at hpos

/-- **The ONLY definition in this module.**  The aligned adapted cell `z + q□_k` as a
Chapter-2 domain, the per-`w` twin of `adaptedDomain` (`HC1_DomainBridge.lean`).

This definition selects NO constant and carries no inequality of its own: its
two structure obligations are Props about the carrier `adaptedCellAtCenter q k w`, and both are
discharged inside the definition itself, from `isOpenBoundedConvexDomain_adaptedCellAtCenter`
(`HC2b_DiagonalWeakRecentSupport.lean`, PUBLIC) and the nonemptiness proved above.  Its
satisfiability is therefore constructive; it is nevertheless exhibited as an explicit `∃`,
before any consumer. -/
def adaptedDomainAt [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) :
    Book.Ch02.Domain d :=
  { carrier := adaptedCellAtCenter q k w
    isDomain := isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w
    nonempty := h6a_adaptedCellAtCenter_nonempty q hq k w }

@[simp] theorem adaptedDomainAt_carrier [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) :
    ((adaptedDomainAt q hq k w : Book.Ch02.Domain d) : Set (Vec d)) = adaptedCellAtCenter q k w := rfl

/-- A solution restricts to any Chapter-2 subdomain carrying a pointwise elliptic
representative of the same field.  This is `exists_restrict_solution`. -/
theorem h6a_exists_restrict_solution {U V : Domain d} {lam Lam : ℝ}
    {b : CoeffOn U} {c : CoeffOn V} (hrep : c.toCoeffField = b.toCoeffField)
    (hVU : (V : Set (Vec d)) ⊆ (U : Set (Vec d)))
    (hEll : IsEllipticFieldOn lam Lam (V : Set (Vec d)) c.toCoeffField)
    (u : Book.Ch02.Solution U b) :
    ∃ z : Book.Ch02.Solution V c, z.toH1.grad = u.toH1.grad := by
  refine ⟨{ toH1 := u.toH1.restrict V.isOpen hVU, isHarmonic := ?_ }, rfl⟩
  rw [hrep]
  exact u.isHarmonic.restrict_of_isOpen_of_isEllipticFieldOn U.isOpen V.isOpen hVU
    (hrep ▸ hEll)

/-- The parent optimizer restricts to an admissible solution on every aligned child
cell of the triadic subdivision.  This is `exists_restrict_solution_adaptedCellAtCenter`, whose
membership hypothesis `hmem : adaptedCellCenter q j w ∈ adaptedCell q p` is here the tree's own
indexing hypothesis `w ∈ triadicIndexBox d n`, through `adaptedCellAtCenter_subset_adaptedCell`
(`HC1_DomainBridge.lean`). -/
theorem h6a_exists_restrict_solution_adaptedCellAtCenter [NeZero d] (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (n : ℕ) {w : Fin d → ℤ} (hw : w ∈ triadicIndexBox d n) {lam Lam : ℝ}
    {b : CoeffOn (adaptedDomain q hq t)}
    {c : CoeffOn (adaptedDomainAt q hq (t - (n : ℤ)) w)}
    (hrep : c.toCoeffField = b.toCoeffField)
    (hEll : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) c.toCoeffField)
    (u : Book.Ch02.Solution (adaptedDomain q hq t) b) :
    ∃ z : Book.Ch02.Solution (adaptedDomainAt q hq (t - (n : ℤ)) w) c,
      z.toH1.grad = u.toH1.grad :=
  h6a_exists_restrict_solution hrep (adaptedCellAtCenter_subset_adaptedCell q t n hw) hEll u

end

end Homogenization.HighContrast.Multiscale
