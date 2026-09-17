import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm

/-!
# HC bridge II: carriers and closed helpers for the diagonal weak-norm bound

Carriers and closed helpers for the diagonal weak-norm estimate of the paper
`p.response.transfer`, depending only on `HC2_WeakSeminorm.lean`.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter blockSub normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Carriers: the two finite sums and the pathwise optimizer energy.
Index convention: the absolute-scale carriers are indexed by the scale `k : ℤ`, over the aligned
index set `alignedIndex q k t`; the grid carriers used here are indexed by the DEPTH `n : ℕ` below
`t`, over `triadicIndexBox d n` (`AdaptedDefs.lean`), exactly as `besovSeminorm`
 and `respAllScaleMax` already are.  So `k = t - n` throughout, and
`alignedIndex q (t-n) t ↦ triadicIndexBox d n`. -/

/-- The recent cell defect `C_{k,t}(E)` at depth `n` (scale `k = t - n`).  The root-mean-square,
over the `3^{nd}` scale-`(t-n)` subcells of `U_t`, of the `E`-normalized difference between the
cell's coarse block and the coarse block of `U_t`.
The size carrier is the TWO-SIDED `‖E^{-1/2} D E^{-1/2}‖`, written here as
`‖toFullBlockMat (normalizedBlock D E)‖`.  The one-sided `blockSpecBound (normalizedBlock D E)`
controls only the upper spectral side and CANNOT carry the pointwise cell step: with `E = I₁₈`,
`D = diag(-1, 1/17, …, 1/17)` (`d = 9`), `blockSpecBound (normalizedBlock D E) = 1/17` while
`|D e₁| = 1 > 16/17`, so even the explicit constant `16` does not repair it.  `blockSpecBound`
remains correct for `respAllScaleMax` (`AdaptedDefs.lean`), which is the spectral positive part
of `p.response.transfer`; the recent cell differences are bounded in their FULL norm at
`p.response.transfer`.
The defect is built from the coarse blocks of the RECENTRED field `b` (`b = respCoeffMinus F a`
at the call site) and normalized by the congruenced `E = respEhatMinus`; mixing the uncongruenced
numerator `coarseBlock … a` with the congruenced denominator is not the fixed-congruence invariant
carrier of `p.response.transfer`.
The sum `avsum` (`WeakNorm.lean`) is spelled out as `(card)⁻¹ * ∑`, as `besovSeminorm` does. -/
def weakCellDefect (q : Mat d) (t : ℤ) (n : ℕ) (E : BlockMat d) (b : CoeffField d) : ℝ :=
  Real.sqrt
    (((triadicIndexBox d n).card : ℝ)⁻¹ *
      ∑ w ∈ triadicIndexBox d n,
        ‖toFullBlockMat
            (normalizedBlock
              (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) E)‖ ^ 2)

/-- The recent averaged normalized defect `D_{k,t}(E)` at depth `n` (scale `k = t - n`).  The flat
average over the scale-`(t-n)` subcells of `U_t` of the `E`-normalized cell-minus-`U_t` block
differences, taken entrywise through `toFullBlockMat`.
The defect is built from the recentred field `b`, normalized by the congruenced `E`, as in
`weakCellDefect`. -/
def weakAverageDefect (q : Mat d) (t : ℤ) (n : ℕ) (E : BlockMat d) (b : CoeffField d) :
    BlockMat d :=
  ofFullBlockMat
    (((triadicIndexBox d n).card : ℝ)⁻¹ •
      ∑ w ∈ triadicIndexBox d n,
        toFullBlockMat
          (normalizedBlock
            (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
              (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) E))

/-- The recent cell sum `𝒰_cell`, the `3^{-n/2}`-weighted sum of the recent cell defects over
the finite window `n ≤ H`, at the exponent `s = 1/2`.
`Finset.range (H+1)` includes both endpoints. -/
def weakCellSum (q : Mat d) (t : ℤ) (H : ℕ) (E : BlockMat d) (b : CoeffField d) : ℝ :=
  ∑ n ∈ Finset.range (H + 1),
    (3 : ℝ) ^ (-((n : ℝ) / 2)) * weakCellDefect q t n E b

/-- The recent averaged-defect sum `𝒰_av`, the `3^{-(1/2 - rho/2)n}`-weighted sum of the square
roots of the sizes of the averaged recent defects over the finite window `n ≤ H`, at `s = 1/2`.
The inner size is the TWO-SIDED norm of `D`, here `‖toFullBlockMat D‖`; the one-sided
`blockSpecBound D` suffers the same loss as in `weakCellDefect`. -/
def weakAverageSum (q : Mat d) (t : ℤ) (H : ℕ) (rho : ℝ) (E : BlockMat d) (b : CoeffField d) :
    ℝ :=
  ∑ n ∈ Finset.range (H + 1),
    (3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ)) *
      Real.sqrt ‖toFullBlockMat (weakAverageDefect q t n E b)‖

/-- The pathwise normalized optimizer energy `ℰ_t = (2 J_t)^{1/2} = ‖symm(b)^{1/2}∇v‖_{L̲²(U)}`
(`p.response.transfer`).  CoarseGraining's `variationEnergyValue` (`Book/Ch02/Response.lean`)
needs a `Domain d` together with a `CoeffOn` of it and a `Solution`, none of which the binders here
carry (they carry a bare `Set (Vec d)` and an `AHarmonicFunction`).  The integrand is therefore
written directly: `∇v · symm(b) ∇v = ∇v · b ∇v = (X x).1 · (X x).2` for the doubled optimizer
field `X = optimizerField b u` (`AdaptedDefs.lean`), so this is the same real number. -/
def weakOptimizerEnergy (U : Set (Vec d)) (b : CoeffField d) (u : AHarmonicFunction b U) : ℝ :=
  Real.sqrt
    (volumeAverage U fun x =>
      vecDot (optimizerField b u x).1 (optimizerField b u x).2)

/-! ## Helpers.  The pointwise comparison identity in the current carriers, the mean identity
generalized off the centred cell, child-maximizer existence on every aligned subcell, and the
nonnegativity facts. -/

omit [NeZero d] in
theorem matVecMul_sub_mat (M N : Mat d) (v : Vec d) :
    matVecMul (M - N) v = matVecMul M v - matVecMul N v := by
  funext i
  simp [matVecMul, sub_mul, Finset.sum_sub_distrib]

omit [NeZero d] in
theorem matVecMul_sub_vec (M : Mat d) (v w : Vec d) :
    matVecMul M (v - w) = matVecMul M v - matVecMul M w := by
  funext i
  simp [matVecMul, mul_sub, Finset.sum_sub_distrib]

omit [NeZero d] in
theorem blockMatVecMul_blockSub (A B : BlockMat d) (x : BlockVec d) :
    blockMatVecMul (blockSub A B) x = blockMatVecMul A x - blockMatVecMul B x := by
  refine Prod.ext ?_ ?_ <;>
    simp [blockMatVecMul, blockSub, matVecMul_sub_mat] <;> abel

omit [NeZero d] in
theorem blockMatVecMul_sub_vec (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  refine Prod.ext ?_ ?_ <;>
    simp [blockMatVecMul, matVecMul_sub_vec] <;> abel

omit [NeZero d] in
/-- The child-minus-parent mean difference is the reflected action of the block defect. -/
theorem blockResponseMean_sub_blockResponseMean (A B : BlockMat d) (x : BlockVec d) :
    blockResponseMean A x - blockResponseMean B x =
      blockMatVecMul (blockSwap d) (blockMatVecMul (blockSub A B) x) := by
  rw [blockMatVecMul_blockSub, blockMatVecMul_sub_vec, blockResponseMean, blockResponseMean]
  abel

/-- The mean identity on a general open bounded convex domain of positive volume. -/
theorem cellAverage_optimizerField_eq_blockResponseMean_of_domain
    {U : Set (Vec d)} (hconv : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal)
    {lam Lam : ℝ} {b : CoeffField d} (hb : IsEllipticFieldOn lam Lam U b)
    (p r : Vec d) (u : AHarmonicFunction b U) (hu : IsResponseMaximizer U p r b u) :
    cellAverage U (optimizerField b u) =
      blockResponseMean (coarseBlockMatrix U b) (-p, r) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  have hne : U.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hvol
    simp at hvol
  have hInt : ResponseLinearIntegrabilityData U b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hb
  have hA : IsCoarseBlockMatrix U b (coarseBlockMatrix U b) :=
    isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hconv hb hvol
  have hJ : ∀ x y : Vec d, ResponseJ U x y b =
      (1 / 2 : ℝ) * blockVecDot (-x, y)
        (blockMatVecMul (coarseBlockMatrix U b) (-x, y)) - vecDot x y := fun x y =>
    responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain hconv hb hvol x y
  set A : BlockMat d := coarseBlockMatrix U b with hAdef
  have hsym := hA.1
  have hURLL : ∀ i j, A.upperRight i j = A.lowerLeft j i := fun i j => hsym (Sum.inl i) (Sum.inr j)
  have hLRs : ∀ i j, A.lowerRight i j = A.lowerRight j i := fun i j => hsym (Sum.inr i) (Sum.inr j)
  have hULs : ∀ i j, A.upperLeft i j = A.upperLeft j i := fun i j => hsym (Sum.inl i) (Sum.inl j)
  have hsw : ∀ x y : Vec d, vecDot x (matVecMul A.upperRight y) =
      vecDot y (matVecMul A.lowerLeft x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hURLL x y
  have hlr : ∀ x y : Vec d, vecDot x (matVecMul A.lowerRight y) =
      vecDot y (matVecMul A.lowerRight x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hLRs x y
  have hul : ∀ x y : Vec d, vecDot x (matVecMul A.upperLeft y) =
      vecDot y (matVecMul A.upperLeft x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hULs x y
  have hQ : ∀ x y : Vec d, ResponseJ U x y b =
      (1 / 2 : ℝ) * (vecDot x (matVecMul A.upperLeft x) - vecDot x (matVecMul A.upperRight y)
        - vecDot y (matVecMul A.lowerLeft x) + vecDot y (matVecMul A.lowerRight y))
        - vecDot x y := by
    intro x y
    rw [hJ x y]
    simp only [blockVecDot, blockMatVecMul, vecDot_add_right, vecDot_neg_left, matVecMul_neg,
      vecDot_neg_right]
    ring
  have hgrad : ∀ i : Fin d, volumeAverage U (fun x => u.toH1.grad x i) =
      -p i + (matVecMul A.lowerRight r) i - (matVecMul A.lowerLeft p) i := by
    intro i
    obtain ⟨ug⟩ := ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hconv hb 0
      (Pi.single i 1)
    rw [basic_cg_identities_average_gradient_coordinate_of_isResponseMaximizer U b p r hInt u hu i
      (ug : AHarmonicFunction b U) ug.isResponseMaximizer]
    have e1 : vecDot p (matVecMul A.upperRight (Pi.single i 1)) = (matVecMul A.lowerLeft p) i := by
      rw [hsw p (Pi.single i 1), vecDot_single_left]
    have e3 : vecDot r (matVecMul A.lowerRight (Pi.single i 1)) = (matVecMul A.lowerRight r) i := by
      rw [hlr r (Pi.single i 1), vecDot_single_left]
    have e4 : vecDot (Pi.single i 1) (matVecMul A.lowerLeft p) = (matVecMul A.lowerLeft p) i :=
      vecDot_single_left _ _
    have e2 : vecDot (Pi.single i 1) (matVecMul A.lowerRight r) = (matVecMul A.lowerRight r) i :=
      vecDot_single_left _ _
    have e5 : vecDot p (Pi.single i 1) = p i := vecDot_single_right _ _
    rw [hQ p r, hQ 0 (Pi.single i 1), hQ p (r - Pi.single i 1)]
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right, vecDot_add_left,
      vecDot_neg_right, vecDot_neg_left, matVecMul_zero, vecDot_zero_left, vecDot_zero_right]
    linarith [e1, e2, e3, e4, e5]
  have hflux : ∀ i : Fin d, volumeAverage U (fun x => matVecMul (b x) (u.toH1.grad x) i) =
      r i + (matVecMul A.upperRight r) i - (matVecMul A.upperLeft p) i := by
    intro i
    obtain ⟨uf⟩ := ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hconv hb
      (Pi.single i 1) 0
    rw [basic_cg_identities_average_flux_coordinate_of_isResponseMaximizer U b p r hInt u hu i
      (uf : AHarmonicFunction b U) uf.isResponseMaximizer]
    have f1 : vecDot p (matVecMul A.upperLeft (Pi.single i 1)) = (matVecMul A.upperLeft p) i := by
      rw [hul p (Pi.single i 1), vecDot_single_left]
    have f2 : vecDot (Pi.single i 1) (matVecMul A.upperLeft p) = (matVecMul A.upperLeft p) i :=
      vecDot_single_left _ _
    have f3 : vecDot (Pi.single i 1) (matVecMul A.upperRight r) = (matVecMul A.upperRight r) i :=
      vecDot_single_left _ _
    have f4 : vecDot r (matVecMul A.lowerLeft (Pi.single i 1)) = (matVecMul A.upperRight r) i := by
      rw [← hsw (Pi.single i 1) r, vecDot_single_left]
    have f5 : vecDot (Pi.single i 1) r = r i := vecDot_single_left _ _
    rw [hQ (p - Pi.single i 1) r, hQ p r, hQ (Pi.single i 1) 0]
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right, vecDot_add_left,
      vecDot_neg_right, vecDot_neg_left, matVecMul_zero, vecDot_zero_left, vecDot_zero_right]
    linarith [f1, f2, f3, f4, f5]
  have hrhs1 : (blockResponseMean A (-p, r)).1 =
      fun i => -p i + (matVecMul A.lowerRight r) i - (matVecMul A.lowerLeft p) i := by
    funext i
    simp only [blockResponseMean, Prod.fst_add, blockMatVecMul_blockSwap_fst]
    simp [blockMatVecMul, matVecMul_neg]
    ring
  have hrhs2 : (blockResponseMean A (-p, r)).2 =
      fun i => r i + (matVecMul A.upperRight r) i - (matVecMul A.upperLeft p) i := by
    funext i
    simp only [blockResponseMean, Prod.snd_add, blockMatVecMul_blockSwap_snd]
    simp [blockMatVecMul, matVecMul_neg]
    ring
  refine Prod.ext ?_ ?_
  · rw [hrhs1]; funext i; exact hgrad i
  · rw [hrhs2]; funext i; exact hflux i

/-- The mean identity for a field that is only a.e. equal to an elliptic representative. -/
theorem cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    {U : Set (Vec d)} (hconv : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal)
    {lam Lam : ℝ} {b f : CoeffField d} (hf : IsEllipticFieldOn lam Lam U f)
    (hae : b =ᵐ[volumeMeasureOn U] f)
    (p r : Vec d) (u : AHarmonicFunction b U) (hu : IsResponseMaximizer U p r b u) :
    cellAverage U (optimizerField b u) =
      blockResponseMean (coarseBlockMatrix U b) (-p, r) := by
  have huT : IsResponseMaximizer U p r f (aHarmonicFunctionOfAEEqCoeff hae u) := by
    intro z
    have key := hu (aHarmonicFunctionOfAEEqCoeff hae.symm z)
    have h1 : volumeAverage U (scalarResponseIntegrand U f p r z) =
        volumeAverage U (scalarResponseIntegrand U b p r
          (aHarmonicFunctionOfAEEqCoeff hae.symm z)) :=
      volumeAverage_scalarResponseIntegrand_congr hae.symm p r z _ (fun _ => rfl)
    have h2 : volumeAverage U (scalarResponseIntegrand U b p r u) =
        volumeAverage U (scalarResponseIntegrand U f p r
          (aHarmonicFunctionOfAEEqCoeff hae u)) :=
      volumeAverage_scalarResponseIntegrand_congr hae p r u _ (fun _ => rfl)
    rw [h1, ← h2]
    exact key
  have hkey := cellAverage_optimizerField_eq_blockResponseMean_of_domain hconv hvol hf p r
    (aHarmonicFunctionOfAEEqCoeff hae u) huT
  have hof : optimizerField b u =ᵐ[volumeMeasureOn U]
      optimizerField f (aHarmonicFunctionOfAEEqCoeff hae u) := by
    filter_upwards [hae] with x hx
    simp [optimizerField, aHarmonicFunctionOfAEEqCoeff, hx]
  rw [cellAverage_congr_ae (subset_refl U) hof, hkey, coarseBlockMatrix_congr_of_ae_eq hae]

/-- Every aligned adapted cell is an open bounded convex domain. -/
theorem isOpenBoundedConvexDomain_adaptedCellAtCenter (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) : IsOpenBoundedConvexDomain (adaptedCellAtCenter q k w) := by
  show IsOpenBoundedConvexDomain (HighContrast.adaptedCellTranslate q k (adaptedCellCenter q k w))
  rw [Annealed.adaptedCellTranslate_eq_cg_affine]
  exact isOpenBoundedConvexDomain_affine_openCube q hq k _

/-- Every aligned adapted cell has positive volume. -/
theorem volume_adaptedCellAtCenter_toReal_pos (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) : 0 < (volume (adaptedCellAtCenter q k w)).toReal := by
  show 0 < (volume (HighContrast.adaptedCellTranslate q k (adaptedCellCenter q k w))).toReal
  rw [Annealed.adaptedCellTranslate_eq_cg_affine]
  exact volume_affine_openCube_toReal_pos q hq k _

/-- The mean identity for the recentred field `a_-` on an arbitrary aligned adapted cell. -/
theorem cellAverage_optimizerField_respCoeffMinus_eq_at
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) (u : AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter q k w))
    (hu : IsResponseMaximizer (adaptedCellAtCenter q k w) p r (respCoeffMinus F a) u) :
    cellAverage (adaptedCellAtCenter q k w) (optimizerField (respCoeffMinus F a) u) =
      blockResponseMean
        (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffMinus F a)) (-p, r) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (adaptedCellAtCenter q k w) (fun x => f x - respg F) :=
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F)
  refine cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w)
    (volume_adaptedCellAtCenter_toReal_pos q hq k w) hEll' ?_ p r u hu
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffMinus, hx]

/-- The mean identity for the recentred field `a_-` on the centred cell `U_t`. -/
theorem cellAverage_optimizerField_respCoeffMinus_eq
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (p r : Vec d) (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u) :
    cellAverage (HighContrast.adaptedCell q t) (optimizerField (respCoeffMinus F a) u) =
      blockResponseMean
        (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a)) (-p, r) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (HighContrast.adaptedCell q t) (fun x => f x - respg F) :=
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F)
  refine cellAverage_optimizerField_eq_blockResponseMean_of_aeEq
    (adaptedCell_isOpenBoundedConvexDomain q hq t) ?_ hEll' ?_ p r u hu
  · have hset : HighContrast.adaptedCell q t =
        translateSet 0 ((matVecMul q) '' (openCubeSet (originCube d t))) := by
      rw [← Annealed.adaptedCellTranslate_eq_cg_affine q t 0]
      simp [HighContrast.adaptedCellTranslate]
    rw [hset]; exact volume_affine_openCube_toReal_pos q hq t 0
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]

/-- POINTWISE COMPARISON, identity half.  The child-cell minus parent-cell optimizer mean
difference is exactly the reflected action of the coarse-block defect that `weakCellDefect`
normalizes. -/
theorem cellAverage_optimizerField_respCoeffMinus_sub_eq
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (k : ℤ) (w : Fin d → ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d)
    (v : AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter q k w))
    (hv : IsResponseMaximizer (adaptedCellAtCenter q k w) p r (respCoeffMinus F a) v)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r (respCoeffMinus F a) u) :
    cellAverage (adaptedCellAtCenter q k w) (optimizerField (respCoeffMinus F a) v) -
        cellAverage (HighContrast.adaptedCell q t) (optimizerField (respCoeffMinus F a) u) =
      blockMatVecMul (blockSwap d)
        (blockMatVecMul
          (blockSub (coarseBlockMatrix (adaptedCellAtCenter q k w) (respCoeffMinus F a))
            (coarseBlockMatrix (HighContrast.adaptedCell q t) (respCoeffMinus F a))) (-p, r)) := by
  rw [cellAverage_optimizerField_respCoeffMinus_eq_at q hq k w F a p r v hv,
    cellAverage_optimizerField_respCoeffMinus_eq q hq t F a p r u hu,
    blockResponseMean_sub_blockResponseMean]

/-- Nonemptiness of an aligned adapted cell. -/
private theorem adaptedCellAtCenter_nonempty (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) :
    (adaptedCellAtCenter q k w).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hpos := volume_adaptedCellAtCenter_toReal_pos q hq k w
  rw [h] at hpos
  simp at hpos

/-- Existence of a child maximizer for `a_-` on every aligned adapted cell, the subcell analogue
of `nonempty_scalarCanonicalMaximizer_respCoeffMinus`. -/
theorem nonempty_scalarCanonicalMaximizer_respCoeffMinus_at (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q k w) p r (respCoeffMinus F a)) := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  have hEll' : IsEllipticFieldOn lam (2 * Lam + 2 * ‖respg F‖ ^ 2 / lam)
      (adaptedCellAtCenter q k w) (fun x => f x - respg F) :=
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F)
  have hbase : Nonempty (ScalarCanonicalMaximizer (adaptedCellAtCenter q k w) p r
      (fun x => f x - respg F)) :=
    ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
      (adaptedCellAtCenter_nonempty q hq k w) (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq k w)
      hEll' p r
  refine nonempty_scalarCanonicalMaximizer_of_aeEq ?_ p r hbase
  refine MeasureTheory.ae_restrict_of_ae ?_
  filter_upwards [hae] with x hx
  simp [respCoeffMinus, hx]

omit [NeZero d] in
/-- Nonnegativity of the recent cell defect. -/
private theorem weakCellDefect_nonneg (q : Mat d) (t : ℤ) (n : ℕ) (E : BlockMat d) (b : CoeffField d) :
    0 ≤ weakCellDefect q t n E b := Real.sqrt_nonneg _

omit [NeZero d] in
/-- Nonnegativity of the recent cell sum. -/
theorem weakCellSum_nonneg (q : Mat d) (t : ℤ) (H : ℕ) (E : BlockMat d) (b : CoeffField d) :
    0 ≤ weakCellSum q t H E b :=
  Finset.sum_nonneg fun n _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (weakCellDefect_nonneg q t n E b)

omit [NeZero d] in
/-- Nonnegativity of the recent averaged-defect sum. -/
theorem weakAverageSum_nonneg (q : Mat d) (t : ℤ) (H : ℕ) (rho : ℝ) (E : BlockMat d)
    (b : CoeffField d) : 0 ≤ weakAverageSum q t H rho E b :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)

omit [NeZero d] in
/-- The swap block exchanges the two slots. -/
theorem blockMatVecMul_blockSwap (X : BlockVec d) :
    blockMatVecMul (blockSwap d) X = (X.2, X.1) :=
  Prod.ext (blockMatVecMul_blockSwap_fst X) (blockMatVecMul_blockSwap_snd X)

omit [NeZero d] in
/-- Conjugating the metric block `M_0 = diag(m, m^{-1})` by the swap `R` inverts it:
`R^t M_0 R = diag(m^{-1}, m)`.  This is the step that turns the reflected mean difference
`R D x` of the pointwise comparison into the `M_0^{-1}` quadratic form. -/
theorem blockVecDot_blockSwap_respM0 (F : BlockMat d) (y : BlockVec d) :
    blockVecDot (blockMatVecMul (blockSwap d) y)
        (blockMatVecMul (respM0 F) (blockMatVecMul (blockSwap d) y)) =
      blockVecDot y
        (blockMatVecMul
          ⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ y) := by
  rw [blockMatVecMul_blockSwap]
  simp [blockVecDot, blockMatVecMul, respM0, matVecMul, vecDot]
  ring

end

end Homogenization.HighContrast.Multiscale
