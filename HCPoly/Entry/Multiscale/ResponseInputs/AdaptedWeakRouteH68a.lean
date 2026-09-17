import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65bMeasurable

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter blockScale blockSub coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix matSqrt matSqrt_spec normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The recent-cell differences (`p.response.transfer`) -/

/-! ### The η-kernel's hypothesis is one-sided.

`respAllScaleMax` is built from `blockSpecBound`, i.e. from the *spectral positive part*
`|(E_t^{-1/2}A_k(z)E_t^{-1/2} - I)_+|` of the paper (`p.response.transfer`).  It
therefore majorizes the recent-cell defect only from ABOVE.  The conclusion of the η-kernel asks for
`∫ ‖D_{n,w}‖^2 ≤ K_n η^{2/Q}` from `∫ M^Q ≤ C_m η` alone; the theorem below shows that this
implication is FALSE, and that the reachable exponent from a one-sided majorant is `η^{1/Q}`,
not `η^{2/Q}`.

The paper does not claim otherwise: at `p.response.transfer` the recent cell differences
`V_{k,t}(z) - V_t + (P_{k,t} - I)` are bounded in `L^2` by `C_H η^{1/Q}` using **the fluctuation
history** (two-sided, `fluctuationHistory`) for the first two terms and **the mean history**
(`meanPenalty_Q(P_{k,t}) ≤ 3^{α(t-1-k)}η`) for the third.  Neither carrier is present in the
hypotheses of `integral_recentDefect_sq_le_minus/plus`. -/

/-! ### Local helpers for the η-kernel

These close the FIRST conjunct (`AEStronglyMeasurable`) of both η-kernel twins, and are
independent of the `η` exponent.

`isOpenBoundedConvexDomain_adaptedCellAtCenter` and `volume_adaptedCellAtCenter_toReal_pos`
are `private` in `HC2b_DiagonalWeakRecentSupport.lean`), which IS in this
file's import closure.  The two proofs are three lines each over public CoarseGraining lemmas,
so they are restated here with citations. -/

-- transcribed: HC2b_DiagonalWeakRecentSupport.lean (private)
private theorem h68_isOpenBoundedConvexDomain_adaptedCellAtCenter [NeZero d] (q : Mat d)
    (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) :
    IsOpenBoundedConvexDomain (adaptedCellAtCenter q k w) := by
  show IsOpenBoundedConvexDomain (HighContrast.adaptedCellTranslate q k (adaptedCellCenter q k w))
  rw [Annealed.adaptedCellTranslate_eq_cg_affine]
  exact isOpenBoundedConvexDomain_affine_openCube q hq k _

-- transcribed: HC2b_DiagonalWeakRecentSupport.lean (private)
private theorem h68_volume_adaptedCellAtCenter_toReal_pos [NeZero d] (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) : 0 < (volume (adaptedCellAtCenter q k w)).toReal := by
  show 0 < (volume (HighContrast.adaptedCellTranslate q k (adaptedCellCenter q k w))).toReal
  rw [Annealed.adaptedCellTranslate_eq_cg_affine]
  exact volume_affine_openCube_toReal_pos q hq k _

/-- `HasQuadraticMu` on every ALIGNED adapted cell. -/
theorem h68_hasQuadraticMu_adaptedCellAtCenter [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ)
    (w : Fin d → ℤ) (a : CoeffSpace d) :
    HasQuadraticMu (adaptedCellAtCenter q j w) (⇑a.1 : CoeffField d) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j (adaptedCellCenter q j w) a
  have hConv : IsOpenBoundedConvexDomain (adaptedCellAtCenter q j w) :=
    h68_isOpenBoundedConvexDomain_adaptedCellAtCenter q hq j w
  let : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q j w)) :=
    hConv.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (adaptedCellAtCenter q j w)).toReal :=
    h68_volume_adaptedCellAtCenter_toReal_pos q hq j w
  obtain ⟨R, ⟨compat⟩⟩ :=
    exists_recovery_compatibility_of_isOpenBoundedConvexDomain hConv hEll hvol
  obtain ⟨Qm, hQm⟩ := R.hasQuadraticMuOfIsEllipticFieldOn hEll hvol compat
  exact ⟨Qm, fun Pv => by rw [Mu_congr_of_ae_eq (ae_restrict_of_ae hae) Pv]; exact hQm Pv⟩

/-! ### the η-kernel measurability layer -/

/-- Entrywise measurability is preserved by a fixed two-sided matrix product. -/
theorem h68_measurable_mul_mul {Ω : Type*} [MeasurableSpace Ω] (L R : FullBlockMat d)
    (X : Ω → FullBlockMat d) (hX : ∀ ζ δ, Measurable fun ω => X ω ζ δ) (α β : BlockCoord d) :
    Measurable fun ω => (L * X ω * R) α β := by
  have hrw : (fun ω => (L * X ω * R) α β)
      = fun ω => ∑ δ : BlockCoord d, (∑ ζ : BlockCoord d, L α ζ * X ω ζ δ) * R δ β := by
    funext ω
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun δ _ => by rw [Matrix.mul_apply]
  rw [hrw]
  exact Finset.measurable_sum _ fun δ _ =>
    (Finset.measurable_sum _ fun ζ _ => (hX ζ δ).const_mul _).mul_const _

/-- The congruence bridge on an ALIGNED adapted cell, minus sign. -/
theorem h68_coarseBlockMatrix_respCoeffMinus_at [NeZero d] {q : Mat d} (hq : IsUnit q) (j : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)
      = blockCongr (respG F) (coarseBlock (adaptedCellAtCenter q j w) a) :=
  coarseBlockMatrix_sub_skew_eq_blockCongr (respg_isSkew F)
    (h68_hasQuadraticMu_adaptedCellAtCenter q hq j w a)

/-- Entrywise measurability of the recentred coarse block on an aligned cell, minus sign. -/
theorem h68_measurable_coarseBlockMatrix_minus [NeZero d] {q : Mat d} (hq : IsUnit q)
    (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (α β : BlockCoord d) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β := by
  have hrw : (fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffMinus F a)) α β)
      = fun a : CoeffSpace d =>
        ((toFullBlockMat (respG F))ᵀ * toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a) *
          toFullBlockMat (respG F)) α β := by
    funext a
    rw [h68_coarseBlockMatrix_respCoeffMinus_at hq j w F a, blockCongr,
      toFullBlockMat_ofFullBlockMat]
  rw [hrw]
  exact h68_measurable_mul_mul _ _ _ (fun ζ δ => h67_measurable_coarseBlock_entry hq j w ζ δ) α β

/-- **The measurability conjunct of the η-kernel (minus).** -/
theorem h68_aestronglyMeasurable_recentDefectBlock_minus [NeZero d] {q : Mat d} (hq : IsUnit q)
    (P : Measure (CoeffSpace d)) (t : ℤ) (n : ℕ) (w : Fin d → ℤ) (E F : BlockMat d) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      recentDefectBlock q t n w E (respCoeffMinus F a)) P := by
  refine Measurable.aestronglyMeasurable ?_
  refine measurable_pi_lambda _ fun α => measurable_pi_lambda _ fun β => ?_
  have hcell : HighContrast.adaptedCell q t = adaptedCellAtCenter q t 0 := (b130_adaptedCellAtCenter_zero q t).symm
  have hrw : (fun a : CoeffSpace d => recentDefectBlock q t n w E (respCoeffMinus F a) α β)
      = fun a : CoeffSpace d =>
        (matSqrt ((toFullBlockMat E)⁻¹) *
          (fun a' : CoeffSpace d =>
            toFullBlockMat (blockSub
              (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) (respCoeffMinus F a'))
              (coarseBlockMatrix (adaptedCellAtCenter q t 0) (respCoeffMinus F a')))) a *
          matSqrt ((toFullBlockMat E)⁻¹)) α β := by
    funext a
    rw [recentDefectBlock, normalizedBlock, toFullBlockMat_ofFullBlockMat, hcell]
  rw [hrw]
  refine h68_measurable_mul_mul _ _ _ (fun ζ δ => ?_) α β
  simp only [h67_toFullBlockMat_blockSub]
  exact (h68_measurable_coarseBlockMatrix_minus hq (t - (n : ℤ)) w F ζ δ).sub
    (h68_measurable_coarseBlockMatrix_minus hq t 0 F ζ δ)

/-- `G_+ = (shear by g) ∘ D`, the adjoint congruence of the plus recentring. -/
def h68_respGPlus (F : BlockMat d) : BlockMat d :=
  ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d))

/-- The congruence bridge on an ALIGNED adapted cell, plus sign. -/
theorem h68_coarseBlockMatrix_respCoeffPlus_at [NeZero d] {q : Mat d} (hq : IsUnit q) (j : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)
      = blockCongr (h68_respGPlus F) (coarseBlock (adaptedCellAtCenter q j w) a) := by
  have hgnskew : matTranspose (-(respg F)) = -(-(respg F)) := by
    have hT : matTranspose (-(respg F)) = -matTranspose (respg F) := by
      simp only [matTranspose, Matrix.transpose_neg]
    rw [hT, respg_isSkew F]
  have h1 : respCoeffPlus F a
      = fun y => (adjointCoeffField (⇑a.1 : CoeffField d)) y - (-(respg F)) := by
    funext y
    simp only [respCoeffPlus, adjointCoeffField, sub_neg_eq_add]
  have h2 := coarseBlockMatrix_sub_skew_eq_blockCongr (U := adaptedCellAtCenter q j w)
    (a := adjointCoeffField (⇑a.1 : CoeffField d)) hgnskew
    (hasQuadraticMu_adjointCoeffField (h68_hasQuadraticMu_adaptedCellAtCenter q hq j w a))
  have h3 : coarseBlockMatrix (adaptedCellAtCenter q j w) (adjointCoeffField (⇑a.1 : CoeffField d))
      = blockCongr (blockD d) (coarseBlock (adaptedCellAtCenter q j w) a) := by
    rw [coarseBlockMatrix_adjointCoeffField_of_exists
      (exists_coarseBlockMatrix_of_hasQuadraticMu
        (h68_hasQuadraticMu_adaptedCellAtCenter q hq j w a)), ← blockCongr_blockD]
    rfl
  rw [h1, h2, h3, blockCongr_blockCongr, h68_respGPlus]
  exact congrArg (fun M => blockCongr M (coarseBlock (adaptedCellAtCenter q j w) a))
    (congrArg ofFullBlockMat (blockD_mul_shear_neg (respg F)))

/-- Entrywise measurability of the recentred coarse block on an aligned cell, plus sign. -/
theorem h68_measurable_coarseBlockMatrix_plus [NeZero d] {q : Mat d} (hq : IsUnit q)
    (j : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (α β : BlockCoord d) :
    Measurable fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β := by
  have hrw : (fun a : CoeffSpace d =>
      toFullBlockMat (coarseBlockMatrix (adaptedCellAtCenter q j w) (respCoeffPlus F a)) α β)
      = fun a : CoeffSpace d =>
        ((toFullBlockMat (h68_respGPlus F))ᵀ *
          toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a) *
          toFullBlockMat (h68_respGPlus F)) α β := by
    funext a
    rw [h68_coarseBlockMatrix_respCoeffPlus_at hq j w F a, blockCongr,
      toFullBlockMat_ofFullBlockMat]
  rw [hrw]
  exact h68_measurable_mul_mul _ _ _ (fun ζ δ => h67_measurable_coarseBlock_entry hq j w ζ δ) α β

/-- **The measurability conjunct of the η-kernel (plus).** -/
theorem h68_aestronglyMeasurable_recentDefectBlock_plus [NeZero d] {q : Mat d} (hq : IsUnit q)
    (P : Measure (CoeffSpace d)) (t : ℤ) (n : ℕ) (w : Fin d → ℤ) (E F : BlockMat d) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      recentDefectBlock q t n w E (respCoeffPlus F a)) P := by
  refine Measurable.aestronglyMeasurable ?_
  refine measurable_pi_lambda _ fun α => measurable_pi_lambda _ fun β => ?_
  have hcell : HighContrast.adaptedCell q t = adaptedCellAtCenter q t 0 := (b130_adaptedCellAtCenter_zero q t).symm
  have hrw : (fun a : CoeffSpace d => recentDefectBlock q t n w E (respCoeffPlus F a) α β)
      = fun a : CoeffSpace d =>
        (matSqrt ((toFullBlockMat E)⁻¹) *
          (fun a' : CoeffSpace d =>
            toFullBlockMat (blockSub
              (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) (respCoeffPlus F a'))
              (coarseBlockMatrix (adaptedCellAtCenter q t 0) (respCoeffPlus F a')))) a *
          matSqrt ((toFullBlockMat E)⁻¹)) α β := by
    funext a
    rw [recentDefectBlock, normalizedBlock, toFullBlockMat_ofFullBlockMat, hcell]
  rw [hrw]
  refine h68_measurable_mul_mul _ _ _ (fun ζ δ => ?_) α β
  simp only [h67_toFullBlockMat_blockSub]
  exact (h68_measurable_coarseBlockMatrix_plus hq (t - (n : ℤ)) w F ζ δ).sub
    (h68_measurable_coarseBlockMatrix_plus hq t 0 F ζ δ)

/-! ### The two-sided carrier

The ONE-SIDED hypothesis `∫ respAllScaleMax ^ Q ∂P ≤ Cm * η` cannot imply the η-kernel's conclusion
`∫ ‖D_{n,w}‖ ^ 2 ≤ K n * η ^ (2/Q)` for ANY constant sequence `K`.  The conclusion is unchanged,
and the hypothesis carrier is replaced by its two-sided twin `respAllScaleAbs`
(`AdaptedDefs.lean`), which is `respAllScaleMax` with `blockSpecBound` (the spectral positive
part) replaced by `blockOpNorm`; the premise's route already runs through the TWO-SIDED
`blockOpNorm (normalizedFluctuation …)`.

The lemmas below are the comparison layer that keeps every EXISTING `respAllScaleMax` consumer
(`b130_coarseBlock_le_one_add_respAllScaleMax` among them) available under the new hypothesis:
`respAllScaleMax ≤ respAllScaleAbs` pointwise. -/

/-- `v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ (v ⬝ᵥ v)` for an ARBITRARY square matrix -- no positivity. -/
private theorem b179_dot_mulVec_le_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℝ) (v : n → ℝ) : v ⬝ᵥ (N *ᵥ v) ≤ ‖N‖ * (v ⬝ᵥ v) := by
  have hsq := vecSq_mulVec_le N v
  have hvv : (0 : ℝ) ≤ v ⬝ᵥ v := b130_dotProduct_self_nonneg v
  rcases eq_or_lt_of_le (norm_nonneg N) with h0 | hpos
  · have hN : N = 0 := norm_eq_zero.mp h0.symm
    subst hN
    simp
  · have hexp : (0 : ℝ) ≤ (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) :=
      b130_dotProduct_self_nonneg _
    have hexpand : (‖N‖ • v - N *ᵥ v) ⬝ᵥ (‖N‖ • v - N *ᵥ v) =
        ‖N‖ * ‖N‖ * (v ⬝ᵥ v) - 2 * ‖N‖ * (v ⬝ᵥ (N *ᵥ v)) + (N *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, dotProduct_comm (N *ᵥ v) v]
      ring
    rw [hexpand] at hexp
    nlinarith [hexp, hsq, hpos]

/-- The Loewner envelope of an ARBITRARY doubled block by its operator norm.  This is the step
that does NOT need positive semidefiniteness, and it is what makes `blockSpecBound ≤ blockOpNorm`
unconditional. -/
private theorem b179_loewner_le_blockOpNorm (N : BlockMat d) :
    BlockMatLoewnerLE N (blockScale (blockOpNorm N) (Book.Ch02.blockIdentity d)) := by
  intro X
  have h := b179_dot_mulVec_le_opNorm (toFullBlockMat N) (toFullBlockVec X)
  have hL : blockVecDot X (blockMatVecMul N X) =
      toFullBlockVec X ⬝ᵥ (toFullBlockMat N *ᵥ toFullBlockVec X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  have hB : blockOpNorm N = ‖toFullBlockMat N‖ := rfl
  rw [hL, b130_qform_blockScale, b130_qform_identity, hB]
  linarith only [h]

/-- `‖I‖ ≤ 1` for the doubled identity in the `L²` operator norm (the `d = 0` case is the
zero space, where the norm is `0`). -/
private theorem b179_norm_one_le : ‖(1 : FullBlockMat d)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty (BlockCoord d) with hi | hi
  · let := hi
    have he : (1 : FullBlockMat d) = 0 := Subsingleton.elim _ _
    rw [he, norm_zero]; norm_num
  · exact le_of_eq CStarRing.norm_one

/-- `toFullBlockMat` of the doubled identity. -/
private theorem b179_toFullBlockMat_blockIdentity :
    toFullBlockMat (Book.Ch02.blockIdentity d) = (1 : FullBlockMat d) := by
  ext (i | i) (j | j) <;>
    simp [toFullBlockMat, Book.Ch02.blockIdentity, Book.Ch02.blockDiag, Matrix.one_apply]

/-- The defining set of `blockSpecBound` is bounded below by `0`. -/
private theorem b179_blockSpecBound_le (N : BlockMat d) (c : ℝ) (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    blockSpecBound N ≤ c := by
  refine csInf_le ⟨0, ?_⟩ ⟨hc, h⟩
  rintro y ⟨hy0, -⟩
  exact hy0

/-- **The comparison, termwise, UNCONDITIONAL.**  `blockSpecBound N ≤ blockOpNorm N` for
every doubled block: `blockSpecBound N = sInf {c ≥ 0 | N ≼ c I}` and `‖N‖` is a member of that
set by `b179_loewner_le_blockOpNorm`.  This is the inequality that makes `respAllScaleAbs`
(`AdaptedDefs.lean`) a genuine strengthening of `respAllScaleMax`, so every existing
`respAllScaleMax` consumer -- in particular
`b130_coarseBlock_le_one_add_respAllScaleMax` -- remains available. -/
theorem h68_blockSpecBound_le_blockOpNorm (N : BlockMat d) :
    blockSpecBound N ≤ blockOpNorm N :=
  b179_blockSpecBound_le N _ (by rw [blockOpNorm]; exact norm_nonneg _)
    (b179_loewner_le_blockOpNorm N)

/-- A normalized block of a positive semidefinite block is positive semidefinite. -/
theorem h68_normalizedBlock_posSemidef {A R : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (hR : (toFullBlockMat R).PosDef) :
    (toFullBlockMat (normalizedBlock A R)).PosSemidef := by
  have hs : (matSqrt (toFullBlockMat R)⁻¹).IsHermitian :=
    (Multiscale.matSqrt_inv_posDef_full hR).isHermitian
  have hp := hA.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat R)⁻¹)
  rw [hs.eq] at hp
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  exact hp

/-- `0 ≤ blockSpecBound Hb`: every member of the defining set is nonnegative, and `Real.sInf`
of the empty set is `0`. -/
theorem b179_blockSpecBound_nonneg (Hb : BlockMat d) : 0 ≤ blockSpecBound Hb := by
  rw [blockSpecBound]
  exact Real.sInf_nonneg fun c hc => hc.1

/-- A Loewner bound against `c I` is a bound on the full quadratic form at EVERY vector, not
merely at the vectors of the form `toFullBlockVec X`: `toFullBlockVec` is a bijection
(`toFullBlockVec_ofFullBlockVec`). -/
private theorem b179_dot_le_of_loewner_le_scale_identity {N : BlockMat d} {c : ℝ}
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d)))
    (v : FullBlockVec d) : v ⬝ᵥ (toFullBlockMat N *ᵥ v) ≤ c * (v ⬝ᵥ v) := by
  have hX := h (ofFullBlockVec v)
  rw [b130_qform_blockScale, b130_qform_identity] at hX
  have hL : blockVecDot (ofFullBlockVec v) (blockMatVecMul N (ofFullBlockVec v)) =
      toFullBlockVec (ofFullBlockVec v) ⬝ᵥ
        (toFullBlockMat N *ᵥ toFullBlockVec (ofFullBlockVec v)) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  rw [hL, toFullBlockVec_ofFullBlockVec] at hX
  linarith only [hX]

/-- On a positive semidefinite block a Loewner bound `N ≼ c I` bounds the operator norm.
This is the converse of `b179_loewner_le_blockOpNorm`, and it is the ONLY place where
positive semidefiniteness is genuinely needed. -/
private theorem b179_blockOpNorm_le_of_loewner {N : BlockMat d}
    (hN : (toFullBlockMat N).PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (h : BlockMatLoewnerLE N (blockScale c (Book.Ch02.blockIdentity d))) :
    blockOpNorm N ≤ c :=
  opNorm_le_of_psd_dot_le hN hc (b179_dot_le_of_loewner_le_scale_identity h)

/-- **The reverse comparison on a PSD block**: the two-sided operator norm of `N - I` exceeds
its spectral positive part by at most `2`.  `N ≼ (1 + s) I` with `s = blockSpecBound (N - I)`
by `b130_le_one_add_specBound`, hence `‖N‖ ≤ 1 + s` by `b179_blockOpNorm_le_of_loewner`, hence
`‖N - I‖ ≤ ‖N‖ + ‖I‖ ≤ s + 2`.

This is what turns the EXISTING one-sided envelope `b130_pathwise_envelope` into an envelope
for the two-sided carrier `respAllScaleAbs`, i.e. it discharges the `BddAbove` side condition
of `h68_respAllScaleMax_le_respAllScaleAbs` and of the `le_csSup` step the η-kernel needs. -/
theorem h68_blockOpNorm_sub_id_le_specBound_add_two (N : BlockMat d)
    (hN : (toFullBlockMat N).PosSemidef) :
    blockOpNorm (blockSub N (Book.Ch02.blockIdentity d))
      ≤ blockSpecBound (blockSub N (Book.Ch02.blockIdentity d)) + 2 := by
  set s : ℝ := blockSpecBound (blockSub N (Book.Ch02.blockIdentity d)) with hs
  have hs0 : 0 ≤ s := b179_blockSpecBound_nonneg _
  have hNle : blockOpNorm N ≤ 1 + s := by
    refine b179_blockOpNorm_le_of_loewner hN (by linarith) ?_
    exact b130_le_one_add_specBound N
      (blockOpNorm (blockSub N (Book.Ch02.blockIdentity d))) s
      (by rw [blockOpNorm]; exact norm_nonneg _)
      (b179_loewner_le_blockOpNorm _) le_rfl
  have hsub : toFullBlockMat (blockSub N (Book.Ch02.blockIdentity d)) =
      toFullBlockMat N - (1 : FullBlockMat d) := by
    rw [b130_toFullBlockMat_blockSub, b179_toFullBlockMat_blockIdentity]
  have htri : ‖toFullBlockMat N - (1 : FullBlockMat d)‖ ≤
      ‖toFullBlockMat N‖ + ‖(1 : FullBlockMat d)‖ := norm_sub_le _ _
  have h1 := b179_norm_one_le (d := d)
  have hB : blockOpNorm N = ‖toFullBlockMat N‖ := rfl
  rw [blockOpNorm, hsub]
  rw [hB] at hNle
  linarith

/-- **`respAllScaleMax ≤ respAllScaleAbs` pointwise.**

One side condition, genuine:

* `hbdd` -- `BddAbove` of the defining set of `respAllScaleAbs`.  `Real.sSup` takes the junk
  value `0` on an unbounded set, so WITHOUT this the inequality is false; the existing
  `respAllScaleMax` lemmas carry exactly the same side condition (`le_csSup hbdd` in
  `b130_coarseBlock_le_one_add_respAllScaleMax`, whose `hbdd` comes from
  `b130_pathwise_envelope`).  Stated, not assumed away. -/
theorem h68_respAllScaleMax_le_respAllScaleAbs (P : Measure (CoeffSpace d)) (γ : ℝ)
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockOpNorm (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    respAllScaleMax P γ jStar F t a ≤ respAllScaleAbs P γ jStar F t a := by
  rw [respAllScaleMax]
  refine Real.sSup_le ?_ ?_
  · rintro y ⟨n, z, hz, rfl⟩
    refine le_trans ?_ (le_csSup hbdd ⟨n, z, hz, rfl⟩)
    exact mul_le_mul_of_nonneg_left (h68_blockSpecBound_le_blockOpNorm _)
      (Real.rpow_nonneg (by norm_num) _)
  · rw [respAllScaleAbs]
    refine Real.sSup_nonneg ?_
    rintro y ⟨n, z, hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by rw [blockOpNorm]; exact norm_nonneg _)

/-- The coarse block of an ALIGNED adapted cell is positive semidefinite.  The `w`-general
form of `Annealed.coarseBlock_adaptedCell_posSemidef` (`ParentChildBlocks.lean`, stated only
for `w = 0`); `adaptedCellAtCenter q j w` is by definition `adaptedCellTranslate q j
(adaptedCellCenter q j w)` (`HCPoly/Entry/Setup/AdaptedGrid.lean`), which is exactly what
`Annealed.blockPosDef_coarseBlock_adapted` (`AdaptedDomainRecovery.lean`) takes. -/
theorem h68_coarseBlock_adaptedCellAtCenter_posSemidef [NeZero d] (q : Mat d) (hq : IsUnit q)
    (j : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) :
    (toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a)).PosSemidef := by
  have hsymm : IsSymmetricBlockMat (coarseBlock (adaptedCellAtCenter q j w) a) :=
    isSymmetricBlockMat_coarseBlockMatrix (adaptedCellAtCenter q j w) (⇑a.1)
  have hpos : Book.Ch02.BlockPosDef (coarseBlock (adaptedCellAtCenter q j w) a) :=
    Annealed.blockPosDef_coarseBlock_adapted q hq j (adaptedCellCenter q j w) a
  exact (Annealed.fullBlock_posDef_of_pos hsymm hpos).posSemidef

/-- `‖U‖ ≤ 1` for a matrix with `Uᵀ U = 1`, through the C⋆-identity `‖UᵀU‖ = ‖U‖²`
(`CStarRing.norm_star_mul_self`, `star = ᵀ` over `ℝ`), as in
`HCPoly/Entry/Annealed/RecurrenceTransport.lean`. -/
private theorem b179_norm_le_one_of_transpose_mul_self
    (U : FullBlockMat d) (h : Uᵀ * U = 1) : ‖U‖ ≤ 1 := by
  have hsq : ‖Uᵀ * U‖ = ‖U‖ * ‖U‖ := by
    have hst := CStarRing.norm_star_mul_self (x := U)
    rwa [show (star U : FullBlockMat d) = Uᵀ from rfl] at hst
  rw [h] at hsq
  have h1 := b179_norm_one_le (d := d)
  nlinarith [hsq, h1, norm_nonneg U]

/-- **Congruence invariance of the normalized operator norm.**  Applying the SAME congruence
`blockCongr G` to a block AND to its normalizer leaves the normalized block orthogonally
similar, so its operator norm does not increase:

`U := matSqrt E * G * matSqrt (Gᵀ E G)⁻¹` satisfies `Uᵀ U = 1` and
`normalizedBlock (blockCongr G Z) (blockCongr G E) = Uᵀ · normalizedBlock Z E · U`.

This is the step that carries `h68_weighted_blockOpNorm_le_respAllScaleAbs` from the
`E_t`-picture of `respAllScaleAbs` to the `Ehat^∓`-picture of `recentDefect`: recall
`respEhatMinus = blockCongr (respG F) (respMean …)` (`AdaptedDefs.lean`) and that
`h68_coarseBlockMatrix_respCoeffMinus_at` puts the numerator in the matching `blockCongr`
form. -/
theorem h68_blockOpNorm_normalizedBlock_blockCongr_le (G Z E : BlockMat d)
    (hE : (toFullBlockMat E).PosDef)
    (hC : (toFullBlockMat (blockCongr G E)).PosDef) :
    blockOpNorm (normalizedBlock (blockCongr G Z) (blockCongr G E))
      ≤ blockOpNorm (normalizedBlock Z E) := by
  set Ef : FullBlockMat d := toFullBlockMat E with hEf
  set Gf : FullBlockMat d := toFullBlockMat G with hGf
  set Zf : FullBlockMat d := toFullBlockMat Z with hZf
  set Cf : FullBlockMat d := toFullBlockMat (blockCongr G E) with hCfd
  have hCeq : Cf = Gfᵀ * Ef * Gf := by
    rw [hCfd, blockCongr, toFullBlockMat_ofFullBlockMat]
  set S : FullBlockMat d := matSqrt Cf⁻¹ with hSd
  set T : FullBlockMat d := matSqrt Ef⁻¹ with hTd
  set R : FullBlockMat d := matSqrt Ef with hRd
  set U : FullBlockMat d := R * Gf * S with hUd
  have hSsym : Sᵀ = S := transpose_eq_of_psd (matSqrt_inv_posDef_full hC).posSemidef
  have hRsym : Rᵀ = R := transpose_eq_of_psd (matSqrt_spec hE.posSemidef).1
  have hRR : R * R = Ef := (matSqrt_spec hE.posSemidef).2
  have hRT : R * T = 1 := Annealed.matSqrt_mul_matSqrt_inv_full hE
  have hTR : T * R = 1 := Annealed.matSqrt_inv_mul_matSqrt_full hE
  have hUU : Uᵀ * U = 1 := by
    rw [hUd, Matrix.transpose_mul, Matrix.transpose_mul, hSsym, hRsym]
    calc S * (Gfᵀ * R) * (R * Gf * S) = S * (Gfᵀ * (R * R) * Gf) * S := by noncomm_ring
      _ = S * Cf * S := by rw [hRR, ← hCeq]
      _ = 1 := matSqrt_inv_mul_self_mul_matSqrt_inv_full hC
  have hUUt : U * Uᵀ = 1 := _root_.mul_eq_one_comm.mp hUU
  have hUn : ‖U‖ ≤ 1 := b179_norm_le_one_of_transpose_mul_self U hUU
  have hUtn : ‖Uᵀ‖ ≤ 1 := by
    refine b179_norm_le_one_of_transpose_mul_self Uᵀ ?_
    rw [Matrix.transpose_transpose]
    exact hUUt
  have hlhs : toFullBlockMat (normalizedBlock (blockCongr G Z) (blockCongr G E)) =
      S * (Gfᵀ * Zf * Gf) * S := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, ← hCfd, ← hSd, blockCongr,
      toFullBlockMat_ofFullBlockMat]
  have hrhs : toFullBlockMat (normalizedBlock Z E) = T * Zf * T := by
    rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, ← hEf, ← hTd]
  have hsim : Uᵀ * (T * Zf * T) * U = S * (Gfᵀ * Zf * Gf) * S := by
    rw [hUd, Matrix.transpose_mul, Matrix.transpose_mul, hSsym, hRsym]
    calc S * (Gfᵀ * R) * (T * Zf * T) * (R * Gf * S)
        = S * Gfᵀ * (R * T) * Zf * (T * R) * Gf * S := by noncomm_ring
      _ = S * (Gfᵀ * Zf * Gf) * S := by
            rw [hRT, hTR]; noncomm_ring
  rw [blockOpNorm, blockOpNorm, hlhs, hrhs, ← hsim]
  have hb1 : ‖Uᵀ * (T * Zf * T) * U‖ ≤ ‖Uᵀ * (T * Zf * T)‖ * ‖U‖ := norm_mul_le _ _
  have hb2 : ‖Uᵀ * (T * Zf * T)‖ ≤ ‖Uᵀ‖ * ‖T * Zf * T‖ := norm_mul_le _ _
  have hM0 : (0 : ℝ) ≤ ‖T * Zf * T‖ := norm_nonneg _
  have hU0 : (0 : ℝ) ≤ ‖U‖ := norm_nonneg _
  have hUt0 : (0 : ℝ) ≤ ‖Uᵀ‖ := norm_nonneg _
  have hP0 : (0 : ℝ) ≤ ‖Uᵀ * (T * Zf * T)‖ := norm_nonneg _
  nlinarith [hb1, hb2, hUn, hUtn, hM0, hU0, hUt0, hP0]

/-- **The `respAllScaleAbs` envelope.**  The two-sided defining set is a.e. bounded above, by
`C + 2` where `C` is the constant of the ONE-SIDED `b130_pathwise_envelope`: the weights
`3 ^ (-(ρ n))` are at most `1`, and `h68_blockOpNorm_sub_id_le_specBound_add_two` costs `2`.

This is the `respAllScaleAbs` analogue of `b130_pathwise_envelope`, and it is
what lets `le_csSup` be applied to `respAllScaleAbs` -- so the junk value `0` of `Real.sSup` on
an unbounded set is excluded, exactly as for `respAllScaleMax`. -/
theorem b179_pathwise_envelope_abs (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockOpNorm (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} := by
  let : NeZero d := ⟨by omega⟩
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hm
  have hEt : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    Annealed.adaptedMean_posDef d hd P γ E Ψ Kg Src hstat hdag jStar hj (explicitCanonicalMetric F) hm t
  filter_upwards [b130_pathwise_envelope hd γ hγ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a ha
  obtain ⟨C, hC0, -, hterms⟩ := ha
  refine ⟨C + 2, ?_⟩
  rintro y ⟨n, z, hz, rfl⟩
  have hw1 : (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hρ : 0 ≤ respRho γ := by rw [respRho]; linarith [hγ.1, hγ.2]
    nlinarith [hn0, hρ]
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hpsd := h68_normalizedBlock_posSemidef
    (h68_coarseBlock_adaptedCellAtCenter_posSemidef (respGrid jStar F) hq (t - (n : ℤ)) z a) hEt
  have hkey := h68_blockOpNorm_sub_id_le_specBound_add_two _ hpsd
  have hspec := hterms n z hz
  have hs0 : (0 : ℝ) ≤ blockSpecBound (blockSub
      (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
        (respMean P jStar F t)) (Book.Ch02.blockIdentity d)) :=
    b179_blockSpecBound_nonneg _
  nlinarith [hkey, hspec, hw0, hw1, hs0]

/-- **The `le_csSup` step for the two-sided carrier.**  Every weighted term of the defining set
of `respAllScaleAbs` is at most `respAllScaleAbs` itself, a.e.  This is the pathwise input the
η-kernel needs on BOTH sides, and the exact analogue of the `le_csSup hbdd hmem` step of
`b130_coarseBlock_le_one_add_respAllScaleMax`. -/
theorem h68_weighted_blockOpNorm_le_respAllScaleAbs (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) :
    ∀ᵐ a ∂P, ∀ (n : ℕ), ∀ z ∈ triadicIndexBox d n,
      (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockOpNorm (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))
        ≤ respAllScaleAbs P γ jStar F t a := by
  filter_upwards [b179_pathwise_envelope_abs hd γ hγ P E Ψ Kg Src hstat hdag jStar hj F hm t]
    with a hbdd
  intro n z hz
  exact le_csSup hbdd ⟨n, z, hz, rfl⟩

end

end Homogenization.HighContrast.Multiscale
