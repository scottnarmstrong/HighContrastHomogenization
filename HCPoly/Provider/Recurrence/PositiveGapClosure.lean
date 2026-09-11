/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.MeanOrder
import HCPoly.Provider.Recurrence.PositiveGapIntegration

/-!
# The positive-gap estimate read at the carriers of the fixed-grid recurrence

`l.fixed.geometry.positive.gap` is proved for abstract random blocks: a positive excess `D`
caught below `Ĝ = P + Y`, a bound `b` on the mean of `tr D`, and the mixed norms
`x = ‖D‖_{L^Q(S_Q)}`, `y = ‖Y‖_{L^Q(S_Q)}`.  Three passages carry it onto the
data of `p.fixed.geometry.parent.child.recurrence`, and they are taken here.

*The expectation identities.*  With `F̂` the response over the parent cell and
`Ĝ` the average of the responses over its aligned children, both normalized by
the parent mean `E_p^q`, the reference proof records `E[D] = B` and
`E[tr D] = b` for `D = Ĝ - F̂` and `B = P_{j,p}^q - I`.  Both are the
interchange of a fixed linear functional with the block-valued Bochner integral:
normalization is a two-sided multiplication by a deterministic matrix and the
trace is a linear functional, so each passes through.  The mean of the
normalized parent response is the identity and the mean of the normalized
average is the relative mean, so `E[D] = P_{j,p}^q - I`.  Since `D` is positive
along every realization, the `L^1` norm of `tr D` is its mean, which is the
fail-closed form the integrated trace-power display takes as its gap hypothesis.

*The finiteness read-back.*  The integrated display is an inequality in
`ℝ≥0∞`.  On the event that the two mixed norms are finite it becomes the
printed quadratic inequality between real numbers, and the two constants it
carries are reconciled into the single constant `C = 2^{Q-2}(2m)^{1-1/Q}` the
absorption step takes, at the cost of `(2m)^{1-1/Q} ≥ 1`.

*The mixed-norm triangle step.*  The closing estimate of `l.fixed.geometry.positive.gap` is
pointwise; the conclusion is between mixed norms.  Passing between them costs
the `L^Q` norm of a constant, which is that constant exactly because the law is
a probability measure — the one place in the chain where the normalization of
the law is genuinely used.
-/

namespace Homogenization
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Flattening the block difference and the normalized difference -/

/-- The flattening of a difference of doubled blocks is the difference of the
flattenings. -/
theorem toFullBlockMat_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  rw [Matrix.sub_apply, toFullBlockMat_blockSub_apply]

/-- The flattening of the `F`-normalized difference, expanded as the difference
of the two congruences. -/
theorem toFullBlockMat_normalizedBlock_blockSub (X Y F : BlockMat d) :
    toFullBlockMat (normalizedBlock (blockSub X Y) F) =
      matSqrt (toFullBlockMat F)⁻¹ * toFullBlockMat X * matSqrt (toFullBlockMat F)⁻¹ -
        matSqrt (toFullBlockMat F)⁻¹ * toFullBlockMat Y * matSqrt (toFullBlockMat F)⁻¹ := by
  rw [toFullBlockMat_normalizedBlock, toFullBlockMat_blockSub, Matrix.mul_sub, Matrix.sub_mul]

/-! ## The trace against the block-valued integral -/

/-- **The trace passes through the block-valued Bochner integral**, being a
linear functional on a finite-dimensional space. -/
theorem integral_blockTrace {P : Measure (CoeffSpace d)} {D : CoeffSpace d → BlockMat d}
    (hint : Integrable (fun a => toFullBlockMat (D a)) P) :
    ∫ a, blockTrace (D a) ∂P = Matrix.trace (∫ a, toFullBlockMat (D a) ∂P) := by
  show ∫ a, Matrix.trace (toFullBlockMat (D a)) ∂P =
    Matrix.trace (∫ a, toFullBlockMat (D a) ∂P)
  exact (LinearMap.toContinuousLinearMap
    (Matrix.traceLinearMap (BlockCoord d) ℝ ℝ)).integral_comp_comm hint

/-- The trace of an integrable block-valued map is integrable. -/
theorem integrable_blockTrace {P : Measure (CoeffSpace d)} {D : CoeffSpace d → BlockMat d}
    (hint : Integrable (fun a => toFullBlockMat (D a)) P) :
    Integrable (fun a => blockTrace (D a)) P :=
  (LinearMap.toContinuousLinearMap
    (Matrix.traceLinearMap (BlockCoord d) ℝ ℝ)).integrable_comp hint

/-- **`E[tr D] = b`, fail-closed.**  For a block that is positive along every
realization the `L^1` norm of its trace is the mean of that trace, with no
finiteness hedge: the trace is already nonnegative, so no absolute value is
lost.  This is the form the gap hypothesis of the integrated trace-power display
is stated in. -/
theorem eLpNorm_blockTrace_eq_ofReal {P : Measure (CoeffSpace d)}
    {D : CoeffSpace d → BlockMat d} {c : ℝ}
    (hpos : ∀ a, (toFullBlockMat (D a)).PosSemidef)
    (hint : Integrable (fun a => toFullBlockMat (D a)) P)
    (hmean : ∫ a, blockTrace (D a) ∂P = c) :
    eLpNorm (fun a => blockTrace (D a)) 1 P = ENNReal.ofReal c := by
  have hnorm : ∫ a, ‖blockTrace (D a)‖ ∂P = c := by
    rw [← hmean]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a =>
      Real.norm_of_nonneg (hpos a).trace_nonneg)
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (integrable_blockTrace hint), hnorm]

/-! ## The expectation identities at the adapted means -/

/-- The normalized excess is Bochner integrable as soon as the two responses
are. -/
theorem integrable_toFullBlockMat_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {q : Mat d} {p : ℤ} (hintp : HasFiniteAdaptedMean P q p)
    {Gh : CoeffSpace d → BlockMat d} (hGint : Integrable (fun a => toFullBlockMat (Gh a)) P) :
    Integrable (fun a => toFullBlockMat (normalizedBlock
      (blockSub (Gh a) (coarseBlock (adaptedCell q p) a)) (adaptedMean P q p))) P := by
  simp only [toFullBlockMat_normalizedBlock_blockSub]
  exact (integrable_mul_left_mul_right _ _ hGint).sub
    (integrable_mul_left_mul_right _ _ (integrable_toFullBlockMat hintp))

/-- **`0 ≤ D`.**  The excess of the aligned average over the response is
positive along every realization, congruence by the inverse square root of the
parent mean preserving the pathwise order. -/
theorem posSemidef_toFullBlockMat_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {q : Mat d} {p : ℤ} (hEp : (toFullBlockMat (adaptedMean P q p)).PosDef)
    {Gh : CoeffSpace d → BlockMat d}
    (hGle : ∀ a, toFullBlockMat (coarseBlock (adaptedCell q p) a) ≤ toFullBlockMat (Gh a))
    (a : CoeffSpace d) :
    (toFullBlockMat (normalizedBlock (blockSub (Gh a) (coarseBlock (adaptedCell q p) a))
      (adaptedMean P q p))).PosSemidef := by
  have hS : (matSqrt (toFullBlockMat (adaptedMean P q p))⁻¹)ᴴ =
      matSqrt (toFullBlockMat (adaptedMean P q p))⁻¹ :=
    (matSqrt_spec hEp.inv.posSemidef).1.isHermitian
  have hdiff := (Matrix.le_iff.mp (hGle a)).mul_mul_conjTranspose_same
    (matSqrt (toFullBlockMat (adaptedMean P q p))⁻¹)
  rw [hS, Matrix.mul_sub, Matrix.sub_mul] at hdiff
  rwa [toFullBlockMat_normalizedBlock_blockSub]

/-- **`E[D] = B`** (`l.fixed.geometry.positive.gap`, at the carriers of
`p.fixed.geometry.parent.child.recurrence`): the mean of the normalized excess of the aligned
average over the parent response is `P_{j,p}^q - I`.  The parent response
integrates to the parent mean, whose normalization by its own inverse square
root is the identity, and the aligned average integrates to the child mean,
whose normalization is the relative mean. -/
theorem integral_toFullBlockMat_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {q : Mat d} {j p : ℤ} (hintp : HasFiniteAdaptedMean P q p)
    (hEp : (toFullBlockMat (adaptedMean P q p)).PosDef) {Gh : CoeffSpace d → BlockMat d}
    (hGint : Integrable (fun a => toFullBlockMat (Gh a)) P)
    (hGmean : ∫ a, toFullBlockMat (Gh a) ∂P = toFullBlockMat (adaptedMean P q j)) :
    ∫ a, toFullBlockMat (normalizedBlock (blockSub (Gh a) (coarseBlock (adaptedCell q p) a))
        (adaptedMean P q p)) ∂P =
      toFullBlockMat (relMean P q j p) - 1 := by
  set S : FullBlockMat d := matSqrt (toFullBlockMat (adaptedMean P q p))⁻¹
  have hAint : Integrable (fun a => toFullBlockMat (coarseBlock (adaptedCell q p) a)) P :=
    integrable_toFullBlockMat hintp
  simp only [toFullBlockMat_normalizedBlock_blockSub]
  rw [integral_sub (integrable_mul_left_mul_right S S hGint)
      (integrable_mul_left_mul_right S S hAint),
    integral_mul_left_mul_right S S hGint, integral_mul_left_mul_right S S hAint,
    hGmean, ← toFullBlockMat_adaptedMean_eq_integral hintp, toFullBlockMat_relMean,
    matSqrt_inv_conj hEp]

/-- **`E[tr D] = b`** (`l.fixed.geometry.positive.gap`, at the carriers of
`p.fixed.geometry.parent.child.recurrence`): the mean of the trace of the normalized excess
is the trace gap `tr(P_{j,p}^q - I)` of the relative mean. -/
theorem integral_blockTrace_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {q : Mat d} {j p : ℤ} (hintp : HasFiniteAdaptedMean P q p)
    (hEp : (toFullBlockMat (adaptedMean P q p)).PosDef) {Gh : CoeffSpace d → BlockMat d}
    (hGint : Integrable (fun a => toFullBlockMat (Gh a)) P)
    (hGmean : ∫ a, toFullBlockMat (Gh a) ∂P = toFullBlockMat (adaptedMean P q j)) :
    ∫ a, blockTrace (normalizedBlock (blockSub (Gh a) (coarseBlock (adaptedCell q p) a))
        (adaptedMean P q p)) ∂P =
      blockTrace (relMean P q j p) - 2 * (d : ℝ) := by
  have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp [Fintype.card_sum, two_mul]
  rw [integral_blockTrace (integrable_toFullBlockMat_normalizedBlock_blockSub hintp hGint),
    integral_toFullBlockMat_normalizedBlock_blockSub hintp hEp hGint hGmean, Matrix.trace_sub,
    Matrix.trace_one, hcard]
  rfl

/-- **The gap hypothesis of the integrated trace-power display, at the adapted
means.**  The `L^1` norm of the trace of the normalized excess is the trace gap
of the relative mean, so any bound on that gap is a bound in the fail-closed
form the display consumes. -/
theorem eLpNorm_blockTrace_normalizedBlock_blockSub_le {P : Measure (CoeffSpace d)}
    {q : Mat d} {j p : ℤ} {b : ℝ} (hintp : HasFiniteAdaptedMean P q p)
    (hEp : (toFullBlockMat (adaptedMean P q p)).PosDef) {Gh : CoeffSpace d → BlockMat d}
    (hGint : Integrable (fun a => toFullBlockMat (Gh a)) P)
    (hGmean : ∫ a, toFullBlockMat (Gh a) ∂P = toFullBlockMat (adaptedMean P q j))
    (hGle : ∀ a, toFullBlockMat (coarseBlock (adaptedCell q p) a) ≤ toFullBlockMat (Gh a))
    (hb : blockTrace (relMean P q j p) - 2 * (d : ℝ) ≤ b) :
    eLpNorm (fun a => blockTrace (normalizedBlock
        (blockSub (Gh a) (coarseBlock (adaptedCell q p) a)) (adaptedMean P q p))) 1 P ≤
      ENNReal.ofReal b := by
  rw [eLpNorm_blockTrace_eq_ofReal
    (posSemidef_toFullBlockMat_normalizedBlock_blockSub hEp hGle)
    (integrable_toFullBlockMat_normalizedBlock_blockSub hintp hGint)
    (integral_blockTrace_normalizedBlock_blockSub hintp hEp hGint hGmean)]
  exact ENNReal.ofReal_le_ofReal hb

/-! ## The finiteness read-back of the quadratic display -/

/-- **The extended-real display, read back on finite mixed norms.**  A bound
`u^Q ≤ αb + β(y^{Q-1}x)` in `ℝ≥0∞` between the images of nonnegative reals is
that bound between the reals themselves, `ENNReal.ofReal` being an order
embedding on the nonnegative axis. -/
theorem rpow_le_add_mul_of_ofReal_le {Q α β b x y : ℝ} (hQ : 2 ≤ Q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ENNReal.ofReal x ^ Q ≤ ENNReal.ofReal (α * b) +
      ENNReal.ofReal β * (ENNReal.ofReal y ^ (Q - 1) * ENNReal.ofReal x)) :
    x ^ Q ≤ α * b + β * (y ^ (Q - 1) * x) := by
  have hrhs : (0 : ℝ) ≤ α * b + β * (y ^ (Q - 1) * x) :=
    add_nonneg (mul_nonneg hα hb) (mul_nonneg hβ (mul_nonneg (Real.rpow_nonneg hy _) hx))
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by linarith only [hQ] : (0 : ℝ) ≤ Q),
    ENNReal.ofReal_rpow_of_nonneg hy (by linarith only [hQ] : (0 : ℝ) ≤ Q - 1),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hy _), ← ENNReal.ofReal_mul hβ,
    ← ENNReal.ofReal_add (mul_nonneg hα hb)
      (mul_nonneg hβ (mul_nonneg (Real.rpow_nonneg hy _) hx))] at h
  exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp h

/-- The two constants of the quadratic display are reconciled into the single
constant the absorption step takes, at the cost of `(2m)^{1-1/Q} ≥ 1`. -/
private theorem rpow_le_mul_add_mul_of_le (hd : 0 < d) {Q p b x y : ℝ} (hQ : 2 ≤ Q) (hp : 0 ≤ p)
    (hb : 0 ≤ b)
    (h : x ^ Q ≤ (2 : ℝ) ^ (Q - 2) * p ^ (Q - 1) * b +
      (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) * (y ^ (Q - 1) * x)) :
    x ^ Q ≤ (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) * p ^ (Q - 1) * b +
      (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) * y ^ (Q - 1) * x := by
  have hd1 : (1 : ℝ) ≤ (2 * d : ℝ) := by
    have hcast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [hcast]
  have hfac : (1 : ℝ) ≤ (2 * d : ℝ) ^ (1 - Q⁻¹) :=
    Real.one_le_rpow hd1 (one_sub_inv_nonneg (by linarith only [hQ]))
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (Q - 2) := Real.rpow_nonneg (by norm_num) _
  have hkey : (0 : ℝ) ≤ (2 : ℝ) ^ (Q - 2) * (p ^ (Q - 1) * b) *
      ((2 * d : ℝ) ^ (1 - Q⁻¹) - 1) :=
    mul_nonneg (mul_nonneg h2 (mul_nonneg (Real.rpow_nonneg hp _) hb))
      (by linarith only [hfac])
  linarith only [h, hkey]

/-- **The input of the absorption step, from the two finiteness guards.**  The
integrated trace-power display, read back on finite mixed norms and with its two
constants reconciled, is exactly the quadratic inequality
`x^Q ≤ C|P|^{Q-1}b + Cy^{Q-1}x` that Young's inequality is applied to in
`l.fixed.geometry.positive.gap`, with `C = 2^{Q-2}(2m)^{1-1/Q}`. -/
theorem rpow_le_mul_add_mul_of_eLpNorm_eq (P : Measure (CoeffSpace d)) (hd : 0 < d) {Q : ℝ}
    (hQ : 2 ≤ Q) {D Gh Pm Y : CoeffSpace d → BlockMat d} {p b x y : ℝ} (hp : 0 ≤ p)
    (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hD : ∀ a, IsSymmetricBlockMat (D a)) (hDpos : ∀ a, (toFullBlockMat (D a)).PosSemidef)
    (hY : ∀ a, IsSymmetricBlockMat (Y a))
    (hsplit : ∀ a, toFullBlockMat (Gh a) = toFullBlockMat (Pm a) + toFullBlockMat (Y a))
    (hPm : ∀ a, toFullBlockMat (Pm a) ≤ p • (1 : FullBlockMat d))
    (hDG : ∀ a, toFullBlockMat (D a) ≤ toFullBlockMat (Gh a))
    (hmD : AEStronglyMeasurable (fun a => schattenNorm Q (D a)) P)
    (hmY : AEStronglyMeasurable (fun a => schattenNorm Q (Y a)) P)
    (hmT : AEStronglyMeasurable (fun a => blockTrace (D a)) P)
    (hgap : eLpNorm (fun a => blockTrace (D a)) 1 P ≤ ENNReal.ofReal b)
    (hxval : eLpNorm (fun a => schattenNorm Q (D a)) (ENNReal.ofReal Q) P = ENNReal.ofReal x)
    (hyval : eLpNorm (fun a => schattenNorm Q (Y a)) (ENNReal.ofReal Q) P = ENNReal.ofReal y) :
    x ^ Q ≤ (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) * p ^ (Q - 1) * b +
      (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) * y ^ (Q - 1) * x := by
  have hα : (0 : ℝ) ≤ (2 : ℝ) ^ (Q - 2) * p ^ (Q - 1) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hp _)
  have hβ : (0 : ℝ) ≤ (2 : ℝ) ^ (Q - 2) * (2 * d : ℝ) ^ (1 - Q⁻¹) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _)
  have hmain := eLpNorm_schattenNorm_rpow_le P hd hQ hp hD hDpos hY hsplit hPm hDG hmD hmY hmT hgap
  rw [hxval, hyval] at hmain
  exact rpow_le_mul_add_mul_of_le hd hQ hp hb
    (rpow_le_add_mul_of_ofReal_le hQ hα hβ hb hx hy hmain)

/-! ## The closing step in the mixed norm -/

/-- **The closing step of `l.fixed.geometry.positive.gap` in the mixed norm.**  The
pointwise estimate `|Ĥ|_{S_Q} ≤ (2m)^{1/Q}(|Y|_{S_Q} + |D|_{S_Q} + b)` passes to
the `L^Q(S_Q)` level by monotonicity and the triangle inequality of the norm.
The mean gap `b` is deterministic, and its `L^Q` norm is `b` itself exactly
because the law is a probability measure; that is the whole role of the
normalization here, and it is assumed rather than derived. -/
theorem eLpNorm_schattenNorm_le_mul_add (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    {Q : ℝ} (hQ : 1 ≤ Q) {H Y D : CoeffSpace d → BlockMat d} {B : BlockMat d}
    (hH : ∀ a, IsSymmetricBlockMat (H a)) (hY : ∀ a, IsSymmetricBlockMat (Y a))
    (hD : ∀ a, IsSymmetricBlockMat (D a)) (hB : IsSymmetricBlockMat B)
    (hBpos : (toFullBlockMat B).PosSemidef)
    (heq : ∀ a, toFullBlockMat (H a) =
      toFullBlockMat (Y a) - (toFullBlockMat (D a) - toFullBlockMat B))
    (hmY : AEStronglyMeasurable (fun a => schattenNorm Q (Y a)) P)
    (hmD : AEStronglyMeasurable (fun a => schattenNorm Q (D a)) P) :
    eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal ((2 * d : ℝ) ^ Q⁻¹) *
        (eLpNorm (fun a => schattenNorm Q (Y a)) (ENNReal.ofReal Q) P +
          eLpNorm (fun a => schattenNorm Q (D a)) (ENNReal.ofReal Q) P +
          ENNReal.ofReal (blockTrace B)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal Q := ENNReal.one_le_ofReal.mpr hQ
  have hfac : (0 : ℝ) ≤ (2 * d : ℝ) ^ Q⁻¹ := Real.rpow_nonneg (by positivity) _
  have hB0 : (0 : ℝ) ≤ blockTrace B := hBpos.trace_nonneg
  have hconst : eLpNorm (fun _ : CoeffSpace d => blockTrace B) (ENNReal.ofReal Q) P =
      ENNReal.ofReal (blockTrace B) := by
    rw [eLpNorm_const _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hp1))
        (IsProbabilityMeasure.ne_zero P),
      measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal hB0]
  have hmono : eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P ≤
      eLpNorm (fun a => (2 * d : ℝ) ^ Q⁻¹ *
        (schattenNorm Q (Y a) + schattenNorm Q (D a) + blockTrace B)) (ENNReal.ofReal Q) P := by
    refine eLpNorm_mono_real fun a => ?_
    rw [Real.norm_of_nonneg (zero_le_schattenNorm (hH a) Q)]
    exact schattenNorm_le_mul_add_blockTrace (hH a) (hY a) (hD a) hB hBpos hQ (heq a)
  have hsmul : eLpNorm (fun a => (2 * d : ℝ) ^ Q⁻¹ *
      (schattenNorm Q (Y a) + schattenNorm Q (D a) + blockTrace B)) (ENNReal.ofReal Q) P =
      ENNReal.ofReal ((2 * d : ℝ) ^ Q⁻¹) *
        eLpNorm (fun a => schattenNorm Q (Y a) + schattenNorm Q (D a) + blockTrace B)
          (ENNReal.ofReal Q) P := by
    have hfun : (fun a => (2 * d : ℝ) ^ Q⁻¹ *
        (schattenNorm Q (Y a) + schattenNorm Q (D a) + blockTrace B)) =
        (2 * d : ℝ) ^ Q⁻¹ •
          fun a => schattenNorm Q (Y a) + schattenNorm Q (D a) + blockTrace B := by
      funext a
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hfac]
  have hadd : eLpNorm (fun a => schattenNorm Q (Y a) + schattenNorm Q (D a) + blockTrace B)
      (ENNReal.ofReal Q) P ≤
      eLpNorm (fun a => schattenNorm Q (Y a)) (ENNReal.ofReal Q) P +
        eLpNorm (fun a => schattenNorm Q (D a)) (ENNReal.ofReal Q) P +
        ENNReal.ofReal (blockTrace B) := by
    have h1 := eLpNorm_add_le (μ := P) (p := ENNReal.ofReal Q)
      (f := fun a => schattenNorm Q (Y a) + schattenNorm Q (D a))
      (g := fun _ => blockTrace B) (hmY.add hmD) aestronglyMeasurable_const hp1
    have h2 := eLpNorm_add_le (μ := P) (p := ENNReal.ofReal Q)
      (f := fun a => schattenNorm Q (Y a)) (g := fun a => schattenNorm Q (D a)) hmY hmD hp1
    rw [hconst] at h1
    exact le_trans h1 (add_le_add h2 le_rfl)
  calc eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P
      ≤ _ := hmono
    _ = _ := hsmul
    _ ≤ _ := by gcongr

/-- **The closing estimate between real numbers.**  On the event that the three
mixed norms are finite, the mixed-norm closing step is the estimate
`f ≤ K(y + x + b)` the absorption step of `l.fixed.geometry.positive.gap` is applied
to. -/
theorem le_mul_add_of_eLpNorm_eq (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] {Q : ℝ}
    (hQ : 1 ≤ Q) {H Y D : CoeffSpace d → BlockMat d} {B : BlockMat d} {f x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hH : ∀ a, IsSymmetricBlockMat (H a)) (hY : ∀ a, IsSymmetricBlockMat (Y a))
    (hD : ∀ a, IsSymmetricBlockMat (D a)) (hB : IsSymmetricBlockMat B)
    (hBpos : (toFullBlockMat B).PosSemidef)
    (heq : ∀ a, toFullBlockMat (H a) =
      toFullBlockMat (Y a) - (toFullBlockMat (D a) - toFullBlockMat B))
    (hmY : AEStronglyMeasurable (fun a => schattenNorm Q (Y a)) P)
    (hmD : AEStronglyMeasurable (fun a => schattenNorm Q (D a)) P)
    (hfval : eLpNorm (fun a => schattenNorm Q (H a)) (ENNReal.ofReal Q) P = ENNReal.ofReal f)
    (hxval : eLpNorm (fun a => schattenNorm Q (D a)) (ENNReal.ofReal Q) P = ENNReal.ofReal x)
    (hyval : eLpNorm (fun a => schattenNorm Q (Y a)) (ENNReal.ofReal Q) P = ENNReal.ofReal y) :
    f ≤ (2 * d : ℝ) ^ Q⁻¹ * (y + x + blockTrace B) := by
  have hfac : (0 : ℝ) ≤ (2 * d : ℝ) ^ Q⁻¹ := Real.rpow_nonneg (by positivity) _
  have hB0 : (0 : ℝ) ≤ blockTrace B := hBpos.trace_nonneg
  have hmain := eLpNorm_schattenNorm_le_mul_add P hQ hH hY hD hB hBpos heq hmY hmD
  rw [hfval, hxval, hyval, ← ENNReal.ofReal_add hy hx,
    ← ENNReal.ofReal_add (add_nonneg hy hx) hB0, ← ENNReal.ofReal_mul hfac] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hfac (by linarith only [hx, hy, hB0]))).mp hmain

end

end Recurrence
end HighContrast
end Homogenization
