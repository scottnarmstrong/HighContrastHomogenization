import HCPoly.Entry.Multiscale.ResponseInputs.GalerkinSelection
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# The cutoff-weighted quadratic readout as a continuous Hilbert functional

On a positive-volume response cell `U` with a cutoff weight `φ`, the cutoff-weighted quadratic
readout sends a doubled Hilbert block field `z` to the volume average

`(|U|)⁻¹ ∫_U φ(x) ⟪z₁(x), z₂(x)⟫ dx`,

where `z₁` and `z₂` are the potential and flux components of `z`.  Because `φ` is bounded, this is
the diagonal of a bounded bilinear form on `HilbertBlockL2 U`, hence continuous; this is the
analytic ingredient behind `e.response.cutoff.estimate`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The pointwise linear map `(p, q) ↦ (q, 0)` on doubled Hilbert vectors, transported from the
algebraic block carrier. -/
def blockFluxProjL (d : ℕ) : HilbertBlockVec d →L[ℝ] HilbertBlockVec d :=
  (HilbertBlockVec.continuousLinearEquivBlockVec d).symm.toContinuousLinearMap ∘L
    (((ContinuousLinearMap.snd ℝ (Vec d) (Vec d)).prod (0 : BlockVec d →L[ℝ] Vec d)) ∘L
      (HilbertBlockVec.continuousLinearEquivBlockVec d).toContinuousLinearMap)

/-- The pointwise action of `blockFluxProjL`: the potential slot is discarded and the flux slot is
paired with zero. -/
@[simp]
theorem blockFluxProjL_apply (X : HilbertBlockVec d) :
    blockFluxProjL d X = HilbertBlockVec.ofBlockVec (X.flux.toVec, 0) :=
  rfl

/-- The pointwise readout of `blockFluxProjL` against `X` is the pairing of the potential and flux
components. -/
theorem inner_blockFluxProjL (X : HilbertBlockVec d) :
    inner ℝ X (blockFluxProjL d X) = vecDot X.potential.toVec X.flux.toVec := by
  rw [blockFluxProjL_apply, HilbertBlockVec.inner_def]
  simp [blockVecDot, vecDot]

/-- The `L²` realization of `blockFluxProjL`. -/
def blockFluxProjL2 (U : Set (Vec d)) : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  (blockFluxProjL d).compLpL 2 (volumeMeasureOn U)

/-- The `L²` realization of `blockFluxProjL` acts pointwise. -/
theorem coeFn_blockFluxProjL2 (U : Set (Vec d)) (z : HilbertBlockL2 U) :
    (blockFluxProjL2 U z : Vec d → HilbertBlockVec d) =ᵐ[volumeMeasureOn U]
      fun x => blockFluxProjL d (z x) :=
  (blockFluxProjL d).coeFn_compLpL z

/-- Pointwise multiplication by an a.e. bounded scalar field preserves `L²`. -/
theorem memLp_weighted_smul {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) (z : HilbertBlockL2 U) :
    MemLp (fun x => φ x • (z : Vec d → HilbertBlockVec d) x) 2 (volumeMeasureOn U) := by
  refine MemLp.of_le_mul (c := 2) (Lp.memLp z) (hφm.smul (Lp.aestronglyMeasurable z)) ?_
  filter_upwards [hφb] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- Pointwise multiplication by an a.e. bounded scalar field, as a linear map on the doubled
`L²` space. -/
noncomputable def weightedBlockSMul {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    HilbertBlockL2 U →ₗ[ℝ] HilbertBlockL2 U where
  toFun z := (memLp_weighted_smul hφm hφb z).toLp
    (fun x => φ x • (z : Vec d → HilbertBlockVec d) x)
  map_add' z w := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb (z + w)),
      MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb z),
      MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb w),
      Lp.coeFn_add ((memLp_weighted_smul hφm hφb z).toLp _)
        ((memLp_weighted_smul hφm hφb w).toLp _),
      Lp.coeFn_add z w] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' c z := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb (c • z)),
      MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb z),
      Lp.coeFn_smul c ((memLp_weighted_smul hφm hφb z).toLp _),
      Lp.coeFn_smul c z] with x h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply]
    rw [smul_comm]

/-- The weighted multiplication map acts pointwise. -/
theorem coeFn_weightedBlockSMul {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) (z : HilbertBlockL2 U) :
    (weightedBlockSMul hφm hφb z : Vec d → HilbertBlockVec d) =ᵐ[volumeMeasureOn U]
      fun x => φ x • z x :=
  MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb z)

/-- Pointwise multiplication by an a.e. bounded scalar field, as a continuous linear map on the
doubled `L²` space. -/
noncomputable def weightedBlockSMulL {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  (weightedBlockSMul hφm hφb).mkContinuous 2 (by
    intro z
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_weightedBlockSMul hφm hφb z, hφb] with x h1 h2
    rw [h1, norm_smul]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

/-- The continuous weighted multiplication map acts pointwise. -/
theorem coeFn_weightedBlockSMulL {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) (z : HilbertBlockL2 U) :
    (weightedBlockSMulL hφm hφb z : Vec d → HilbertBlockVec d) =ᵐ[volumeMeasureOn U]
      fun x => φ x • z x :=
  MemLp.coeFn_toLp (memLp_weighted_smul hφm hφb z)

/-- The cutoff-weighted quadratic readout: the volume average of `φ` against the pointwise
potential-flux pairing of a doubled `L²` block field.  This is the quadratic readout of
`e.response.cutoff.estimate`. -/
noncomputable def cutoffQuadReadout (U : Set (Vec d)) (φ : Vec d → ℝ) :
    HilbertBlockL2 U → ℝ :=
  fun z => volumeAverage U
    (fun x => φ x * vecDot ((z x).potential.toVec) ((z x).flux.toVec))

/-- Under an a.e. bound on `φ`, the readout is the diagonal of the bounded bilinear form induced by
weighted multiplication. -/
theorem cutoffQuadReadout_eq_weighted_inner {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) (z : HilbertBlockL2 U) :
    cutoffQuadReadout U φ z =
      (volume U).toReal⁻¹ * inner ℝ z
        (weightedBlockSMulL hφm hφb (blockFluxProjL2 (d := d) U z)) := by
  rw [cutoffQuadReadout, volumeAverage, MeasureTheory.L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_weightedBlockSMulL hφm hφb (blockFluxProjL2 (d := d) U z),
    coeFn_blockFluxProjL2 (d := d) U z] with x h1 h2
  rw [h1, h2, real_inner_smul_right, inner_blockFluxProjL]

/-- The cutoff-weighted quadratic readout is continuous in the doubled `L²` field, for any cutoff
weight bounded a.e. by `2`; this is the analytic input to `e.response.cutoff.estimate`. -/
theorem continuous_cutoffQuadReadout (U : Set (Vec d)) [IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : 0 < (volume U).toReal) {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2) :
    Continuous (cutoffQuadReadout U φ) := by
  have _ := hvol
  have heq : cutoffQuadReadout U φ = fun z => (volume U).toReal⁻¹ * inner ℝ z
      (weightedBlockSMulL hφm hφb (blockFluxProjL2 (d := d) U z)) :=
    funext fun z => cutoffQuadReadout_eq_weighted_inner hφm hφb z
  rw [heq]
  exact continuous_const.mul
    (continuous_inner.comp (continuous_id.prodMk
      ((weightedBlockSMulL hφm hφb).continuous.comp
        (blockFluxProjL2 (d := d) U).continuous)))

/-- On a block field promoted to the doubled `L²` space, the readout is the volume average of the
pointwise potential-flux pairing. -/
theorem cutoffQuadReadout_toHilbertBlockL2OfBlockField (U : Set (Vec d)) {φ : Vec d → ℝ}
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    cutoffQuadReadout U φ (toHilbertBlockL2OfBlockField (U := U) hX) =
      volumeAverage U (fun x => φ x * vecDot (X.potential x) (X.flux x)) := by
  simp only [cutoffQuadReadout, volumeAverage]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (U := U) hX] with x hx
  rw [hx]
  simp [hilbertifyBlockField, BlockState.eval]

end

end Homogenization.HighContrast.Multiscale
