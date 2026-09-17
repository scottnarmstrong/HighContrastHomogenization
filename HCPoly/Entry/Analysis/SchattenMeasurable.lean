import HCPoly.Entry.Analysis.SchattenIntegrability

/-!
# Measurability and membership closure for the Schatten norm

Support for the paper's Schatten estimates, on the real exponent
and CG block carriers. The pinned Mathlib supplies the real matrix CFC, but does
not register its isometry for the L2 operator norm. We prove that property from
the spectral representation, then use Mathlib's variable-operator continuity.

Continuity is asserted on symmetric full matrices. The CFC is zero off
that closed set, so its Schatten value is measurable on all full matrices.
Entrywise a.e. measurability therefore suffices, without a circular moment premise.
The dimension factor in the subtraction proof proves finiteness only; it is not
a sharp Schatten triangle inequality or a constant in the printed gap estimate.
-/

open Homogenization.HighContrast (CoeffSpace blockSub)
namespace Homogenization.HighContrast

open MeasureTheory Filter Topology
open scoped BigOperators Matrix.Norms.L2Operator ContinuousFunctionalCalculus

noncomputable section

variable {d : ℕ}

namespace Analysis

private theorem matrix_isometric_cfc {n : Type*} [Fintype n] [DecidableEq n] :
    IsometricContinuousFunctionalCalculus ℝ (Matrix n n ℝ) IsSelfAdjoint where
  isometric M hM := by
    have h : M.IsHermitian := hM
    rw [cfcHom_eq_of_continuous_of_map_id hM h.cfcAux
      h.isClosedEmbedding_cfcAux.continuous h.cfcAux_id]
    apply AddMonoidHomClass.isometry_of_norm h.cfcAux
    intro f
    rw [Matrix.IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply]
    rw [CStarRing.norm_mul_mem_unitary
      (hU := Unitary.star_mem h.eigenvectorUnitary.prop)]
    rw [CStarRing.norm_mem_unitary_mul _ h.eigenvectorUnitary.prop]
    rw [Matrix.l2_opNorm_diagonal]
    simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2 fun i =>
        f.norm_coe_le_norm ⟨h.eigenvalues i, h.eigenvalues_mem_spectrum_real i⟩
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
      intro x
      have hxmem : (x : ℝ) ∈ Set.range h.eigenvalues := by
        rw [← h.spectrum_real_eq_range_eigenvalues]
        exact x.property
      obtain ⟨i, hi⟩ := hxmem
      have hx : x = ⟨h.eigenvalues i, h.eigenvalues_mem_spectrum_real i⟩ :=
        Subtype.ext hi.symm
      rw [hx]
      exact norm_le_pi_norm
        (fun j : n => f ⟨h.eigenvalues j, h.eigenvalues_mem_spectrum_real j⟩) i

/-- The Schatten norm is continuous on symmetric full blocks, for every
real exponent `N ≥ 1`, including nonintegral exponents and dimension zero. -/
theorem continuousOn_absSchattenNorm {N : ℝ} (hN : 1 ≤ N) :
    ContinuousOn (fun M : FullBlockMat d => absSchattenNorm N (ofFullBlockMat M))
      {M | M.IsHermitian} := by
  let := matrix_isometric_cfc (n := BlockCoord d)
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcfc : ContinuousOn
      (fun M : FullBlockMat d => cfc (fun x : ℝ => |x| ^ N) M)
      {M | M.IsHermitian} := by
    refine ContinuousOn.cfc (s := fun M : FullBlockMat d =>
      Metric.closedBall (0 : ℝ) (‖M‖ + 1)) (fun x : ℝ => |x| ^ N) ?_ ?_ ?_ ?_ ?_
    · intro M _
      exact isCompact_closedBall _ _
    · exact continuous_id.continuousOn
    · intro M _
      have hn : ∀ᶠ M' : FullBlockMat d in 𝓝 M, ‖M'‖ < ‖M‖ + 1 :=
        continuous_norm.continuousAt.eventually
          (isOpen_Iio.mem_nhds (by simp))
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with M' hM' hHerm
      intro x hx
      exact Metric.mem_closedBall.mpr (by
        simpa [Real.dist_eq, abs_sub_comm] using
          (IsometricContinuousFunctionalCalculus.norm_spectrum_le M' hx hHerm).trans hM'.le)
    · intro M hM
      exact hM
    · intro M _
      exact ((Real.continuous_rpow_const hNpos.le).comp continuous_abs).continuousOn
  have ht := (Continuous.matrix_trace continuous_id).comp_continuousOn hcfc
  simpa only [absSchattenNorm, toFullBlockMat_ofFullBlockMat] using!
    (Real.continuous_rpow_const (inv_nonneg.mpr hNpos.le)).comp_continuousOn ht

/-- Borel measurability on all full blocks uses the zero convention off
the closed set of symmetric matrices; global continuity is not asserted. The
explicit function type is CG's `FullBlockMat d` unfolded to expose its entrywise
Borel sigma algebra, without adding an instance or a carrier. -/
theorem measurable_absSchattenNorm {N : ℝ} (hN : 1 ≤ N) :
    Measurable (fun M : BlockCoord d → BlockCoord d → ℝ =>
      absSchattenNorm N (ofFullBlockMat M)) := by
  classical
  have hOM : OpensMeasurableSpace (BlockCoord d → BlockCoord d → ℝ) := inferInstance
  have hs : MeasurableSet {M : BlockCoord d → BlockCoord d → ℝ | Matrix.IsHermitian M} := by
    exact @IsClosed.measurableSet _ _ _ _ hOM
      (isClosed_eq (f := fun M : BlockCoord d → BlockCoord d → ℝ =>
        Matrix.conjTranspose M) continuous_id.matrix_conjTranspose continuous_id)
  have hc : ContinuousOn (fun M : BlockCoord d → BlockCoord d → ℝ =>
      absSchattenNorm N (ofFullBlockMat M)) {M | Matrix.IsHermitian M} :=
    continuousOn_absSchattenNorm hN
  have hp := hc.measurable_piecewise
    (g := fun _ => (0 : ℝ)) continuous_const.continuousOn hs
  convert hp using 1
  funext M
  by_cases hM : M ∈ {M : BlockCoord d → BlockCoord d → ℝ | Matrix.IsHermitian M}
  · simp [Set.piecewise_eq_of_mem _ _ _ hM]
  · have hM' : ¬ @IsSelfAdjoint (FullBlockMat d) _ M := hM
    simp [Set.piecewise_eq_of_notMem _ _ _ hM, absSchattenNorm, toFullBlockMat_ofFullBlockMat M,
      cfc_apply_of_not_predicate (A := FullBlockMat d) M hM',
      Real.zero_rpow (inv_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hN)))]

/-- The a.e. measurability bridge depends on the entrywise measurability
premise alone, so it applies in particular to a.e. symmetric fields before their
moment integrability has been established. -/
theorem aestronglyMeasurable_absSchattenNorm {P : Measure (CoeffSpace d)}
    {F : CoeffSpace d → BlockMat d} (hF : HasMeasurableBlock P F)
    {N : ℝ} (hN : 1 ≤ N) :
    AEStronglyMeasurable (fun ω => absSchattenNorm N (F ω)) P := by
  have hm : AEMeasurable (fun ω α β => toFullBlockMat (F ω) α β) P :=
    aemeasurable_pi_lambda _ fun α =>
      aemeasurable_pi_lambda _ fun β => (hF α β).aemeasurable
  simpa only [Function.comp_def, ofFullBlockMat_toFullBlockMat] using
    ((measurable_absSchattenNorm (d := d) hN).comp_aemeasurable hm).aestronglyMeasurable

end Analysis

namespace MemLqSchatten

private theorem entry_sub (A B : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (blockSub A B) α β = blockMatEntry A α β - blockMatEntry B α β := by
  cases α <;> cases β <;> rfl

private theorem full_sub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

/-- Subtraction preserves the real Schatten moment carrier on any measure
space. The crude factor `(2*d)^(1/N)` is used only for moment finiteness, and
does not supply the sharp triangle inequality in the printed gap estimate. -/
theorem sub {P : Measure (CoeffSpace d)} {N : ℝ}
    {F G : CoeffSpace d → BlockMat d}
    (hF : MemLqSchatten P N F) (hG : MemLqSchatten P N G) (hN : 1 ≤ N) :
    MemLqSchatten P N (fun a => blockSub (F a) (G a)) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hm : HasMeasurableBlock P (fun a => blockSub (F a) (G a)) := by
    intro α β
    simp only [entry_sub]
    exact (hF.measurable α β).sub (hG.measurable α β)
  have hs : ∀ᵐ a ∂P, IsSymmetricBlockMat (blockSub (F a) (G a)) := by
    filter_upwards [hF.symmetric, hG.symmetric] with a ha hb
    intro α β
    rw [entry_sub, entry_sub, ha α β, hb α β]
  have hsm := Analysis.aestronglyMeasurable_absSchattenNorm hm hN
  have hdom := ((hF.memLp_absSchattenNorm hN).add
    (hG.memLp_absSchattenNorm hN)).const_mul ((2 * (d : ℝ)) ^ N⁻¹)
  have hmem : MemLp (fun a => absSchattenNorm N (blockSub (F a) (G a)))
      (ENNReal.ofReal N) P := by
    apply hdom.mono' hsm
    filter_upwards [hF.symmetric, hG.symmetric, hs] with a ha hb hab
    have hA := (Analysis.toFullBlockMat_isHermitian_iff (F a)).2 ha
    have hB := (Analysis.toFullBlockMat_isHermitian_iff (G a)).2 hb
    have hAB := (Analysis.toFullBlockMat_isHermitian_iff _).2 hab
    rw [Real.norm_eq_abs, abs_of_nonneg (Analysis.absSchattenNorm_nonneg hAB hN)]
    calc
      absSchattenNorm N (blockSub (F a) (G a))
          ≤ (2 * (d : ℝ)) ^ N⁻¹ * blockOpNorm (blockSub (F a) (G a)) :=
        Analysis.absSchattenNorm_le_dim_rpow_mul_blockOpNorm hAB hN
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * (blockOpNorm (F a) + blockOpNorm (G a)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [blockOpNorm, full_sub] using
          norm_sub_le (toFullBlockMat (F a)) (toFullBlockMat (G a))
      _ ≤ (2 * (d : ℝ)) ^ N⁻¹ * (absSchattenNorm N (F a) + absSchattenNorm N (G a)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (Analysis.blockOpNorm_le_absSchattenNorm hA hN)
            (Analysis.blockOpNorm_le_absSchattenNorm hB hN)) (by positivity)
  refine ⟨hm, hs, ?_⟩
  have hi := (integrable_norm_rpow_iff hsm
    (ne_of_gt (ENNReal.ofReal_pos.mpr hNpos)) ENNReal.ofReal_ne_top).2 hmem
  apply hi.congr
  filter_upwards [hs] with a ha
  have hA := (Analysis.toFullBlockMat_isHermitian_iff _).2 ha
  simp [Real.norm_eq_abs, abs_of_nonneg (Analysis.absSchattenNorm_nonneg hA hN),
    ENNReal.toReal_ofReal hNpos.le]

/-- Centering by the entrywise expectation preserves membership on a finite
measure space. This uses subtraction closure and symmetry of the mean, with no
additional moment or measurability premise. -/
theorem center {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {N : ℝ}
    {H : CoeffSpace d → BlockMat d} (hH : MemLqSchatten P N H) (hN : 1 ≤ N) :
    MemLqSchatten P N (fun a => blockSub (H a)
      (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (H b) α β ∂P))) := by
  exact hH.sub (Analysis.memLqSchatten_const P hN _
    (Analysis.isSymmetricBlockMat_integral hH.symmetric)) hN

end MemLqSchatten

end

end Homogenization.HighContrast
