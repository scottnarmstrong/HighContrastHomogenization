import HCPoly.Entry.Analysis.SchattenSpectral
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Integrability support for the positive-gap estimate

This file collects the supporting lemmas for the positive-gap estimate:
entrywise expectations, trace/order preservation by integration, and basic
membership examples.
-/

open Homogenization.HighContrast (CoeffSpace blockSub blockTrace
  blockVecDot_blockMatVecMul_eq_sum toFullBlockMat_eq_blockMatEntry)
namespace Homogenization.HighContrast

open MeasureTheory
open scoped BigOperators
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

namespace MemLqSchatten

private theorem absSchattenNorm_nonneg_ae {P : Measure (CoeffSpace d)}
    {N : ℝ} {H : CoeffSpace d → BlockMat d}
    (hH : MemLqSchatten P N H) (hN : 1 ≤ N) :
    0 ≤ᵐ[P] fun a => absSchattenNorm N (H a) := by
  filter_upwards [hH.symmetric] with a ha
  exact Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff (H a)).2 ha) hN

private theorem absSchattenNorm_aestronglyMeasurable {P : Measure (CoeffSpace d)}
    {N : ℝ} {H : CoeffSpace d → BlockMat d}
    (hH : MemLqSchatten P N H) (hN : 1 ≤ N) :
    AEStronglyMeasurable (fun a => absSchattenNorm N (H a)) P := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : AEStronglyMeasurable (fun a => absSchattenNorm N (H a) ^ N) P :=
    hH.integrable.aestronglyMeasurable
  have hroot :
      (fun a => (absSchattenNorm N (H a) ^ N) ^ N⁻¹) =ᵐ[P]
        fun a => absSchattenNorm N (H a) := by
    filter_upwards [absSchattenNorm_nonneg_ae hH hN] with a ha
    exact Real.rpow_rpow_inv ha hNpos.ne'
  exact (hpow.aemeasurable.pow_const N⁻¹).aestronglyMeasurable.congr hroot

/-- The real Schatten moment carrier gives the corresponding Mathlib `eLpNorm`
membership of the scalar Schatten norm. -/
theorem memLp_absSchattenNorm {d : ℕ} {P : Measure (CoeffSpace d)}
    {N : ℝ} {H : CoeffSpace d → BlockMat d} (hH : MemLqSchatten P N H) (hN : 1 ≤ N) :
    MemLp (fun a => absSchattenNorm N (H a)) (ENNReal.ofReal N) P := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp0 : ENNReal.ofReal N ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hNpos)
  have hsn_meas : AEStronglyMeasurable (fun a => absSchattenNorm N (H a)) P :=
    absSchattenNorm_aestronglyMeasurable hH hN
  rw [← MeasureTheory.integrable_norm_rpow_iff hsn_meas hp0 ENNReal.ofReal_ne_top]
  exact hH.integrable.congr <| by
    filter_upwards [absSchattenNorm_nonneg_ae hH hN] with a ha
    simp [Real.norm_eq_abs, abs_of_nonneg ha, ENNReal.toReal_ofReal hNpos.le]

/-- The real mixed norm is the real value of the finite Mathlib `eLpNorm`. -/
theorem lqSchattenNorm_eq_eLpNorm_toReal {d : ℕ}
    {P : Measure (CoeffSpace d)} {N : ℝ} {H : CoeffSpace d → BlockMat d}
    (hH : MemLqSchatten P N H) (hN : 1 ≤ N) :
    eLpNorm (fun a => absSchattenNorm N (H a)) (ENNReal.ofReal N) P < ⊤ ∧
      0 ≤ lqSchattenNorm P N H ∧
      lqSchattenNorm P N H =
        (eLpNorm (fun a => absSchattenNorm N (H a)) (ENNReal.ofReal N) P).toReal := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp0 : ENNReal.ofReal N ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hNpos)
  have hmem := hH.memLp_absSchattenNorm hN
  have hnonneg_moment : 0 ≤ᵐ[P] fun a => absSchattenNorm N (H a) ^ N := by
    filter_upwards [absSchattenNorm_nonneg_ae hH hN] with a ha
    exact Real.rpow_nonneg ha N
  have hnorm_integral_eq :
      (∫ a, ‖absSchattenNorm N (H a)‖ ^ (ENNReal.ofReal N).toReal ∂P) =
        ∫ a, absSchattenNorm N (H a) ^ N ∂P := by
    apply integral_congr_ae
    filter_upwards [absSchattenNorm_nonneg_ae hH hN] with a ha
    simp [Real.norm_eq_abs, abs_of_nonneg ha, ENNReal.toReal_ofReal hNpos.le]
  have hlq_nonneg : 0 ≤ lqSchattenNorm P N H := by
    unfold lqSchattenNorm
    exact Real.rpow_nonneg (integral_nonneg_of_ae hnonneg_moment) N⁻¹
  constructor
  · exact hmem.eLpNorm_lt_top
  constructor
  · exact hlq_nonneg
  · unfold lqSchattenNorm
    rw [hmem.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top]
    rw [ENNReal.toReal_ofReal]
    · rw [hnorm_integral_eq, ENNReal.toReal_ofReal hNpos.le]
    · rw [hnorm_integral_eq, ENNReal.toReal_ofReal hNpos.le]
      exact Real.rpow_nonneg (integral_nonneg_of_ae hnonneg_moment) N⁻¹

theorem abs_blockMatEntry_le_blockOpNorm (H : BlockMat d) (α β : BlockCoord d) :
    |blockMatEntry H α β| ≤ blockOpNorm H := by
  let M : FullBlockMat d := toFullBlockMat H
  have hentry :
      blockMatEntry H α β = M.mulVec (Pi.single β (1 : ℝ)) α := by
    simp [M, Matrix.mulVec, toFullBlockMat_eq_blockMatEntry]
  calc
    |blockMatEntry H α β| = |M.mulVec (Pi.single β (1 : ℝ)) α| := by rw [hentry]
    _ = ‖(WithLp.toLp (2 : ENNReal) (M.mulVec (Pi.single β (1 : ℝ))) :
          EuclideanSpace ℝ (BlockCoord d)).ofLp α‖ := by
        simp [Real.norm_eq_abs]
    _ ≤ ‖(WithLp.toLp (2 : ENNReal) (M.mulVec (Pi.single β (1 : ℝ))) :
          EuclideanSpace ℝ (BlockCoord d))‖ :=
        PiLp.norm_apply_le _ α
    _ = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M
          (WithLp.toLp (2 : ENNReal) (Pi.single β (1 : ℝ)))‖ := by
        rw [Matrix.toEuclideanCLM_toLp]
    _ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ *
          ‖(WithLp.toLp (2 : ENNReal) (Pi.single β (1 : ℝ)) :
            EuclideanSpace ℝ (BlockCoord d))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖Matrix.toEuclideanCLM (n := BlockCoord d) (𝕜 := ℝ) M‖ := by
        simp
    _ = blockOpNorm H := by
        simp [blockOpNorm, M, Matrix.l2_opNorm_toEuclideanCLM]

/-- Each scalar block entry is integrable on a finite measure space. -/
theorem integrable_entry {d : ℕ} {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {N : ℝ} {H : CoeffSpace d → BlockMat d}
    (hH : MemLqSchatten P N H) (hN : 1 ≤ N) (α β : BlockCoord d) :
    Integrable (fun a => blockMatEntry (H a) α β) P := by
  have hscalar :
      Integrable (fun a => absSchattenNorm N (H a)) P :=
    (hH.memLp_absSchattenNorm hN).integrable (ENNReal.one_le_ofReal.mpr hN)
  refine hscalar.mono' (hH.measurable α β) ?_
  filter_upwards [hH.symmetric] with a ha
  have hHerm : (toFullBlockMat (H a)).IsHermitian :=
    (Analysis.toFullBlockMat_isHermitian_iff (H a)).2 ha
  calc
    ‖blockMatEntry (H a) α β‖ = |blockMatEntry (H a) α β| := Real.norm_eq_abs _
    _ ≤ blockOpNorm (H a) := abs_blockMatEntry_le_blockOpNorm (H a) α β
    _ ≤ absSchattenNorm N (H a) := Analysis.blockOpNorm_le_absSchattenNorm hHerm hN

end MemLqSchatten

namespace Analysis

private theorem l2_opNorm_conjStarAlgAut_for_integrability {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℝ)) (A : Matrix n n ℝ) :
    ‖(Unitary.conjStarAlgAut ℝ _ U) A‖ = ‖A‖ := by
  rw [Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary
    (A := (U : Matrix n n ℝ) * A) (hU := Unitary.star_mem U.prop)]
  exact CStarRing.norm_mem_unitary_mul A U.prop

private theorem hermitian_l2_opNorm_eq_eigenvalue_norm_for_integrability {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) :
    ‖toFullBlockMat H‖ = ‖hH.eigenvalues‖ := by
  conv_lhs => rw [hH.spectral_theorem]
  rw [l2_opNorm_conjStarAlgAut_for_integrability]
  simp

private theorem abs_eigenvalue_le_l2_opNorm_for_integrability {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) (i : BlockCoord d) :
    |hH.eigenvalues i| ≤ blockOpNorm H := by
  rw [blockOpNorm, hermitian_l2_opNorm_eq_eigenvalue_norm_for_integrability hH]
  simpa [Real.norm_eq_abs] using norm_le_pi_norm hH.eigenvalues i

private theorem eigen_abs_rpow_sum_le_card_mul_blockOpNorm_rpow {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (_hN : 1 ≤ N) :
    (∑ i : BlockCoord d, |hH.eigenvalues i| ^ N) ≤
      (Fintype.card (BlockCoord d) : ℝ) * blockOpNorm H ^ N := by
  calc
    (∑ i : BlockCoord d, |hH.eigenvalues i| ^ N)
        ≤ ∑ _i : BlockCoord d, blockOpNorm H ^ N := by
          refine Finset.sum_le_sum fun i _hi => ?_
          exact Real.rpow_le_rpow (abs_nonneg _)
            (abs_eigenvalue_le_l2_opNorm_for_integrability hH i) (by positivity)
    _ = (Fintype.card (BlockCoord d) : ℝ) * blockOpNorm H ^ N := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- A crude finite-dimensional comparison in the reverse direction from
`blockOpNorm_le_absSchattenNorm`.  The factor depends only on the doubled block dimension and the
exponent; it is used only to prove membership/definedness of subtraction and centering fields,
not as one of the sharp printed constants in the PositiveGap estimate. -/
theorem absSchattenNorm_le_dim_rpow_mul_blockOpNorm {d : ℕ} {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N H ≤ (2 * (d : ℝ)) ^ N⁻¹ * blockOpNorm H := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNne : N ≠ 0 := hNpos.ne'
  have hsum_nonneg : 0 ≤ ∑ i : BlockCoord d, |hH.eigenvalues i| ^ N :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) N
  have hop_nonneg : 0 ≤ blockOpNorm H := by
    unfold blockOpNorm
    exact norm_nonneg _
  have hcard_nonneg : 0 ≤ (Fintype.card (BlockCoord d) : ℝ) := by positivity
  have hcard_eq : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
    simp only [BlockCoord, Fintype.card_sum, Fintype.card_fin]
    rw [Nat.cast_add]
    ring
  rw [Analysis.absSchattenNorm_eq_eigenvalues hH hN, schattenNormEigen]
  calc
    (∑ i : BlockCoord d, |hH.eigenvalues i| ^ N) ^ N⁻¹
        ≤ ((Fintype.card (BlockCoord d) : ℝ) * blockOpNorm H ^ N) ^ N⁻¹ :=
          Real.rpow_le_rpow hsum_nonneg
            (eigen_abs_rpow_sum_le_card_mul_blockOpNorm_rpow hH hN) (by positivity)
    _ = (Fintype.card (BlockCoord d) : ℝ) ^ N⁻¹ * blockOpNorm H := by
          rw [Real.mul_rpow hcard_nonneg (Real.rpow_nonneg hop_nonneg N)]
          rw [← Real.rpow_mul hop_nonneg N N⁻¹, mul_inv_cancel₀ hNne, Real.rpow_one]
    _ = (2 * (d : ℝ)) ^ N⁻¹ * blockOpNorm H := by
          rw [hcard_eq]

private theorem blockMatEntry_blockSub (A B : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (blockSub A B) α β = blockMatEntry A α β - blockMatEntry B α β := by
  cases α <;> cases β <;> rfl

private theorem blockTrace_eq_sum_entries (H : BlockMat d) :
    blockTrace H = ∑ α : BlockCoord d, blockMatEntry H α α := by
  simp [blockTrace, Matrix.trace, toFullBlockMat_eq_blockMatEntry]

private theorem integrable_quadratic_form {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d}
    (hH : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (H a) α β) P)
    (X : BlockVec d) :
    Integrable (fun a => blockVecDot X (blockMatVecMul (H a) X)) P := by
  rw [show (fun a => blockVecDot X (blockMatVecMul (H a) X)) =
      fun a => ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec X α * (blockMatEntry (H a) α β * toFullBlockVec X β) by
    funext a
    exact blockVecDot_blockMatVecMul_eq_sum (H a) X]
  refine integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => ?_
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    ((hH α β).const_mul (toFullBlockVec X α * toFullBlockVec X β))

private theorem blockVecDot_blockMatVecMul_integral {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d}
    (hH : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (H a) α β) P)
    (X : BlockVec d) :
    blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P)) X) =
      ∫ a, blockVecDot X (blockMatVecMul (H a) X) ∂P := by
  calc
    blockVecDot X
        (blockMatVecMul
          (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P)) X)
        = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec X α *
              ((∫ a, blockMatEntry (H a) α β ∂P) * toFullBlockVec X β) := by
          rw [blockVecDot_blockMatVecMul_eq_sum]
          simp
    _ = ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            ∫ a, toFullBlockVec X α *
              (blockMatEntry (H a) α β * toFullBlockVec X β) ∂P := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
    _ = ∫ a, ∑ α : BlockCoord d, ∑ β : BlockCoord d,
            toFullBlockVec X α * (blockMatEntry (H a) α β * toFullBlockVec X β) ∂P := by
          symm
          rw [MeasureTheory.integral_finsetSum]
          · congr with α
            rw [MeasureTheory.integral_finsetSum]
            intro β _
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              ((hH α β).const_mul (toFullBlockVec X α * toFullBlockVec X β))
          · intro α _
            exact integrable_finsetSum _ fun β _ => by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                ((hH α β).const_mul (toFullBlockVec X α * toFullBlockVec X β))
    _ = ∫ a, blockVecDot X (blockMatVecMul (H a) X) ∂P := by
          apply integral_congr_ae
          exact ae_of_all P fun a => (blockVecDot_blockMatVecMul_eq_sum (H a) X).symm

/-- Constant symmetric blocks are in the real Schatten carrier over a finite law. -/
theorem memLqSchatten_const {d : ℕ} (P : Measure (CoeffSpace d))
    [IsFiniteMeasure P] {N : ℝ} (_hN : 1 ≤ N) (B : BlockMat d)
    (hB : IsSymmetricBlockMat B) : MemLqSchatten P N (fun _ => B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α β
    exact aestronglyMeasurable_const
  · exact ae_of_all P fun _ => hB
  · exact integrable_const _

/-- Entrywise Bochner integration commutes with block subtraction. -/
theorem integral_blockSub {d : ℕ} {P : Measure (CoeffSpace d)}
    {F G : CoeffSpace d → BlockMat d}
    (hF : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (F a) α β) P)
    (hG : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (G a) α β) P) :
    ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (blockSub (F a) (G a)) α β ∂P) =
      blockSub (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P))
        (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)) := by
  change
    ofFullBlockMat
        (Matrix.of fun α β => ∫ a, blockMatEntry (blockSub (F a) (G a)) α β ∂P) =
      ofFullBlockMat
        (Matrix.of fun α β =>
          (∫ a, blockMatEntry (F a) α β ∂P) - ∫ a, blockMatEntry (G a) α β ∂P)
  congr 1
  ext α β
  simp [blockMatEntry_blockSub, MeasureTheory.integral_sub (hF α β) (hG α β)]

/-- The trace of an entrywise Bochner expectation is the expected trace. -/
theorem blockTrace_integral {d : ℕ} {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d}
    (hH : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (H a) α β) P) :
    Integrable (fun a => blockTrace (H a)) P ∧
      blockTrace (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P)) =
        ∫ a, blockTrace (H a) ∂P := by
  have hdiag : ∀ α : BlockCoord d, Integrable (fun a => blockMatEntry (H a) α α) P :=
    fun α => hH α α
  constructor
  · rw [show (fun a => blockTrace (H a)) =
      fun a => ∑ α : BlockCoord d, blockMatEntry (H a) α α by
        funext a
        exact blockTrace_eq_sum_entries (H a)]
    exact integrable_finsetSum _ fun α _ => hdiag α
  · calc
      blockTrace
          (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P))
          = ∑ α : BlockCoord d, ∫ a, blockMatEntry (H a) α α ∂P := by
            simp [blockTrace_eq_sum_entries]
      _ = ∫ a, ∑ α : BlockCoord d, blockMatEntry (H a) α α ∂P := by
            rw [MeasureTheory.integral_finsetSum]
            exact fun α _ => hdiag α
      _ = ∫ a, blockTrace (H a) ∂P := by
            apply integral_congr_ae
            exact ae_of_all P fun a => (blockTrace_eq_sum_entries (H a)).symm

/-- Entrywise Bochner expectation preserves almost-everywhere symmetry. -/
theorem isSymmetricBlockMat_integral {d : ℕ} {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d} (hH : ∀ᵐ a ∂P, IsSymmetricBlockMat (H a)) :
    IsSymmetricBlockMat
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (H a) α β ∂P)) := by
  intro α β
  simp only [blockMatEntry_ofFullBlockMat, Matrix.of_apply]
  exact integral_congr_ae (hH.mono fun a ha => ha α β)

/-- Entrywise Bochner expectation preserves the block Loewner order. -/
theorem blockMatLoewnerLE_integral {d : ℕ} {P : Measure (CoeffSpace d)}
    {F G : CoeffSpace d → BlockMat d}
    (hF : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (F a) α β) P)
    (hG : ∀ α β : BlockCoord d, Integrable (fun a => blockMatEntry (G a) α β) P)
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    BlockMatLoewnerLE
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (F a) α β ∂P))
      (ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (G a) α β ∂P)) := by
  intro X
  rw [blockVecDot_blockMatVecMul_integral hF X,
    blockVecDot_blockMatVecMul_integral hG X]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  exact integral_mono_ae
    ((integrable_quadratic_form hF X).const_mul (1 / 2 : ℝ))
    ((integrable_quadratic_form hG X).const_mul (1 / 2 : ℝ))
    (hFG.mono fun a ha => ha X)

end Analysis

end

end Homogenization.HighContrast
