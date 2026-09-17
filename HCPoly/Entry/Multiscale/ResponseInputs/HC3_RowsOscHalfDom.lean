import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscSum
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectLayerLoad
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsOscLimDom

/-!
# The oscillation half of the cutoff-mean row, closed by domination

`HC3_DirectOscHalf` bounds the oscillation half of the second cutoff-mean row of
`p.response.transfer` by the source load, but it asks for an annealed bound on the descendant
remainder, and that bound would need the annealed mean of the cell average of a POINTWISE modulus
of the optimizer state, which the standing assumptions do not supply: the ellipticity constants of
a sample are not bounded in the law.

The passage to the limit does not need it.  The remainder tends to zero along every sample from
the pathwise ellipticity alone, and the generation increments see only CELL AVERAGES of the state,
so the scale-average seminorm of those averages is an integrable envelope for the whole series.
This module restates the oscillation half through
`integrable_and_abs_integral_sub_integral_le_of_dominated_descendant`, which replaces the annealed
remainder bound by those two hypotheses, and additionally delivers the `P`-integrability of the
annealed functional.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The oscillation half of the cutoff-mean row is bounded by the source load, by domination.**
The hypotheses of `abs_integral_sub_cellPart_le_descendant_load` with its annealed remainder bound
`|∫ rem N| ≤ C₀ 3^{-N} M` replaced by the pathwise vanishing `rem N a → 0` and an integrable
envelope `env` for the generation increments, and with the integrability of `Phi` replaced by its
almost-everywhere strong measurability.  The conclusion carries that integrability as well as the
bound. -/
theorem integrable_and_abs_integral_sub_cellPart_le_descendant_load {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s : ℤ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (Phi Tcell : CoeffSpace d → ℝ) (inc rem : ℕ → CoeffSpace d → ℝ)
    (Z : ℕ → Finset (Fin d → ℤ)) (θ : ℕ → (Fin d → ℤ) → ℝ)
    (pairing G D : ℕ → (Fin d → ℤ) → CoeffSpace d → ℝ)
    (env : ℕ → CoeffSpace d → ℝ) (K EJ : ℝ)
    (hK : 0 ≤ K) (hEJ : 0 ≤ EJ)
    (hdec : ∀ (N : ℕ) (a : CoeffSpace d),
      Phi a = Tcell a + (∑ n ∈ Finset.range N, inc n a) + rem N a)
    (hincdef : ∀ (n : ℕ) (a : CoeffSpace d),
      inc n a = ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a)
    (henv0 : ∀ (n : ℕ) (a : CoeffSpace d), 0 ≤ env n a)
    (henvdom : ∀ (n : ℕ) (a : CoeffSpace d), |inc n a| ≤ env n a)
    (henvsum : ∀ᵐ a ∂P, Summable fun n : ℕ => env n a)
    (henvI : Integrable (fun a => ∑' n : ℕ, env n a) P)
    (hrem0 : ∀ a : CoeffSpace d, Filter.Tendsto (fun N : ℕ => rem N a) Filter.atTop (nhds 0))
    (hθ : ∀ n : ℕ, ∀ W ∈ Z n, |θ n W| ≤ K * (3 : ℝ) ^ (-(n : ℝ)))
    (hG : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ G n W a)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a)
    (hbd : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, |pairing n W a| ≤ G n W a * Real.sqrt (2 * D n W a))
    (hGsq : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P)
      ≤ (((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
          ∑ z ∈ triadicIndexBox d (n + 1),
            (Real.sqrt (vecDot Y.1 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
                  Y.1)) +
              Real.sqrt (vecDot Y.2 (matVecMul
                  (annealedBlockOf P
                    (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
                  Y.2))) ^ 2)
    (hDval : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P) ≤ 2 * EJ)
    (hPhiM : AEStronglyMeasurable Phi P) (hT : Integrable Tcell P)
    (hincI : ∀ n : ℕ, Integrable (inc n) P)
    (hFint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) P)
    (hDint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) P)
    (hMidint : ∀ n : ℕ, Integrable (fun a =>
      Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a)) P)
    (hPint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
      θ n W * (Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a))) P)
    (hsumm : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2))) :
    Integrable Phi P
      ∧ |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P|
          ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
                * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y))
              * Real.sqrt (2 * EJ) := by
  let L : ℕ → ℝ := fun n =>
    (((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d (n + 1),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
              Y.2))) ^ 2
  let g : ℕ → ℝ := fun n =>
    (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2)
  have hL : ∀ n, 0 ≤ L n := by
    intro n
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun z _ => sq_nonneg _)
  have hg : Summable g := by
    simpa only [g] using hsumm
  have hweight : ∀ n : ℕ,
      (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n
        = (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1) := by
    intro n
    have hw : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
        = (3 : ℝ) ^ ((3 : ℝ) / 2)
          * (3 : ℝ) ^ (-((3 : ℝ) / 2) * ((n + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    rw [hw]
    dsimp only [L, g]
    ring
  have hsum : Summable (fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) := by
    have hg1 : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff 1).2 hg
    have hc : Summable (fun n : ℕ => (3 : ℝ) ^ ((3 : ℝ) / 2) * g (n + 1)) :=
      Summable.mul_left ((3 : ℝ) ^ ((3 : ℝ) / 2)) hg1
    exact Summable.congr hc (fun n => (hweight n).symm)
  have hsum' : Summable (fun n : ℕ => (3 : ℝ) ^ (-(n : ℝ)) * Real.sqrt (L n)) :=
    summable_rpow_neg_mul_sqrt_of_summable L hL hsum
  have hPint' : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
      θ n W * pairing n W a) P :=
    fun n => (hincI n).congr (Filter.Eventually.of_forall fun a => hincdef n a)
  let B : ℝ := K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
        * Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n))
      * Real.sqrt (2 * EJ)
  have hB : ∀ N : ℕ, |∑ n ∈ Finset.range N, ∫ a, inc n a ∂P| ≤ B := by
    intro N
    have h := abs_sum_range_descendant_pairing_le P N Z θ pairing G D L K EJ
      hK hEJ hL hθ hG hD hbd hGsq hDval hFint hDint hMidint hPint hPint' hsum hsum'
    have hcongr : (∑ n ∈ Finset.range N, ∫ a, inc n a ∂P)
        = ∑ n ∈ Finset.range N, ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
            θ n W * pairing n W a ∂P := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      exact integral_congr_ae (Filter.Eventually.of_forall fun a => hincdef n a)
    rw [hcongr]
    exact h
  have hpair : Integrable Phi P ∧ |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P| ≤ B :=
    integrable_and_abs_integral_sub_integral_le_of_dominated_descendant P Phi Tcell inc rem env B
      hdec henv0 henvdom henvsum henvI hrem0 hB hT hPhiM hincI
  have hsum_le : (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)
      ≤ (3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y :=
    tsum_succ_layer_le_respSourceLoad P jStar F s b Y hsumm
  have hBle : B ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
        * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y))
      * Real.sqrt (2 * EJ) := by
    dsimp only [B]
    have hTle : Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n)
        ≤ Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y) :=
      Real.sqrt_le_sqrt hsum_le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hTle (Real.sqrt_nonneg _)) hK)
      (Real.sqrt_nonneg _)
  refine ⟨hpair.1, ?_⟩
  calc |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P| ≤ B := hpair.2
    _ ≤ K * (Real.sqrt (∑' n : ℕ, (3 : ℝ) ^ (-((n : ℝ) / 2)))
          * Real.sqrt ((3 : ℝ) ^ ((3 : ℝ) / 2) * respSourceLoad P jStar F s b Y))
        * Real.sqrt (2 * EJ) := hBle

end

end Homogenization.HighContrast.Multiscale
