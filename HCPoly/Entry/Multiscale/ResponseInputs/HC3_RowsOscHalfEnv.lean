import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsOscHalfDom
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsOscEnv

/-!
# The oscillation half of the cutoff-mean row with the envelope supplied

`HC3_RowsOscHalfDom` bounds the oscillation half of the cutoff-mean row of `p.response.transfer`
by the source load, from a pathwise vanishing remainder and an increment envelope with four
properties.  `HC3_RowsOscEnv` builds that envelope out of the data the row already carries: the
cutoff weights, the head energies and the cell energies of the generation cells.  This module puts
the two together, so that the oscillation half consumes only the carriers' own inputs and no
envelope has to be exhibited at the call site.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The oscillation half of the cutoff-mean row, with the envelope built in.**  The hypotheses
of `integrable_and_abs_integral_sub_cellPart_le_descendant_load` with its four envelope conditions
removed: the Young splitting of the Cauchy--Schwarz product of the head energy and the cell energy
supplies them from the weight bound `hθ`, the pairing bound `hbd`, the annealed bounds `hGsq` and
`hDval` and the source-load summability `hsumm` that the row already carries. -/
theorem integrable_and_abs_integral_sub_cellPart_le_descendant_load_of_carriers {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (s : ℤ)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d)
    (Phi Tcell : CoeffSpace d → ℝ) (inc rem : ℕ → CoeffSpace d → ℝ)
    (Z : ℕ → Finset (Fin d → ℤ)) (θ : ℕ → (Fin d → ℤ) → ℝ)
    (pairing G D : ℕ → (Fin d → ℤ) → CoeffSpace d → ℝ) (K EJ : ℝ)
    (hK : 0 ≤ K) (hEJ : 0 ≤ EJ)
    (hdec : ∀ (N : ℕ) (a : CoeffSpace d),
      Phi a = Tcell a + (∑ n ∈ Finset.range N, inc n a) + rem N a)
    (hincdef : ∀ (n : ℕ) (a : CoeffSpace d),
      inc n a = ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a)
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
  classical
  set L : ℕ → ℝ := fun n =>
    (((triadicIndexBox d (n + 1)).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d (n + 1),
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P
                (adaptedCellAtCenter (respGrid jStar F) (s - ((n + 1 : ℕ) : ℤ)) z) b).lowerRight
              Y.2))) ^ 2 with hLdef
  set g : ℕ → ℝ := fun n =>
    (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
      ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ z ∈ triadicIndexBox d n,
          (Real.sqrt (vecDot Y.1 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
                Y.1)) +
            Real.sqrt (vecDot Y.2 (matVecMul
                (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
                Y.2))) ^ 2) with hgdef
  -- The layer weights shift by one generation, so the layer series is summable.
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
    rw [hw, hLdef, hgdef]
    ring
  have hsumL : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n := by
    have hg1 : Summable (fun n : ℕ => g (n + 1)) := (summable_nat_add_iff 1).2 hsumm
    exact Summable.congr (Summable.mul_left ((3 : ℝ) ^ ((3 : ℝ) / 2)) hg1)
      fun n => (hweight n).symm
  have henv := aeSummable_and_integrable_tsum_descendantEnvelope P Z G D L K EJ hK hD
    hGsq hDval hFint hDint hsumL
  refine integrable_and_abs_integral_sub_cellPart_le_descendant_load P jStar F s b Y Phi Tcell
    inc rem Z θ pairing G D (descendantEnvelope Z G D K) K EJ hK hEJ hdec hincdef
    (fun n a => descendantEnvelope_nonneg Z G D K hK hD n a) ?_ henv.1 henv.2 hrem0 hθ hG hD hbd
    hGsq hDval hPhiM hT hincI hFint hDint hMidint hPint hsumm
  intro n a
  rw [hincdef n a]
  exact abs_flat_weighted_pairing_le_descendantEnvelope Z θ pairing G D K hK hθ hG hD hbd n a

end

end Homogenization.HighContrast.Multiscale
