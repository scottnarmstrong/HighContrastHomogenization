import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakTailCellPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakTailCarrier
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakPrimalBranches
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakSummable
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCarrierInputs
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakParentIntegrable

/-!
# The two tail branches of the cell-average estimate, adjoint sign

The cell-average estimate `e.response.weak.estimate` bounds the normalized scale-average seminorm
of the recentred, metric-transported subcell averages of the doubled optimizer field, in two
branches according to the size of the all-scale maximum `M = respAllScaleMax P γ jStar F t a`.
This module is the adjoint twin of `h6a_tailBranches_minus`: the parent optimizer is attached to
the transposed recentred response coefficient `respCoeffPlus F a`, and the reference sample is the
adjoint normalised block `respEhatPlus`.

Every input of the older-scale branch is composed here once at the estimate's own carriers: the
per-cell bound `h6a_tailCell_of_bridge_plus`, the generic per-scale assembly `h6a_scaleTail_of_inputs`
instantiated at the adjoint coefficient, the summability `h6a_summable_centred`, and the
integrability and nonnegativity inputs.  The abstract branch splitting `h6a_primal_branches` then
turns the per-scale bound into the two printed branch bounds.

The per-scale family is `M_0^{1/2} · ((X)_{z + U_{t-n}} − (X)_{U_t})`, the transported recentring of
the parent optimizer field `X = (∇v, b ∇v)`.  On `1 < M` the whole series is absorbed by the
older-scale term; on `M ≤ 1` only the scales beyond a window `H` are absorbed and the first `H + 1`
scales remain as an explicit head sum.
-/

open Homogenization.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

/-- **The two older-scale branches of the cell-average estimate, adjoint sign.**  For an
invertible selected grid, a generation `t`, a parent harmonic optimizer attached to the transposed
recentred response coefficient, and the pointwise elliptic data of the parent and normalized
blocks, the normalized seminorm of the recentred transported optimizer field obeys the bad-branch
bound `16 / (1 - respRho γ) · K · √M · ℰ` when `1 < M` and the good-branch bound
`∑_{n ≤ H} 3 ^ (-(n / 2)) S n + 16 / (1 - respRho γ) · K · 3 ^ (-(respAlpha γ H)) · ℰ` when
`M ≤ 1`, where `K = √(‖(Ehat_t^+)_+‖)`, `ℰ` is the weak optimizer energy, and `S n` is the
depth-`n` scale average. -/
theorem h6a_tailBranches_plus (P : Measure (CoeffSpace d)) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hm : (explicitCanonicalMetric F).PosDef)
    (hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef)
    (hEhat : (toFullBlockMat (respEhatPlus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))}) :
    (1 < respAllScaleMax P γ jStar F t a →
        (3 : ℝ) ^ (-((t : ℝ) / 2)) *
            besovSeminorm t (fun n w =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverageFamily (respGrid jStar F) t
                    (optimizerField (respCoeffPlus F a) u) n w -
                  cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
          ≤ 16 / (1 - respRho γ) *
              Real.sqrt
                (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
              Real.sqrt (respAllScaleMax P γ jStar F t a) *
              weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u) ∧
    (respAllScaleMax P γ jStar F t a ≤ 1 →
        (3 : ℝ) ^ (-((t : ℝ) / 2)) *
            besovSeminorm t (fun n w =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverageFamily (respGrid jStar F) t
                    (optimizerField (respCoeffPlus F a) u) n w -
                  cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
          ≤ (∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) *
                Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                  ∑ w ∈ triadicIndexBox d n,
                    blockVecDot
                      (blockMatVecMul (blockSqrt (respM0 F))
                        (cellAverageFamily (respGrid jStar F) t
                            (optimizerField (respCoeffPlus F a) u) n w -
                          cellAverage (respCell jStar F t)
                            (optimizerField (respCoeffPlus F a) u)))
                      (blockMatVecMul (blockSqrt (respM0 F))
                        (cellAverageFamily (respGrid jStar F) t
                            (optimizerField (respCoeffPlus F a) u) n w -
                          cellAverage (respCell jStar F t)
                            (optimizerField (respCoeffPlus F a) u)))))
            + 16 / (1 - respRho γ) *
                Real.sqrt
                  (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
                (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) *
                weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u) := by
  classical
  obtain ⟨hmem1, hmem2⟩ :=
    h6a_memVectorL2_optimizerField_respCoeffPlus_cell (respGrid jStar F) hgrid t F a u
  have hK : 0 ≤ Real.sqrt
      (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) :=
    Real.sqrt_nonneg _
  have hEn : 0 ≤ weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u :=
    Real.sqrt_nonneg _
  have hM : 0 ≤ respAllScaleMax P γ jStar F t a := by
    have hSpecBound_nonneg : ∀ Hb : BlockMat d, 0 ≤ blockSpecBound Hb :=
      fun Hb => Real.sInf_nonneg fun _ hx => hx.1
    refine Real.sSup_nonneg ?_
    rintro y ⟨n, z, _hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hSpecBound_nonneg _)
  have hsum := h6a_summable_centred (respGrid jStar F) hgrid t (blockSqrt (respM0 F))
    (optimizerField (respCoeffPlus F a) u) hmem1 hmem2
  have hscale : ∀ n : ℕ,
      Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffPlus F a) u) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u))))
      ≤ Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) u := by
    intro n
    have hcell := h6a_tailCell_of_bridge_plus P γ jStar F t hgrid a n u hm hEmean hEhat hM0 hbdd
    have h1 : ∀ j : Fin d, IntegrableOn
        (fun x => (optimizerField (respCoeffPlus F a) u x).1 j) (respCell jStar F t) :=
      fun j => (h6a_integrableOn_optimizerField_respCoeffPlus_cell
        (respGrid jStar F) hgrid t F a u j).1
    have h2 : ∀ j : Fin d, IntegrableOn
        (fun x => (optimizerField (respCoeffPlus F a) u x).2 j) (respCell jStar F t) :=
      fun j => (h6a_integrableOn_optimizerField_respCoeffPlus_cell
        (respGrid jStar F) hgrid t F a u j).2
    have hnn := h6a_energyDensity_average_nonneg_plus (respGrid jStar F) hgrid t F a u
    have hintE := h6a_integrableOn_energyDensity_respCoeffPlus (respGrid jStar F) hgrid t F a u
    have hmean := h6a_cellAverage_parent_eq_avg_subcells (respGrid jStar F) hgrid t n
      (optimizerField (respCoeffPlus F a) u) h1 h2
    have hvar := h6a_scaleTerm_centred_le (respGrid jStar F) t n (blockSqrt (respM0 F))
      (optimizerField (respCoeffPlus F a) u) hmean.1 hmean.2
    have hpart := h6a_parent_energy_partition_cell (respGrid jStar F) hgrid t n
      (respCoeffPlus F a) u hnn hintE
    have hKp : 0 ≤ Real.sqrt
        (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))) :=
      Real.sqrt_nonneg _
    have hBp : 0 ≤ 1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
        (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) := by
      have hs : 0 ≤ Real.sqrt (respAllScaleMax P γ jStar F t a) := Real.sqrt_nonneg _
      have hp : 0 ≤ (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) :=
        (Real.rpow_pos_of_pos (by norm_num) _).le
      linarith only [mul_nonneg hs hp]
    exact h6a_scaleTail_of_inputs (respGrid jStar F) t n (blockSqrt (respM0 F))
      (respCoeffPlus F a) u
      (Real.sqrt (blockSpecBound (normalizedBlock (respEhatPlus P jStar F t) (respM0 F))))
      (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
        (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))
      hKp hBp hvar hcell hpart
  exact h6a_primal_branches hγ t H
    (fun n w => blockMatVecMul (blockSqrt (respM0 F))
      (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffPlus F a) u) n w -
        cellAverage (respCell jStar F t) (optimizerField (respCoeffPlus F a) u)))
    hK hEn hM hsum hscale

end

end Homogenization.HighContrast.Multiscale
