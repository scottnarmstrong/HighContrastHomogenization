import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedSwarmH7Helpers

/-!
# The source-load series converges at every dual vector

`RespLoadBound` carries the summability of the generation summands of `L_s^∓` only at the two
annealed means `Y^∓`.  The oscillation half of the cutoff-mean row of `p.response.transfer` reads
the same series once per coordinate direction, at the dual vectors `(0, δ_i)` and `(δ_i, 0)`, so it
needs the summability at an arbitrary `Y`.

Nothing in the printed proof of the source-load bound restricts the dual vector: the `Y`-dependence
enters only through the quadratic form `⟨Y, M_0 Y⟩`, which is a finite number for every `Y`.  What
carries the convergence is the scale-wise Loewner envelope
`E[A(V_{s-n,z}; a)] ≤ C Π e(m)^2 3^{γ(j_*-(s-n))_+} E_s` of `h7_annealedBlock_le_adaptedMean`
together with the calibration `Ehat_s^∓ ≤ c M_0`; against the weight `3^{-3n/2}` the resulting
series is geometric of ratio `3^{γ-3/2} < 1`.  This module records that, for both signs.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  annealedBlock aspectRatio blockScale)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The source-load series converges at every dual vector, for both signs.**  Under the standing
data of the response window -- stationarity, coarse ellipticity, the source threshold on `j_*`, the
invertible rounded grid, the window inclusion and the calibration of `Ehat_s^∓` against `M_0` -- the
generation summands of the source load are summable at *every* `Y`, not only at the annealed means
`Y^∓` of `RespLoadBound`. -/
theorem exists_summable_respSourceLoadSummand_all (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (E : BlockMat d) (Ψ : ℝ → ℝ)
        (Kg : ℝ) (Src : CoeffSpace d → ℝ),
        IsStationaryLaw P → CoarseEllipticityDagger P γ E Ψ Kg Src →
        ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar → ⌈Csrc * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) →
        ∀ F : BlockMat d, (toFullBlockMat F).PosDef → (explicitCanonicalMetric F).PosDef →
        ∀ s : ℤ, (jStar : ℤ) ≤ s →
          HighContrast.adaptedCell (respGrid jStar F) s ⊆
            HighContrast.centeredCube d (2 * (jStar : ℤ)) →
        ∀ cM : ℝ, 0 ≤ cM →
          BlockMatLoewnerLE (respEhatMinus P jStar F s) (blockScale cM (respM0 F)) →
          BlockMatLoewnerLE (respEhatPlus P jStar F s) (blockScale cM (respM0 F)) →
        ∀ Y : BlockVec d,
          Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F) Y) ∧
            Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F) Y) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Csrc, Cb, hCsrc, hCb, hcell⟩ := h7_annealedBlock_le_adaptedMean d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P hP E Ψ Kg Src hstat hdag jStar hj hthr F hFfull hmF s hjs hwin cM hcM hEsM hEsP Y
  have : IsProbabilityMeasure P := hP
  have hqU : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hj hmF
  have hM0pd : Book.Ch02.BlockPosDef (respM0 F) := h7_respM0_blockPosDef hmF
  have hM0full : (toFullBlockMat (respM0 F)).PosDef :=
    Annealed.fullBlock_posDef_of_pos (h7_respM0_isSymm hmF) hM0pd
  -- the coarse block is entrywise integrable on every aligned adapted cell
  have hint : ∀ (k : ℤ) (y : Vec d),
      HasIntegrableCoarseBlock P (HighContrast.adaptedCellTranslate (respGrid jStar F) k y) :=
    fun k y => Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ Kg Src hstat hdag
      jStar hj (explicitCanonicalMetric F) hmF k y
  have hAsp : (1 : ℝ) ≤ aspectRatio E := Annealed.one_le_aspectRatio hdag
  have hecc0 : (0 : ℝ) ≤ ‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖ := by positivity
  -- the generation-wise scale factor of the Loewner envelope
  have hA0 : (0 : ℝ) ≤ Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) :=
    mul_nonneg (mul_nonneg hCb.le (by linarith)) hecc0
  set cfun : ℕ → ℝ := fun n =>
    Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0) * cM with hcfun
  have hcfun0 : ∀ n, 0 ≤ cfun n := by
    intro n
    exact mul_nonneg (mul_nonneg hA0 (Real.rpow_nonneg (by norm_num) _)) hcM
  -- the Loewner envelope of the annealed block of each signed family, generation by generation
  have hres : ∀ (G' : BlockMat d) (b : CoeffSpace d → CoeffField d),
      (∀ (k : ℤ) (z : Fin d → ℤ),
          annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) b
            = blockCongr G' (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z))) →
      BlockMatLoewnerLE (blockCongr G' (respMean P jStar F s)) (blockScale cM (respM0 F)) →
      ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
        BlockMatLoewnerLE
          (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b)
          (blockScale (cfun n) (respM0 F)) := by
    intro G' b hb hEs n z _
    rw [hb]
    have h1 := hcell P E Ψ Kg Src hstat hdag jStar hj hthr (explicitCanonicalMetric F) hmF s hjs hwin
      (s - (n : ℤ)) z
    have step1 := h7_blockCongr_mono G' h1
    rw [h7_blockCongr_blockScale] at step1
    have hfac0 : (0 : ℝ) ≤ Cb * aspectRatio E *
        (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
        (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0) :=
      mul_nonneg hA0 (Real.rpow_nonneg (by norm_num) _)
    have step2 := h7_blockScale_mono hEs hfac0
    refine fun V => le_trans (le_trans (step1 V) (step2 V)) ?_
    rw [h7_blockScale_blockScale]
  -- the geometric majorant of the weighted scale factors
  set M : ℝ := max 0 (blockVecDot Y (blockMatVecMul (respM0 F) Y)) with hMdef
  have hM0 : (0 : ℝ) ≤ M := le_max_left _ _
  have hYle : blockVecDot Y (blockMatVecMul (respM0 F) Y) ≤ M := le_max_right _ _
  have hr2lt : (3 : ℝ) ^ (γ - 3 / 2) < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    linarith [hγ.2]
  have hr2pos : (0 : ℝ) < (3 : ℝ) ^ (γ - 3 / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hsum : Summable fun n : ℕ =>
      (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * (cfun n * M)) := by
    have hgeo : Summable fun n : ℕ =>
        (4 * (Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) * cM * M)) *
          ((3 : ℝ) ^ (γ - 3 / 2)) ^ n :=
      (summable_geometric_of_lt_one hr2pos.le hr2lt).mul_left _
    refine hgeo.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (by norm_num) (mul_nonneg (hcfun0 n) hM0))
    · have hmaxle : max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0 ≤ (n : ℝ) := by
        refine max_le ?_ (Nat.cast_nonneg n)
        have hjsR : ((jStar : ℕ) : ℝ) ≤ ((s : ℤ) : ℝ) := by exact_mod_cast hjs
        push_cast
        linarith
      have hpowle : (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (((s - (n : ℤ)) : ℤ) : ℝ)) 0)
          ≤ (3 : ℝ) ^ (γ * (n : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        exact mul_le_mul_of_nonneg_left hmaxle hγ.1
      have hstep : cfun n ≤ Cb * aspectRatio E *
          (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) * (3 : ℝ) ^ (γ * (n : ℝ)) * cM := by
        rw [hcfun]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowle hA0) hcM
      have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hfinal : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * (cfun n * M))
          ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
              * (4 * ((Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
                  (3 : ℝ) ^ (γ * (n : ℝ)) * cM) * M)) := by
        refine mul_le_mul_of_nonneg_left ?_ hw0
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right hstep hM0
      refine hfinal.trans (le_of_eq ?_)
      have hmul : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (3 : ℝ) ^ (γ * (n : ℝ))
          = ((3 : ℝ) ^ (γ - 3 / 2)) ^ n := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
          show -((3 : ℝ) / 2) * (n : ℝ) + γ * (n : ℝ) = (γ - 3 / 2) * (n : ℝ) by ring,
          h7_pow_eq]
      calc (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
              * (4 * ((Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
                  (3 : ℝ) ^ (γ * (n : ℝ)) * cM) * M))
          = (4 * (Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
                cM * M)) *
              ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (3 : ℝ) ^ (γ * (n : ℝ))) := by ring
        _ = (4 * (Cb * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
                cM * M)) * ((3 : ℝ) ^ (γ - 3 / 2)) ^ n := by rw [hmul]
  -- the two signed congruences
  have hbMinus : ∀ (k : ℤ) (z : Fin d → ℤ),
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffMinus F)
        = blockCongr (respG F) (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z)) :=
    fun k z => h7_annealedBlockOf_respCoeffMinus_adapted (respGrid jStar F) hqU k
      (adaptedCellCenter (respGrid jStar F) k z) F hFfull (hint k _)
  set Gplus : BlockMat d :=
    ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)) with hGplus
  have hbPlus : ∀ (k : ℤ) (z : Fin d → ℤ),
      annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffPlus F)
        = blockCongr Gplus (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z)) := by
    intro k z
    have h : annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) k z) (respCoeffPlus F)
        = blockAdjoint (blockCongr (respG F)
            (annealedBlock P (adaptedCellAtCenter (respGrid jStar F) k z))) :=
      h7_annealedBlockOf_respCoeffPlus_adapted (respGrid jStar F) hqU k
        (adaptedCellCenter (respGrid jStar F) k z) F hFfull (hint k _)
    rw [h, blockAdjoint, h7_blockCongr_blockCongr, hGplus]
  have hEsPlus : BlockMatLoewnerLE (blockCongr Gplus (respMean P jStar F s))
      (blockScale cM (respM0 F)) := by
    have h := hEsP
    rw [respEhatPlus, blockAdjoint, respEhatMinus, h7_blockCongr_blockCongr] at h
    exact h
  constructor
  · exact (h7_respSourceLoad_le_of_loewner_scalewise P jStar F s (respCoeffMinus F) Y cfun M
      hcfun0 hM0 hmF hYle hsum (hres (respG F) (respCoeffMinus F) hbMinus hEsM)).1
  · exact (h7_respSourceLoad_le_of_loewner_scalewise P jStar F s (respCoeffPlus F) Y cfun M
      hcfun0 hM0 hmF hYle hsum (hres Gplus (respCoeffPlus F) hbPlus hEsPlus)).1

end

end Homogenization.HighContrast.Multiscale
