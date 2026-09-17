import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportBridgeApply
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportXiDischarge
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportXiLp
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportWeakInputs
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportScaleWeight
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportBesov
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportP1Arith
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportFluxCube
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportAffine
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportState
import HCPoly.Entry.Multiscale.ResponseInputs.HC2a_ReferenceCubePullback
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Entry.Multiscale.ResponseInputs.RecentreCore
import HCPoly.Entry.Multiscale.Initial.GeometricMean
import HCPoly.Entry.Geometry.LoewnerCongruence
import HCPoly.Entry.Setup.SpectralBound

/-!
# The inequality half of the pathwise cutoff bound

The negative-Besov duality bound of the cutoff argument (`AK.HC` Lemma A.1, (A.4)) pairs the
centred pulled-back potential against the pulled-back flux defect with the pulled-back cutoff
weight field.  Its two negative-Besov inputs are bounded by the scale-average seminorm of the
`M_0^{1/2}`-transported, recentred cell averages, and its four coefficients are bounded by the
cutoff class, the scale weights of the reference cube and the dimensional Frobenius product
`Frob₁ · Frob₂ ≤ 3 d²`.  The present file carries out the whole bookkeeping and concludes the
pathwise estimate `e.response.cutoff.estimate` in the exact shape consumed by the annealed
reduction: an explicit dimensional constant (depending only on the dimension and the universal
cutoff profile constant) times the scale weight `3^{-t}` times the square of the scale-average
seminorm of the recentred doubled optimizer state.

The constant is kept explicit and no existential is introduced.
-/

open Homogenization.HighContrast (matSqrt matSqrt_eq matSqrt_spec)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal

noncomputable section

/-- **The pathwise cutoff pairing bound in the shape of the annealed estimate.**  For a doubled
block `F` whose canonical metric is positive definite, a reference cube `Q = originCube d t`, a
cutoff `φ` in the response cutoff class, and a coefficient `b` that agrees almost everywhere on
the adapted cell with a uniformly elliptic field, the absolute cube average of the pulled-back
flux defect against the centred pulled-back potential times the pulled-back cutoff gradient is
bounded by an explicit dimensional constant times the scale weight `3^{-t}` times the square of
the scale-average seminorm of the recentred `M_0^{1/2}`-transported doubled optimizer state.  This
is the inequality half of the pathwise form of `e.response.cutoff.estimate`; it is the duality
bound `AK.HC` Lemma A.1, (A.4) with all four coefficient families and both negative-Besov inputs
discharged. -/
theorem abs_cubeAverage_pullback_pairing_le_besov_sq
    {d : ℕ} [NeZero d] {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    {b : CoeffField d}
    (hb : ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        b =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (u : AHarmonicFunction b (respCell jStar F t)) (Y : BlockVec d)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff (respGrid jStar F) t φ) :
    |cubeAverage (originCube d t)
        (fun y => vecDot
          (matVecMul (respGrid jStar F)⁻¹
            ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
          (((respCenteredPullbackH1 hjStar hm t b u Y y
              - cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
            scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) y :
              Vec d)))| ≤
      (((2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
            96 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          ((((d : ℝ) * Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d *
                (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
            ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2)))) *
        (3 * (d : ℝ) ^ 2)) *
      ((3 : ℝ) ^ (-(t : ℝ)) *
        besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField b u) - Y)) ^ 2) := by
  classical
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ := hb
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  -- The pulled-back flux defect is square integrable on the reference cube.
  have hflux : MemLp (fun y => matVecMul (respGrid jStar F)⁻¹
      ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2)) 2
      (normalizedCubeMeasure (originCube d t)) :=
    memLp_two_pullback_flux_of_exists hq t ⟨lam, Lam, f, hlam, hle, hEll, hbf⟩ u Y
  -- The weight field and its three hypotheses.
  set ξ : Vec d → Vec d :=
    scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) with hξdef
  have hξcont : Continuous ξ := by
    rw [hξdef]
    exact continuous_pi (fun i => (contDiff_xi_of_isResponseCutoff hφ i).continuous)
  have hξLp : MemLp ξ ∞ (normalizedCubeMeasure (originCube d t)) := by
    rw [hξdef]
    exact memLp_top_normalizedCubeMeasure_of_norm_le (originCube d t)
      (by simpa only [hξdef] using hξcont.aestronglyMeasurable)
      (fun y => norm_xi_le_of_isResponseCutoff hφ y)
  have hξ : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i) := by
    intro i
    rw [hξdef]
    exact contDiff_xi_of_isResponseCutoff hφ i
  set B : ℝ := 1024 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t)
    with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h3 : 0 < (3 : ℝ) ^ (-2 * t) := zpow_pos (by norm_num) _
    have hΘ : 0 ≤ responseCutoffProfileConst := responseCutoffProfileConst_pos.le
    positivity
  have hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet (originCube d t),
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B := by
    intro i z _
    rw [hξdef, hBdef]
    exact norm_fderiv_xi_le_of_isResponseCutoff hφ i z
  -- The scale-average seminorm of the recentred doubled optimizer state.
  set A : ℝ := besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
          (optimizerField b u) - Y)) with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact besovSeminorm_nonneg t _
  -- The two Frobenius factors of the metric pullback.
  set Frob₁ : ℝ := Real.sqrt (Book.Ch02.matrixFrobeniusNormSq
      (matTranspose (respGrid jStar F) * (matSqrt (explicitCanonicalMetric F))⁻¹)) with hFrob1def
  set Frob₂ : ℝ := Real.sqrt (Book.Ch02.matrixFrobeniusNormSq
      ((respGrid jStar F)⁻¹ * matSqrt (explicitCanonicalMetric F))) with hFrob2def
  have hFrob1nonneg : 0 ≤ Frob₁ := by rw [hFrob1def]; exact Real.sqrt_nonneg _
  have hFrob2nonneg : 0 ≤ Frob₂ := by rw [hFrob2def]; exact Real.sqrt_nonneg _
  -- `blockSqrt (respM0 F)` acts as the diagonal metric scaling.
  have hSS : matSqrt (explicitCanonicalMetric F) * matSqrt (explicitCanonicalMetric F) = explicitCanonicalMetric F :=
    (matSqrt_spec hm.posSemidef).2
  have hSmPD : (matSqrt (explicitCanonicalMetric F)).PosDef := GeoMean.matSqrtPosDef' hm
  have hinv : (matSqrt (explicitCanonicalMetric F))⁻¹ * (matSqrt (explicitCanonicalMetric F))⁻¹ =
      (explicitCanonicalMetric F)⁻¹ := by
    rw [← Matrix.mul_inv_rev, hSS]
  have hdiag : toFullBlockMat (respM0 F) =
      Matrix.fromBlocks (explicitCanonicalMetric F) 0 0 (explicitCanonicalMetric F)⁻¹ := by
    ext (i | i) (j | j) <;> rfl
  have hBpsd : (Matrix.fromBlocks (matSqrt (explicitCanonicalMetric F)) 0 0
      (matSqrt (explicitCanonicalMetric F))⁻¹).PosSemidef := by
    let _ := hSmPD.isUnit.invertible
    exact (Matrix.PosDef.fromBlocks₁₁ (A := matSqrt (explicitCanonicalMetric F)) (0 : Mat d)
      ((matSqrt (explicitCanonicalMetric F))⁻¹) hSmPD).mpr (by simpa using hSmPD.inv.posSemidef)
  have hmat : matSqrt (toFullBlockMat (respM0 F)) =
      Matrix.fromBlocks (matSqrt (explicitCanonicalMetric F)) 0 0
        (matSqrt (explicitCanonicalMetric F))⁻¹ := by
    refine matSqrt_eq (d124_respM0_posDef hm).posSemidef hBpsd ?_
    rw [hdiag, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hSS, hinv]
  have hsqrt_block : blockSqrt (respM0 F) =
      (⟨matSqrt (explicitCanonicalMetric F), 0, 0, (matSqrt (explicitCanonicalMetric F))⁻¹⟩ : BlockMat d) := by
    unfold blockSqrt
    rw [hmat]
    have hfull : toFullBlockMat (⟨matSqrt (explicitCanonicalMetric F), 0, 0,
        (matSqrt (explicitCanonicalMetric F))⁻¹⟩ : BlockMat d) =
        Matrix.fromBlocks (matSqrt (explicitCanonicalMetric F)) 0 0
          (matSqrt (explicitCanonicalMetric F))⁻¹ := by
      ext (i | i) (j | j) <;> rfl
    rw [← hfull, ofFullBlockMat_toFullBlockMat]
  have hscaled : ∀ Z : BlockVec d, blockMatVecMul (blockSqrt (respM0 F)) Z =
      (matVecMul (matSqrt (explicitCanonicalMetric F)) Z.1,
        matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ Z.2) := by
    intro Z
    rw [hsqrt_block]
    have hz1 : matVecMul (0 : Mat d) Z.2 = 0 := by funext i; simp [matVecMul]
    have hz2 : matVecMul (0 : Mat d) Z.1 = 0 := by funext i; simp [matVecMul]
    refine Prod.ext ?_ ?_
    · show matVecMul (matSqrt (explicitCanonicalMetric F)) Z.1 + matVecMul (0 : Mat d) Z.2 =
          matVecMul (matSqrt (explicitCanonicalMetric F)) Z.1
      rw [hz1, add_zero]
    · show matVecMul (0 : Mat d) Z.1 + matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ Z.2 =
          matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ Z.2
      rw [hz2, zero_add]
  -- The scale-average seminorm of the weak input is the target seminorm.
  have hfam : (fun x : Vec d =>
        (matVecMul (matSqrt (explicitCanonicalMetric F)) (optimizerField b u x - Y).1,
          matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ (optimizerField b u x - Y).2)) =
      fun x => blockMatVecMul (blockSqrt (respM0 F)) (optimizerField b u x - Y) := by
    funext x
    exact (hscaled (optimizerField b u x - Y)).symm
  have hAeq : besovSeminorm t (cellAverageFamily (respGrid jStar F) t (fun x =>
      (matVecMul (matSqrt (explicitCanonicalMetric F)) (optimizerField b u x - Y).1,
        matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ (optimizerField b u x - Y).2))) = A := by
    rw [hfam, hAdef]
    refine besovSeminorm_congr (fun n w hw => ?_)
    have hsub : adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w ⊆ respCell jStar F t :=
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw
    have hfin : volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) ≠ ⊤ :=
      Geometry.volume_adaptedCellAtCenter_ne_top (respGrid jStar F) _ w
    have hvolr : (volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)).toReal =
        |(respGrid jStar F).det| * ((3 : ℝ) ^ (t - (n : ℤ))) ^ d := by
      rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (abs_nonneg _),
        ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - (n : ℤ)))]
    have hvol : (volume (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)).toReal ≠ 0 := by
      rw [hvolr]
      have hdet : 0 < |(respGrid jStar F).det| :=
        abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det _).mp hq))
      positivity
    have : IsFiniteMeasure (volume.restrict (respCell jStar F t)) := by
      simpa [volumeMeasureOn] using!
        (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
    obtain ⟨h1i, h2i⟩ :=
      memLp_two_coords_optimizerField_sub_const (q := respGrid jStar F) hq t hEll hbf u 0
    have h1i' : ∀ i, MemLp (fun x => (optimizerField b u x).1 i) 2
        (volume.restrict (respCell jStar F t)) := fun i => by
      simpa only [sub_zero] using! h1i i
    have h2i' : ∀ i, MemLp (fun x => (optimizerField b u x).2 i) 2
        (volume.restrict (respCell jStar F t)) := fun i => by
      simpa only [sub_zero] using! h2i i
    have hI1 : ∀ i, IntegrableOn (fun x => (optimizerField b u x).1 i)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun i => by
      have h : IntegrableOn (fun x => (optimizerField b u x).1 i) (respCell jStar F t) :=
        (h1i' i).integrable one_le_two
      exact h.mono_set hsub
    have hI2 : ∀ i, IntegrableOn (fun x => (optimizerField b u x).2 i)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) := fun i => by
      have h : IntegrableOn (fun x => (optimizerField b u x).2 i) (respCell jStar F t) :=
        (h2i' i).integrable one_le_two
      exact h.mono_set hsub
    exact cellAverage_blockMatVecMul_sub_const hfin hvol (blockSqrt (respM0 F)) Y hI1 hI2
  -- The two negative-Besov inputs, rewritten with the target seminorm.
  have hgradWeak : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
      (respCenteredPullbackH1 hjStar hm t b u Y).grad ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₁ * A := by
    intro N
    have h := cubeBesov_respCenteredPullbackH1_grad_le hjStar hm t hEll hbf u Y N
    rw [hFrob1def]
    rwa [hAeq] at h
  have hfluxWeak : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
      (fun y => matVecMul (respGrid jStar F)⁻¹
        ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2)) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₂ * A := by
    intro N
    have h := cubeBesov_pullback_fluxDefect_le hjStar hm t hEll hbf u Y N
    rw [hFrob2def]
    rwa [hAeq] at h
  -- The duality bound at the pulled-back data.
  have hbridge := abs_cubeAverage_pullback_pairing_le (jStar := jStar) hjStar hm t b u Y
    (φ := φ) (B := B) (gradWeak := (3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₁ * A)
    (fluxWeak := (3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₂ * A)
    hB0 hξLp hξ hderiv hflux hgradWeak hfluxWeak
  -- The four coefficients of the duality bound.
  set gradCoeff : ℝ := 2 * cubeScaleFactor (originCube d t) * B + 3 *
      cubeLpNorm (originCube d t) ∞ ξ with hgcdef
  set fluxCoeff : ℝ :=
      ((Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) *
          (3 : ℝ) ^ ((d : ℝ) + 1)) * (Fintype.card (Fin d) : ℝ)) *
        ((Fintype.card (Fin d) : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + (1 - 1 / 2)) *
            cubeBesovScaleWeight (-(1 - 1 / 2 - 1 / 2)) (originCube d t))) with hfcdef
  set scaledGrad : ℝ := cubeBesovScaleWeight (-(1 / 2)) (originCube d t) *
      ((3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₁ * A) with hsgdef
  set scaledFlux : ℝ := cubeBesovScaleWeight (-(1 / 2)) (originCube d t) *
      ((3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₂ * A) with hsfdef
  set K : ℝ := 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
      96 * (d : ℝ) ^ 2 * responseCutoffProfileConst with hKdef
  set L : ℝ := ((((d : ℝ) * Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
      ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2))) with hLdef
  have hfluxCoeff_eq : fluxCoeff = L := by
    rw [hfcdef, hLdef]
    have hPc : Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) =
        (d : ℝ) * Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d := by
      simp only [Book.Ch01.Legacy.fullVectorPoincareConstant,
        Homogenization.fullVectorPoincareCubeConstant,
        Homogenization.cubeFullVectorPoincareUniformAnalyticConstant]
    rw [hPc]
    rw [show (Fintype.card (Fin d) : ℝ) = (d : ℝ) by simp]
    rw [show (-(1 - 1 / 2 - 1 / 2) : ℝ) = 0 by norm_num,
      cubeBesovScaleWeight_zero_originCube]
    rw [show (d : ℝ) + (1 - 1 / 2) = (d : ℝ) + 1 / 2 by norm_num]
    ring
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have hΘ : 0 < responseCutoffProfileConst := responseCutoffProfileConst_pos
    positivity
  have hL0 : 0 ≤ L := by
    rw [hLdef]
    have hCZ : 0 ≤ Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d :=
      Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
    positivity
  have hgc0 : 0 ≤ gradCoeff := by
    rw [hgcdef]
    have hcs : 0 ≤ cubeScaleFactor (originCube d t) := by
      rw [cubeScaleFactor_originCube]
      exact Real.rpow_nonneg (by norm_num) _
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcs) hB0)
      (mul_nonneg (by norm_num) (cubeLpNorm_nonneg (originCube d t) ∞ ξ))
  have hfc0 : 0 ≤ fluxCoeff := hfluxCoeff_eq.symm ▸ hL0
  have hxiBound : cubeLpNorm (originCube d t) ∞ ξ ≤
      32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) := by
    rw [hξdef]
    have hK0' : 0 ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) := by
      have hΘ : 0 < responseCutoffProfileConst := responseCutoffProfileConst_pos
      positivity
    have hpow : (3 : ℝ) ^ (-t) = (3 : ℝ) ^ (-(t : ℝ)) := by
      rw [← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    exact cubeLpNorm_top_le_of_norm_le (originCube d t) hK0'
      (fun y => by
        have h := norm_xi_le_of_isResponseCutoff hφ y
        rwa [hpow] at h)
  have hcancel : (3 : ℝ) ^ ((t : ℝ) / 2) * (3 : ℝ) ^ (-((t : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [show (t : ℝ) / 2 + -((t : ℝ) / 2) = 0 by ring, Real.rpow_zero]
  have hscaledGrad_eq : scaledGrad = Frob₁ * A := by
    rw [hsgdef, cubeBesovScaleWeight_neg_half_originCube]
    calc (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₁ * A)
        = ((3 : ℝ) ^ ((t : ℝ) / 2) * (3 : ℝ) ^ (-((t : ℝ) / 2))) * (Frob₁ * A) := by
          ring
      _ = Frob₁ * A := by rw [hcancel, one_mul]
  have hscaledFlux_eq : scaledFlux = Frob₂ * A := by
    rw [hsfdef, cubeBesovScaleWeight_neg_half_originCube]
    calc (3 : ℝ) ^ ((t : ℝ) / 2) * ((3 : ℝ) ^ (-((t : ℝ) / 2)) * Frob₂ * A)
        = ((3 : ℝ) ^ ((t : ℝ) / 2) * (3 : ℝ) ^ (-((t : ℝ) / 2))) * (Frob₂ * A) := by
          ring
      _ = Frob₂ * A := by rw [hcancel, one_mul]
  have hsg0 : 0 ≤ scaledGrad := hscaledGrad_eq.symm ▸ mul_nonneg hFrob1nonneg hA0
  have hsf0 : 0 ≤ scaledFlux := hscaledFlux_eq.symm ▸ mul_nonneg hFrob2nonneg hA0
  have hGf : Frob₁ * Frob₂ ≤ 3 * (d : ℝ) ^ 2 := by
    rw [hFrob1def, hFrob2def]
    exact explicitRoundedGrid_metricFrobenius_product_le jStar hjStar (explicitCanonicalMetric F) hm
  have hsplit : (3 : ℝ) ^ (t : ℝ) * (3 : ℝ) ^ (-2 * t) = (3 : ℝ) ^ (-(t : ℝ)) := by
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have hterm1 : 2 * (3 : ℝ) ^ (t : ℝ) * B =
      2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-(t : ℝ)) := by
    rw [hBdef]
    calc 2 * (3 : ℝ) ^ (t : ℝ) *
          (1024 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-2 * t))
        = 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 *
            ((3 : ℝ) ^ (t : ℝ) * (3 : ℝ) ^ (-2 * t)) := by ring
      _ = 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 *
            (3 : ℝ) ^ (-(t : ℝ)) := by rw [hsplit]
  have hterm2 : 3 * cubeLpNorm (originCube d t) ∞ ξ ≤
      96 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) := by
    calc 3 * cubeLpNorm (originCube d t) ∞ ξ
        ≤ 3 * (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ))) :=
          mul_le_mul_of_nonneg_left hxiBound (by norm_num)
      _ = 96 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) := by ring
  have hgradCoeffK : gradCoeff ≤ K * (3 : ℝ) ^ (-(t : ℝ)) := by
    rw [hKdef]
    rw [hgcdef, cubeScaleFactor_originCube]
    calc 2 * (3 : ℝ) ^ (t : ℝ) * B + 3 * cubeLpNorm (originCube d t) ∞ ξ
        ≤ 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 * (3 : ℝ) ^ (-(t : ℝ)) +
            96 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(t : ℝ)) :=
          add_le_add (le_of_eq hterm1) hterm2
      _ = (2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
            96 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
            (3 : ℝ) ^ (-(t : ℝ)) := by ring
  -- Assemble: duality bound, then the constant arithmetic.
  have hbridge' : |cubeAverage (originCube d t)
      (fun y => vecDot
        (matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (((respCenteredPullbackH1 hjStar hm t b u Y y
            - cubeAverage (originCube d t)
                (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
          scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) y :
            Vec d)))| ≤ (gradCoeff * fluxCoeff) * (scaledGrad * scaledFlux) := by
    refine hbridge.trans_eq ?_
    simp only [hgcdef, hfcdef, hsgdef, hsfdef]
    ring
  have harith := mul_le_const_mul_rpow_mul_sq (d := d) t hA0 hFrob1nonneg hFrob2nonneg hK0 hL0
    hgc0 hfc0 hsg0 hsf0 hgradCoeffK hfluxCoeff_eq.le hscaledGrad_eq.le
    hscaledFlux_eq.le hGf
  have htarget : (K * L * (3 * (d : ℝ) ^ 2)) * ((3 : ℝ) ^ (-(t : ℝ)) * A ^ 2) =
      (((2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
            96 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
          ((((d : ℝ) * Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d *
                (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
            ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2)))) *
        (3 * (d : ℝ) ^ 2)) *
      ((3 : ℝ) ^ (-(t : ℝ)) *
        besovSeminorm t (fun n z =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
              (optimizerField b u) - Y)) ^ 2) := by
    rw [hAdef, hKdef, hLdef]
  exact hbridge'.trans (harith.trans_eq htarget)

end

end Homogenization.HighContrast.Multiscale
