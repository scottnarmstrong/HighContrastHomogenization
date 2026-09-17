import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportP1Ineq
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportP1Ident
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportDischInt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportDischXi
import Homogenization.Geometry.CubeMeasure

/-!
# The pathwise cutoff pairing bound with every hypothesis discharged

The annealed cutoff bound `e.response.cutoff.estimate` is reduced by the frame theorems to the
deterministic pathwise estimate `hpath` on the adapted cell `respCell jStar F t`.  This file lands
that estimate as a single existential in the dimension: for every selected grid, every response
cutoff, every positive-definite block and every a.e.-elliptic representative of the coefficient,
the absolute volume average of the cutoff times the pairing of the centred doubled optimizer state
is at most a dimension-only constant times the scale weight `3 ^ (-t)` times the square of the
scale-average seminorm of the `M_0 ^ (1/2)`-transported recentred state.

The volume average is first identified with the centred cube average on the reference cube by the
integration by parts of the cutoff pairing (`AK.HC` Lemma A.1, (A.4)), the change of variables
`x = (respGrid jStar F) y` and the vanishing of the flux defect against the cutoff gradient; the
resulting cube average is then bounded by the negative-Besov duality bound with all four
coefficient families discharged.  The integrability side conditions of the identification are
supplied here: the flux defect against the cutoff gradient is `L²` on the reference cube because
the flux defect is `L²` and the cutoff gradient is essentially bounded, the centred potential
multiplied by that pairing is integrable because the pulled-back potential is `L²`, and the
centred-potential pairing on the cell is its change of variables.  The constant is the explicit
dimension-only constant of `abs_cubeAverage_pullback_pairing_le_besov_sq`, so it depends on no
other datum.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The pathwise cutoff pairing bound `e.response.cutoff.estimate` (`AK.HC` Lemma A.1, (A.4)) with
every hypothesis discharged, in the exact shape of the `hpath` hypothesis of
`exists_integral_abs_pairing_le_respWeak_of_pathwise`.  There is a dimension-only constant `C₀`
such that, for every grid depth `jStar`, block `F`, scale `t`, response cutoff `φ`, positive
definite canonical metric, coefficient `b` with an a.e.-elliptic representative on the adapted
cell and `b`-harmonic optimizer `u`, the absolute volume average on `respCell jStar F t` of the
cutoff times the pairing of the centred doubled optimizer state with `Y` is at most `C₀` times the
scale weight `3 ^ (-t)` times the square of the scale-average seminorm of the `M_0 ^ (1/2)`-scaled
recentred state. -/
theorem exists_pathwise_cutoff_pairing_bound (d : ℕ) [NeZero d] :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (jStar : ℕ) (F : BlockMat d) (t : ℤ) (φ : Vec d → ℝ),
        2 * d ≤ 3 ^ jStar → IsResponseCutoff (respGrid jStar F) t φ →
        (explicitCanonicalMetric F).PosDef →
        ∀ (b : CoeffField d) (Y : BlockVec d)
          (u : AHarmonicFunction b (respCell jStar F t)),
          (∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
            IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
              b =ᵐ[volumeMeasureOn (respCell jStar F t)] f) →
          |volumeAverage (respCell jStar F t) (fun x =>
              φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))| ≤
            C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
              blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                  (optimizerField b u) - Y)) ^ 2) := by
  set C₀ : ℝ :=
    (((2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
        96 * (d : ℝ) ^ 2 * responseCutoffProfileConst) *
      ((((d : ℝ) * Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
        ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2)))) *
      (3 * (d : ℝ) ^ 2)) with hC₀def
  have hC₀ : 0 ≤ C₀ := by
    rw [hC₀def]
    have hΘ : 0 ≤ responseCutoffProfileConst := responseCutoffProfileConst_pos.le
    have hΘ2 : 0 ≤ responseCutoffProfileConst ^ 2 := sq_nonneg _
    have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    have hCZ : 0 ≤ Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d :=
      Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
    have hp1 : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1) := Real.rpow_nonneg (by norm_num) _
    have hp2 : 0 ≤ (3 : ℝ) ^ ((d : ℝ) + 1 / 2) := Real.rpow_nonneg (by norm_num) _
    have hA : 0 ≤ 2048 * (d : ℝ) ^ 4 * responseCutoffProfileConst ^ 2 +
        96 * (d : ℝ) ^ 2 * responseCutoffProfileConst :=
      add_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hd 4)) hΘ2)
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hd 2)) hΘ)
    have hB : 0 ≤ (((d : ℝ) *
          Homogenization.Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
          ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1 / 2)) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hd hCZ) hp1) hd)
        (mul_nonneg hd hp2)
    exact mul_nonneg (mul_nonneg hA hB)
      (mul_nonneg (by norm_num) (sq_nonneg (d : ℝ)))
  refine ⟨C₀, hC₀, ?_⟩
  intro jStar F t φ hjStar hφ hm b Y u hb
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  set fl : Vec d → Vec d := fun y => matVecMul (respGrid jStar F)⁻¹
    ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2) with hfl
  set ξ : Vec d → Vec d :=
    scalarCutoffGradientField (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) with hξdef
  set w : Vec d → ℝ := (respCenteredPullbackH1 hjStar hm t b u Y).toFun with hw
  set g : Vec d → ℝ := fun x =>
    (u.toH1.toFun x - vecDot Y.1 x) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j)) with hg
  -- Square integrability of the pulled-back flux and of the cutoff gradient.
  have hflux : MemLp fl 2 (normalizedCubeMeasure (originCube d t)) := by
    simpa only [hfl] using! memLp_two_pullback_flux_of_exists hq t hb u Y
  have hξLp : MemLp ξ ∞ (normalizedCubeMeasure (originCube d t)) := by
    simpa only [hξdef] using memLp_top_xi_of_isResponseCutoff (respGrid jStar F) hφ
  have hξ2 : MemLp ξ 2 (normalizedCubeMeasure (originCube d t)) :=
    hξLp.mono_exponent le_top
  -- The normalized cube measure is a finite nonzero multiple of the restricted volume.
  have hc0 : ENNReal.ofReal ((cubeVolume (originCube d t))⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos (originCube d t)))
  have hctop : ENNReal.ofReal ((cubeVolume (originCube d t))⁻¹) ≠ ∞ := ENNReal.ofReal_ne_top
  -- Integrability on the reference cube of the flux defect against the cutoff gradient.
  have hcube_mu : Integrable (fun y => vecDot (fl y) (ξ y))
      (normalizedCubeMeasure (originCube d t)) := by
    have hsum := integrable_finsetSum (Finset.univ)
      (fun i _ => (hflux.eval i).integrable_mul (hξ2.eval i))
    simpa only [vecDot] using! hsum
  have hcube : IntegrableOn (fun y => vecDot (fl y) (ξ y)) (cubeSet (originCube d t)) := by
    show Integrable (fun y => vecDot (fl y) (ξ y))
      (volume.restrict (cubeSet (originCube d t)))
    have h := hcube_mu
    rw [normalizedCubeMeasure, cubeMeasure] at h
    exact (integrable_smul_measure hc0 hctop).mp h
  -- The pulled-back centred potential is `L²` on the reference cube.
  have hw_open : MemLp w 2 (volume.restrict (openCubeSet (originCube d t))) := by
    simpa only [hw] using (respCenteredPullbackH1 hjStar hm t b u Y).memL2
  have hw_vol : MemLp w 2 (volume.restrict (cubeSet (originCube d t))) := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d t)]
    exact hw_open
  have hw_mu : MemLp w 2 (normalizedCubeMeasure (originCube d t)) := by
    rw [normalizedCubeMeasure, cubeMeasure]
    exact hw_vol.smul_measure ENNReal.ofReal_ne_top
  -- Integrability on the reference cube of the centred potential times the pairing.
  have hcubeProd_mu : Integrable (fun y => w y * vecDot (fl y) (ξ y))
      (normalizedCubeMeasure (originCube d t)) := by
    have hterm : ∀ i : Fin d, Integrable (fun y => ξ y i * (fl y i * w y))
        (normalizedCubeMeasure (originCube d t)) := by
      intro i
      exact ((hflux.eval i).integrable_mul hw_mu).mul_of_top_right (hξLp.eval i)
    have hsum := integrable_finsetSum (Finset.univ) (fun i _ => hterm i)
    refine hsum.congr (Filter.Eventually.of_forall (fun y => ?_))
    simp only [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hcubeProd : IntegrableOn (fun y => w y * vecDot (fl y) (ξ y))
      (cubeSet (originCube d t)) := by
    show Integrable (fun y => w y * vecDot (fl y) (ξ y))
      (volume.restrict (cubeSet (originCube d t)))
    have h := hcubeProd_mu
    rw [normalizedCubeMeasure, cubeMeasure] at h
    exact (integrable_smul_measure hc0 hctop).mp h
  -- The two pairings on the cell are the change of variables of the cube pairings.
  have hgcomp : IntegrableOn (fun y => g (matVecMul (respGrid jStar F) y))
      (openCubeSet (originCube d t)) := by
    have hcp : Integrable (fun y => w y * vecDot (fl y) (ξ y))
        (volume.restrict (openCubeSet (originCube d t))) := by
      have h : Integrable (fun y => w y * vecDot (fl y) (ξ y))
          (volume.restrict (cubeSet (originCube d t))) := hcubeProd
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d t)] at h
      exact h
    refine hcp.congr (Filter.Eventually.of_forall (fun y => ?_))
    have hwv : w y = u.toH1.toFun (matVecMul (respGrid jStar F) y)
        - vecDot Y.1 (matVecMul (respGrid jStar F) y) := by
      rw [hw]
      exact congrFun (respCenteredPullbackH1_toFun hjStar hm t b u Y) y
    have hvd := vecDot_pullback_slots hq (φ := φ) hφ.contDiff
      (matVecMul (b (matVecMul (respGrid jStar F) y))
        (u.toH1.grad (matVecMul (respGrid jStar F) y)) - Y.2) y
    have hscg : (fun j : Fin d =>
          (fderiv ℝ φ (matVecMul (respGrid jStar F) y)) (basisVec j))
        = scalarCutoffGradientField φ (matVecMul (respGrid jStar F) y) := by
      funext j
      exact (scalarCutoffGradientField_apply φ (matVecMul (respGrid jStar F) y) j).symm
    simp only [hg, hfl, hξdef, hwv, hscg, optimizerField, Prod.snd_sub]
    exact congrArg (fun s => (u.toH1.toFun (matVecMul (respGrid jStar F) y)
      - vecDot Y.1 (matVecMul (respGrid jStar F) y)) * s) hvd
  have hint2 : IntegrableOn g (HighContrast.adaptedCell (respGrid jStar F) t) := by
    have hemb := measurableEmbedding_matVecMul hq
    have hmap := map_matVecMul_volume_restrict hq (openCubeSet (originCube d t))
    have h1 : Integrable g
        (Measure.map (matVecMul (respGrid jStar F))
          (volume.restrict (openCubeSet (originCube d t)))) :=
      (hemb.integrable_map_iff).mpr hgcomp
    rw [hmap, image_openCubeSet_originCube_eq_adaptedCell (respGrid jStar F) t] at h1
    have hdet : 0 < |(respGrid jStar F).det|⁻¹ :=
      inv_pos.mpr (abs_pos.mpr
        ((Matrix.isUnit_iff_isUnit_det (A := respGrid jStar F)).mp hq |>.ne_zero))
    exact (integrable_smul_measure (c := ENNReal.ofReal |(respGrid jStar F).det|⁻¹)
      (ENNReal.ofReal_ne_zero_iff.mpr hdet) ENNReal.ofReal_ne_top).mp h1
  -- The remaining cell pairing and the flux integrability, from the elliptic representative.
  have hfluxCell : MemVectorL2 (respCell jStar F t)
      (fun x => matVecMul (b x) (u.toH1.grad x)) :=
    memVectorL2_flux_of_exists hq t hb u
  have hint1 : IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1))
      (HighContrast.adaptedCell (respGrid jStar F) t) :=
    hint1_of_inputs hjStar hm hφ hb u Y
  -- The identity converting the volume average to the centred cube average.
  have hid := volumeAverage_cutoff_pairing_eq_neg_cubeAverage_centered
    (jStar := jStar) (F := F) hjStar hm t (b := b) u Y
    hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset hfluxCell hint1
    (by simpa only [hg] using hint2)
    (by simpa only [hfl, hξdef] using! hcube)
    (by simpa only [hw, hfl, hξdef] using! hcubeProd)
  -- The negative-Besov duality bound with all coefficients discharged.
  have hbnd := abs_cubeAverage_pullback_pairing_le_besov_sq
    (jStar := jStar) (F := F) hjStar hm t hb u Y hφ
  calc
    |volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))|
        = |cubeAverage (originCube d t) (fun y => vecDot
            (matVecMul (respGrid jStar F)⁻¹
              ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
            (((respCenteredPullbackH1 hjStar hm t b u Y y -
                cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
              scalarCutoffGradientField
                (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y : Vec d)))| := by
          rw [show volumeAverage (respCell jStar F t) (fun x =>
              φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
              = _ from hid]
          exact abs_neg _
    _ ≤ C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField b u) - Y)) ^ 2) := by
          rw [hC₀def]
          exact hbnd

end

end Homogenization.HighContrast.Multiscale
