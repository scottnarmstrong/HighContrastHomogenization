import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectAECongr
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscRow
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCutoffWeights
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectExpansionInt

/-!
# The cutoff oscillation split at a coefficient of the carrier

The terminal-optimizer replacement row of `p.response.transfer` splits the cutoff fluctuation
`φ - 1` against the optimizer energy on each aligned subcell of the coarse scale.  The variational
identities that produce the split are stated for a coefficient that is elliptic pointwise, while a
sample of the coefficient carrier is elliptic only almost everywhere.  These two statements run the
split at a pointwise elliptic representative of `a_- = a - g` (respectively `a_+ = aᵗ + g`) on the
terminal cell and transport the result back: the carried-along harmonic function has the same
gradient, every quantity of the split is invariant under the almost-everywhere replacement, and the
pathwise response is unchanged as well.

Paper: `p.response.transfer`.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The oscillation split of the cutoff fluctuation against the optimizer energy, for the minus
family, with no pointwise ellipticity hypothesis.  On the terminal cell `respCell jStar F t`, for a
cutoff `φ` of the response class and a response maximizer `u` of the loads `(p, r)` for the
recentred coefficient `respCoeffMinus F a`, the `(φ − 1)`-weighted optimizer energy differs from the
normalized sum, over the depth-`n` triadic subdivision, of the products of the subcell means of
`φ − 1` and of the energy by at most `32 d² responseCutoffProfileConst 3^{-n}` times twice the
pathwise response `respJ (respGrid jStar F) t p r (respCoeffMinus F a)`.  The coefficient is
elliptic only almost everywhere, so the estimate is run at a pointwise elliptic representative and
transported back; the response of the representative agrees with the response of the carrier
coefficient, and the carried-along optimizer has the same gradient.  This is the scale-gain step of
the cutoff estimate of `p.response.transfer`, in the form the row assembly consumes. -/
theorem abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffMinus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff (respGrid jStar F) t φ) (p r : Vec d)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : IsResponseMaximizer (respCell jStar F t) p r (respCoeffMinus F a) u) :
    |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand (respCoeffMinus F a) u)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
          (2 * respJ (respGrid jStar F) t p r (respCoeffMinus F a)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm t a
  let v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae u
  have hmaxf : IsResponseMaximizer (respCell jStar F t) p r f v :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae p r hmax
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have henergy : IntegrableOn (scalarVariationEnergyIntegrand f v) (respCell jStar F t) :=
    hdata.energy v
  have hUmeas : MeasurableSet (respCell jStar F t) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isOpen.measurableSet
  have hUfin : volume (respCell jStar F t) ≠ ⊤ :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).volume_lt_top.ne
  have hφE : IntegrableOn (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      (respCell jStar F t) :=
    integrableOn_cutoff_mul_coord hUmeas hUfin
      (hφ.contDiff.continuous.measurable.sub measurable_const)
      (fun x => by
        show |φ x - 1| ≤ (1 : ℝ)
        rw [abs_le]
        exact ⟨by linarith [hφ.nonneg x], by linarith [hφ.le_two x]⟩)
      henergy
  have hEat : ∀ w ∈ triadicIndexBox d n, IntegrableOn (scalarVariationEnergyIntegrand f v)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w hw => henergy.mono_set (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw)
  have hφat : ∀ w ∈ triadicIndexBox d n, IntegrableOn φ
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w _ => integrableOn_isResponseCutoff hq hφ (t - (n : ℤ)) w
  have hφEat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w hw => hφE.mono_set (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw)
  have hmain := abs_volumeAverage_sub_one_energy_sub_avsum_le hq t n hφ hEll p r v hmaxf
    (hdata.weakFlux v) (hdata.response p r v) (hdata.firstVariation p r v v) henergy
    hφE hEat hφat hφEat
  have hUw : volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      = volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) u x) :=
    volumeAverage_weighted_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (subset_refl (respCell jStar F t)) hae (fun x => φ x - 1) u
  have hVw : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand f v)
        = volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) :=
    fun w hw => volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) hae u
  have hsum : (∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand f v))
      = ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand (respCoeffMinus F a) u) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    rw [hVw w hw]
  have htrans : |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand f v)|
      = |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffMinus F a) u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand (respCoeffMinus F a) u)| := by
    rw [hUw, hsum]
  have hJw : respJ (respGrid jStar F) t p r f
      = respJ (respGrid jStar F) t p r (respCoeffMinus F a) := by
    unfold respJ
    exact (responseJ_congr_of_ae_eq hae p r).symm
  have hRHS : 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
        (2 * respJ (respGrid jStar F) t p r f)
      = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
        (2 * respJ (respGrid jStar F) t p r (respCoeffMinus F a)) := by
    rw [hJw]
  have htransA := htrans
  simp only [respCell] at htransA
  rw [htransA, hRHS] at hmain
  exact hmain

/-- The adjoint twin of `abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffMinus`: the same
oscillation split of the cutoff fluctuation against the optimizer energy, for the transposed
recentred coefficient `respCoeffPlus F a = aᵗ + g` and a response maximizer `u` of the loads
`(p, r)` for it.  The coefficient is elliptic only almost everywhere, so the estimate runs at a
pointwise elliptic representative and is transported back exactly as in the minus case.  This is
the scale-gain step of the adjoint cutoff estimate of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_energy_sub_avsum_le_respCoeffPlus {d : ℕ} [NeZero d]
    {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (n : ℕ)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff (respGrid jStar F) t φ) (p r : Vec d)
    (a : CoeffSpace d) (u : AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : IsResponseMaximizer (respCell jStar F t) p r (respCoeffPlus F a) u) :
    |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand (respCoeffPlus F a) u)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
          (2 * respJ (respGrid jStar F) t p r (respCoeffPlus F a)) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm t a
  let v : AHarmonicFunction f (respCell jStar F t) := aHarmonicFunctionOfAEEqCoeff hae u
  have hmaxf : IsResponseMaximizer (respCell jStar F t) p r f v :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff hae p r hmax
  have : IsFiniteMeasure (volumeMeasureOn (respCell jStar F t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isFiniteMeasure_restrict_volume
  have hdata : ResponseLinearIntegrabilityData (respCell jStar F t) f :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have henergy : IntegrableOn (scalarVariationEnergyIntegrand f v) (respCell jStar F t) :=
    hdata.energy v
  have hUmeas : MeasurableSet (respCell jStar F t) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).isOpen.measurableSet
  have hUfin : volume (respCell jStar F t) ≠ ⊤ :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t).volume_lt_top.ne
  have hφE : IntegrableOn (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      (respCell jStar F t) :=
    integrableOn_cutoff_mul_coord hUmeas hUfin
      (hφ.contDiff.continuous.measurable.sub measurable_const)
      (fun x => by
        show |φ x - 1| ≤ (1 : ℝ)
        rw [abs_le]
        exact ⟨by linarith [hφ.nonneg x], by linarith [hφ.le_two x]⟩)
      henergy
  have hEat : ∀ w ∈ triadicIndexBox d n, IntegrableOn (scalarVariationEnergyIntegrand f v)
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w hw => henergy.mono_set (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw)
  have hφat : ∀ w ∈ triadicIndexBox d n, IntegrableOn φ
      (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w _ => integrableOn_isResponseCutoff hq hφ (t - (n : ℤ)) w
  have hφEat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) :=
    fun w hw => hφE.mono_set (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw)
  have hmain := abs_volumeAverage_sub_one_energy_sub_avsum_le hq t n hφ hEll p r v hmaxf
    (hdata.weakFlux v) (hdata.response p r v) (hdata.firstVariation p r v v) henergy
    hφE hEat hφat hφEat
  have hUw : volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
      = volumeAverage (respCell jStar F t)
        (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) u x) :=
    volumeAverage_weighted_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (subset_refl (respCell jStar F t)) hae (fun x => φ x - 1) u
  have hVw : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand f v)
        = volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) :=
    fun w hw => volumeAverage_scalarVariationEnergyIntegrand_aHarmonicFunctionOfAEEqCoeff
      (adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) t n hw) hae u
  have hsum : (∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand f v))
      = ∑ w ∈ triadicIndexBox d n,
        volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w) (fun x => φ x - 1) *
          volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
            (scalarVariationEnergyIntegrand (respCoeffPlus F a) u) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    rw [hVw w hw]
  have htrans : |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand f v x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand f v)|
      = |volumeAverage (respCell jStar F t)
          (fun x => (φ x - 1) * scalarVariationEnergyIntegrand (respCoeffPlus F a) u x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (fun x => φ x - 1) *
              volumeAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (scalarVariationEnergyIntegrand (respCoeffPlus F a) u)| := by
    rw [hUw, hsum]
  have hJw : respJ (respGrid jStar F) t p r f
      = respJ (respGrid jStar F) t p r (respCoeffPlus F a) := by
    unfold respJ
    exact (responseJ_congr_of_ae_eq hae p r).symm
  have hRHS : 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
        (2 * respJ (respGrid jStar F) t p r f)
      = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) *
        (2 * respJ (respGrid jStar F) t p r (respCoeffPlus F a)) := by
    rw [hJw]
  have htransA := htrans
  simp only [respCell] at htransA
  rw [htransA, hRHS] at hmain
  exact hmain

end

end Homogenization.HighContrast.Multiscale
