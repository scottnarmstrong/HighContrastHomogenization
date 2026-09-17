import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsStateFam
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffQuadConnectTwo
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffCentredSplitInt

/-!
# The cutoff pairing is measurable in the sample without its absolute value

`HC3_CutoffPairingMeasFamily` records that the MODULUS of the cutoff pairing of
`e.response.cutoff.estimate` is almost-everywhere strongly measurable in the coefficient sample for
an arbitrary family of response maximizers.  The row assembly
`abs_respCenteredJ{Minus,Plus}_le_cutoffRows_of_obligations` needs the `P`-integrability of the
SIGNED pairing, which the modulus alone does not give: an integrable modulus supplies the finite
integral but not the measurability of the signed function.

The signed measurability follows by the same route, and with no further input.  The doubled
optimizer state of an arbitrary response maximizer agrees almost everywhere on the terminal cell
with the measurable canonical Chapter-2 selection, so the signed pairing agrees with the canonical
signed pairing; and the canonical signed pairing is measurable by
`aestronglyMeasurable_pairing_canonical_of_quadratic`, whose quadratic input is discharged with no
hypothesis beyond the cutoff class by
`measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeff{Minus,Plus}_full`.  Together with the
integrability of the modulus, which `p.response.transfer` already carries, this closes
the `hA` side condition of the row assembly.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The canonical signed cutoff pairing is measurable, minus recentring.**  With no hypothesis
beyond the cutoff class: the three linear readouts of the canonical optimizer state are measurable,
and so is the quadratic one. -/
theorem aestronglyMeasurable_canonical_cutoff_pairing_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d) :
    AEStronglyMeasurable (fun a : CoeffSpace d => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffMinusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffMinusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  refine aestronglyMeasurable_pairing_canonical_of_quadratic P (respGrid jStar F) hq t
    p q' Y hφ ?_ ?_ ?_ ?_
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffMinus_potential
        (respGrid jStar F) hq t F p q' hφ W
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffMinus_flux
        (respGrid jStar F) hq t F p q' hφ W
  · intro a
    simpa only [respCell] using
      memVectorL2_canonicalRespCoeffMinus_flux (respGrid jStar F) hq t F p q' a
  · exact (measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffMinus_full
      (respGrid jStar F) hq t F p q' hφ).aestronglyMeasurable

/-- **The canonical signed cutoff pairing is measurable, plus recentring.**  The adjoint twin of
`aestronglyMeasurable_canonical_cutoff_pairing_respCoeffMinus`. -/
theorem aestronglyMeasurable_canonical_cutoff_pairing_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d) :
    AEStronglyMeasurable (fun a : CoeffSpace d => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffPlusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState
              (adaptedDomain (respGrid jStar F) (Geometry.isUnit_roundedGrid hjStar hm) t)
              (canonicalRespCoeffPlusOn (respGrid jStar F)
                (Geometry.isUnit_roundedGrid hjStar hm) t F a) p q' x).2 - Y.2))) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  refine aestronglyMeasurable_pairing_canonical_of_quadratic P (respGrid jStar F) hq t
    p q' Y hφ ?_ ?_ ?_ ?_
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffPlus_potential
        (respGrid jStar F) hq t F p q' hφ W
  · intro W
    simpa only [respCell] using
      measurable_volumeAverage_cutoff_vecDot_canonicalRespCoeffPlus_flux
        (respGrid jStar F) hq t F p q' hφ W
  · intro a
    simpa only [respCell] using
      memVectorL2_canonicalRespCoeffPlus_flux (respGrid jStar F) hq t F p q' a
  · exact (measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffPlus_full
      (respGrid jStar F) hq t F p q' hφ).aestronglyMeasurable

/-- **The signed cutoff pairing of an arbitrary maximizer family is measurable, minus
recentring.**  The doubled optimizer state of the maximizer agrees almost everywhere on the
terminal cell with the canonical Chapter-2 selection, so the two pairings agree sample by sample. -/
theorem aestronglyMeasurable_hc3CutoffPairingOnCellAux_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) (uM a)) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      hc3CutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffMinus F a) (uM a)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d =>
        hc3CutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffMinus F a) (uM a))
      = fun a : CoeffSpace d => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2)) := by
    funext a
    have hfield := optimizerField_ae_eq_canonicalState_respCoeffMinus
      (respGrid jStar F) hq t F a p q' (uM a) (hmax a)
    have hInt : (fun x => φ x * vecDot ((optimizerField (respCoeffMinus F a) (uM a) x).1 - Y.1)
          ((optimizerField (respCoeffMinus F a) (uM a) x).2 - Y.2))
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffMinusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2)) := by
      filter_upwards [hfield] with x hx
      rw [show optimizerField (respCoeffMinus F a) (uM a) x = _ from hx]
    exact volumeAverage_congr_ae (subset_refl (respCell jStar F t)) hInt
  rw [hEq]
  exact aestronglyMeasurable_canonical_cutoff_pairing_respCoeffMinus P jStar F t hjStar hm φ hφ
    p q' Y

/-- **The signed cutoff pairing of an arbitrary maximizer family is measurable, plus
recentring.**  The adjoint twin of
`aestronglyMeasurable_hc3CutoffPairingOnCellAux_respCoeffMinus`. -/
theorem aestronglyMeasurable_hc3CutoffPairingOnCellAux_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) (uP a)) :
    AEStronglyMeasurable (fun a : CoeffSpace d =>
      hc3CutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffPlus F a) (uP a)) P := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hEq : (fun a : CoeffSpace d =>
        hc3CutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffPlus F a) (uP a))
      = fun a : CoeffSpace d => volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2)) := by
    funext a
    have hfield := optimizerField_ae_eq_canonicalState_respCoeffPlus
      (respGrid jStar F) hq t F a p q' (uP a) (hmax a)
    have hInt : (fun x => φ x * vecDot ((optimizerField (respCoeffPlus F a) (uP a) x).1 - Y.1)
          ((optimizerField (respCoeffPlus F a) (uP a) x).2 - Y.2))
        =ᵐ[volumeMeasureOn (respCell jStar F t)]
        (fun x => φ x * vecDot
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).1 - Y.1)
          ((canonicalOptimizerBlockState (adaptedDomain (respGrid jStar F) hq t)
              (canonicalRespCoeffPlusOn (respGrid jStar F) hq t F a) p q' x).2 - Y.2)) := by
      filter_upwards [hfield] with x hx
      rw [show optimizerField (respCoeffPlus F a) (uP a) x = _ from hx]
    exact volumeAverage_congr_ae (subset_refl (respCell jStar F t)) hInt
  rw [hEq]
  exact aestronglyMeasurable_canonical_cutoff_pairing_respCoeffPlus P jStar F t hjStar hm φ hφ
    p q' Y

/-- **The `hA` side condition of the row assembly, minus recentring.**  The half-weighted signed
cutoff pairing is `P`-integrable: its modulus is integrable by the premise that
`p.response.transfer` already carries, and the signed function is measurable.  The modulus is
stated through `hc3CutoffPairingOnCellAux`, which is the same function as the kernel's
`hc3CutoffPairingOnCell` -- the two definitions have identical bodies, so the premise
discharges `habs` directly. -/
theorem integrable_half_hc3CutoffPairingOnCellAux_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffMinus F a) (uM a))
    (habs : Integrable (fun a : CoeffSpace d =>
      |hc3CutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffMinus F a) (uM a)|) P) :
    Integrable (fun a : CoeffSpace d => (1 / 2 : ℝ) *
      hc3CutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffMinus F a) (uM a)) P := by
  have hmeas := aestronglyMeasurable_hc3CutoffPairingOnCellAux_respCoeffMinus
    P jStar F t hjStar hm φ hφ p q' Y uM hmax
  refine Integrable.const_mul ?_ (1 / 2 : ℝ)
  refine habs.mono' hmeas (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs]

/-- **The `hA` side condition of the row assembly, plus recentring.**  The adjoint twin of
`integrable_half_hc3CutoffPairingOnCellAux_respCoeffMinus`. -/
theorem integrable_half_hc3CutoffPairingOnCellAux_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hm : (explicitCanonicalMetric F).PosDef)
    (φ : Vec d → ℝ) (hφ : IsResponseCutoff (respGrid jStar F) t φ)
    (p q' : Vec d) (Y : BlockVec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (respCoeffPlus F a) (uP a))
    (habs : Integrable (fun a : CoeffSpace d =>
      |hc3CutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffPlus F a) (uP a)|) P) :
    Integrable (fun a : CoeffSpace d => (1 / 2 : ℝ) *
      hc3CutoffPairingOnCellAux (respCell jStar F t) φ Y (respCoeffPlus F a) (uP a)) P := by
  have hmeas := aestronglyMeasurable_hc3CutoffPairingOnCellAux_respCoeffPlus
    P jStar F t hjStar hm φ hφ p q' Y uP hmax
  refine Integrable.const_mul ?_ (1 / 2 : ℝ)
  refine habs.mono' hmeas (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs]

end

end Homogenization.HighContrast.Multiscale
