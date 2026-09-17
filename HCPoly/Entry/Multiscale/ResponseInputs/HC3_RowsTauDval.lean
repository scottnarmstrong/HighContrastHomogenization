import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectTauIdentity

/-!
# Twice the annealed mean subcell deficit is twice the scale defect

The row assembly of `p.response.transfer` consumes the scale defect with a factor two, because the
quadratic-response identity measures the energy of the difference field by twice the deficit.  This
module records that rescaling of the mean subcell deficit: the flat average, over the depth-`H`
aligned subcells of the coarse scale `s`, of twice each subcell's deficit integrates to twice the
scale defect `tau^∓`.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Twice the mean subcell deficit is twice the minus scale defect** (`p.response.transfer`).
The rescaling by the constant `2` of `integral_avsum_subcellDeficit_eq_respTauMinus`: for a
stationary law `P`, the flat average over the depth-`H` aligned subcells of the coarse scale `s` of
twice the gap between each subcell's own response and the restricted terminal response integrates
to twice the defect `respTauMinus` between the coarse and terminal scales. -/
theorem integral_avsum_two_subcellDeficit_eq_two_respTauMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))
      (respCell jStar F t))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) P)
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a)) P) :
    (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a))) ∂P)
      = 2 * respTauMinus P jStar F s t e := by
  have h := integral_avsum_subcellDeficit_eq_respTauMinus P hstat jStar hjStar F hm H s t ht hjs e
    uM hmax hblk hrespint hJint hRint hJt hJs
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  rw [← Finset.mul_sum]
  ring

/-- **Twice the mean subcell deficit is twice the plus scale defect** (`p.response.transfer`).
The rescaling by the constant `2` of `integral_avsum_subcellDeficit_eq_respTauPlus`: for a
stationary law `P`, the flat average over the depth-`H` aligned subcells of the coarse scale `s` of
twice the gap between each subcell's own response and the restricted terminal response integrates
to twice the adjoint defect `respTauPlus` between the coarse and terminal scales. -/
theorem integral_avsum_two_subcellDeficit_eq_two_respTauPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ))
    (hjs : (jStar : ℤ) ≤ s) (e : Vec d)
    (uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (hmax : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a))
    (hblk : ∀ w : Fin d → ℤ,
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) s w))
    (hrespint : ∀ a, MeasureTheory.IntegrableOn
      (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))
      (respCell jStar F t))
    (hJint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hRint : ∀ w ∈ triadicIndexBox d H, Integrable (fun a =>
      volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
        (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
          (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) P)
    (hJt : Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P)
    (hJs : Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a)) P) :
    (∫ a, (((triadicIndexBox d H).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d H,
        2 * (ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uP a))) ∂P)
      = 2 * respTauPlus P jStar F s t e := by
  have h := integral_avsum_subcellDeficit_eq_respTauPlus P hstat jStar hjStar F hm H s t ht hjs e
    uP hmax hblk hrespint hJint hRint hJt hJs
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with a
  rw [← Finset.mul_sum]
  ring

end

end Homogenization.HighContrast.Multiscale
