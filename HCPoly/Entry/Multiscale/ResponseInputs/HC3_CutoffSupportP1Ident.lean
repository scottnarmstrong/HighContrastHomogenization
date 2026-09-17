import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Entry.Multiscale.ResponseInputs.H1LinearPullback
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCubeForm
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportAdjoint
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportZeroAvg
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportCentring
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportSolenoidal

/-!
# The cutoff pairing as a centred cube average

On the adapted cell `U_t = q ⋄_t` the cutoff-weighted pairing of the gradient defect of a harmonic
optimizer against its flux defect is, after integration by parts, the negative of the normalized
average of the centred potential against the flux defect contracted with the gradient of the
cutoff.  Composing that identity with the change of variables `x = q y` and with the adjointness of
the pulled-back pairing rewrites it on the reference cube `originCube d t`, where the first slot of
the pairing is the pulled-back flux defect `q⁻¹ (b ∇v - q₀)` and the second is the gradient of the
pulled-back cutoff.

Because the flux defect is weakly divergence free, the pairing against the cutoff gradient has zero
average, so centring the potential changes nothing.  The resulting identity is the exact shape in
which the negative-Besov duality bound `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)) is
stated, and it is the identity half of the pathwise cutoff bound: no inequality is involved.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The cutoff-weighted pairing of the gradient defect of a harmonic optimizer against its flux
defect, normalized over the adapted cell `U_t = q ⋄_t`, equals the negative of the normalized
average over the reference cube `originCube d t` of the Euclidean pairing of the pulled-back flux
defect `q⁻¹ (b ∇v - q₀)` against the centred pulled-back potential multiplied into the gradient of
the pulled-back cutoff.  With `q` the selected grid and the potential centred at its cube average,
this is the identity form of the cutoff estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1,
(A.4)) on which the negative-Besov duality bound is applied. -/
theorem volumeAverage_cutoff_pairing_eq_neg_cubeAverage_centered
    {d : ℕ} [NeZero d] {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    {b : CoeffField d} (u : AHarmonicFunction b (HighContrast.adaptedCell (respGrid jStar F) t))
    (Y : BlockVec d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ HighContrast.adaptedCell (respGrid jStar F) t)
    (hflux : MemVectorL2 (HighContrast.adaptedCell (respGrid jStar F) t)
      (fun x => matVecMul (b x) (u.toH1.grad x)))
    (hint1 : MeasureTheory.IntegrableOn (fun x => φ x *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2) (u.toH1.grad x - Y.1))
      (HighContrast.adaptedCell (respGrid jStar F) t))
    (hint2 : MeasureTheory.IntegrableOn (fun x => (u.toH1.toFun x - vecDot Y.1 x) *
      vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
        (fun j => (fderiv ℝ φ x) (basisVec j))) (HighContrast.adaptedCell (respGrid jStar F) t))
    (hcube : MeasureTheory.IntegrableOn
      (fun y => vecDot
        (matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (scalarCutoffGradientField
          (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y))
      (cubeSet (originCube d t)))
    (hcubeProd : MeasureTheory.IntegrableOn
      (fun y => respCenteredPullbackH1 hjStar hm t b u Y y * vecDot
        (matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (scalarCutoffGradientField
          (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y))
      (cubeSet (originCube d t))) :
    volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -cubeAverage (originCube d t) (fun y =>
          vecDot
            (matVecMul (respGrid jStar F)⁻¹
              ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
            (((respCenteredPullbackH1 hjStar hm t b u Y y -
                cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
              scalarCutoffGradientField
                (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y : Vec d))) := by
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell (respGrid jStar F) t)) :=
    (adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F)
      (isUnit_respGrid hjStar hm) t).isFiniteMeasure_restrict_volume
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell (respGrid jStar F) t) :=
    adaptedCell_isOpenBoundedConvexDomain (respGrid jStar F) hq t
  have hint2' : MeasureTheory.IntegrableOn
      (fun x => (u.toH1.toFun x - vecDot Y.1 x - 0) *
        vecDot (matVecMul (b x) (u.toH1.grad x) - Y.2)
          (fun j => (fderiv ℝ φ x) (basisVec j)))
      (HighContrast.adaptedCell (respGrid jStar F) t) := by
    simpa only [sub_zero] using hint2
  have hIBP := cubeAverage_cutoff_pairing_eq_neg (q := respGrid jStar F) hq t hU u hflux Y 0
    hφ hφ_compact hφ_sub hint1 hint2'
  have hsol : IsSolenoidalOn (HighContrast.adaptedCell (respGrid jStar F) t)
      (fun x => matVecMul (b x) (u.toH1.grad x) - Y.2) :=
    isSolenoidalOn_fluxDefect_of_finiteMeasure u hflux Y.2
  have hzero : cubeAverage (originCube d t)
      (fun y => vecDot
        (matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (scalarCutoffGradientField
          (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)) = 0 := by
    let f : Vec d → ℝ := fun x => vecDot
      (matVecMul (b x) (u.toH1.grad x) - Y.2)
      (fun j => (fderiv ℝ φ x) (basisVec j))
    have hz : volumeAverage (HighContrast.adaptedCell (respGrid jStar F) t) f = 0 :=
      volumeAverage_vecDot_solenoidal_gradCutoff_eq_zero hU hsol hφ hφ_compact hφ_sub
    have hcov := volumeAverage_adaptedCell_eq_cubeAverage_comp (q := respGrid jStar F) hq t f
    have hcomp : cubeAverage (originCube d t)
        (fun y => f (matVecMul (respGrid jStar F) y)) = 0 := hcov.symm.trans hz
    refine Eq.trans ?_ hcomp
    apply congrArg (cubeAverage (originCube d t))
    funext y
    exact vecDot_pullback_slots hq hφ
      ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2) y
  have hcent := cubeAverage_centered_mul_of_average_eq_zero (originCube d t)
    (f := fun y => respCenteredPullbackH1 hjStar hm t b u Y y)
    (g := fun y => vecDot
      (matVecMul (respGrid jStar F)⁻¹
        ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
      (scalarCutoffGradientField
        (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y))
    hcubeProd hcube hzero
  have hpt : ∀ y : Vec d,
      (u.toH1.toFun (matVecMul (respGrid jStar F) y)
          - vecDot Y.1 (matVecMul (respGrid jStar F) y) - 0) *
        vecDot
          (matVecMul (b (matVecMul (respGrid jStar F) y))
            (u.toH1.grad (matVecMul (respGrid jStar F) y)) - Y.2)
          (fun j => (fderiv ℝ φ (matVecMul (respGrid jStar F) y)) (basisVec j))
      = (respCenteredPullbackH1 hjStar hm t b u Y).toFun y *
        vecDot
          (matVecMul (respGrid jStar F)⁻¹
            ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
          (scalarCutoffGradientField
            (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y) := by
    intro y
    simp only [optimizerField, Prod.snd_sub]
    rw [respCenteredPullbackH1_toFun, sub_zero]
    refine congrArg (fun t : ℝ =>
      (u.toH1.toFun (matVecMul (respGrid jStar F) y)
        - vecDot Y.1 (matVecMul (respGrid jStar F) y)) * t) ?_
    rw [vecDot_pullback_slots hq hφ
      (matVecMul (b (matVecMul (respGrid jStar F) y))
        (u.toH1.grad (matVecMul (respGrid jStar F) y)) - Y.2) y]
    congr 1
  have hmain : volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
      = -cubeAverage (originCube d t) (fun y =>
          respCenteredPullbackH1 hjStar hm t b u Y y *
            vecDot
              (matVecMul (respGrid jStar F)⁻¹
                ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
              (scalarCutoffGradientField
                (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)) := by
    unfold respCell
    rw [hIBP]
    apply congrArg (fun z : ℝ => -z)
    apply congrArg (cubeAverage (originCube d t))
    funext y
    exact hpt y
  calc
    volumeAverage (respCell jStar F t) (fun x =>
        φ x * vecDot ((optimizerField b u x).1 - Y.1) ((optimizerField b u x).2 - Y.2))
        = -cubeAverage (originCube d t) (fun y =>
            respCenteredPullbackH1 hjStar hm t b u Y y *
              vecDot
                (matVecMul (respGrid jStar F)⁻¹
                  ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
                (scalarCutoffGradientField
                  (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)) := hmain
    _ = -cubeAverage (originCube d t) (fun y =>
            (respCenteredPullbackH1 hjStar hm t b u Y y
              - cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) *
              vecDot
                (matVecMul (respGrid jStar F)⁻¹
                  ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
                (scalarCutoffGradientField
                  (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)) :=
          congrArg (fun z : ℝ => -z) hcent.symm
    _ = -cubeAverage (originCube d t) (fun y =>
            vecDot
              (matVecMul (respGrid jStar F)⁻¹
                ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
              (((respCenteredPullbackH1 hjStar hm t b u Y y
                  - cubeAverage (originCube d t)
                      (fun z => respCenteredPullbackH1 hjStar hm t b u Y z)) •
                scalarCutoffGradientField
                  (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y : Vec d))) := by
          apply congrArg (fun z : ℝ => -z)
          apply congrArg (cubeAverage (originCube d t))
          funext y
          exact (vecDot_smul_right
            (matVecMul (respGrid jStar F)⁻¹
              ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
            (scalarCutoffGradientField
              (fun z : Vec d => φ (matVecMul (respGrid jStar F) z)) y)
            (respCenteredPullbackH1 hjStar hm t b u Y y
              - cubeAverage (originCube d t)
                  (fun z => respCenteredPullbackH1 hjStar hm t b u Y z))).symm

end

end Homogenization.HighContrast.Multiscale
