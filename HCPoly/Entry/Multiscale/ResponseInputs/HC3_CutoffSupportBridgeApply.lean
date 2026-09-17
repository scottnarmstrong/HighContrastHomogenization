import HCPoly.Entry.Multiscale.ResponseInputs.H1LinearPullback
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Product.Bridge
import Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.QuantitativeCutoff.Basic

/-!
# The negative-Besov duality bound at the pulled-back cutoff data

The generic cutoff-product duality bound
`Book.Ch05.Section53.JUpperBoundWeakNorms.abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct`
is the direct full-dual pairing form of `AK.HC` Lemma A.1, (A.4).  This file reads it on the
reference cube after the linear change of variables of the cutoff argument: with `q = respGrid jStar F`
the centred potential is the pulled-back response `respCenteredPullbackH1`, the flux is the
pulled-back flux defect `q⁻¹ (b ∇v - q0)`, and the weight field is the gradient of the pulled-back
cutoff `scalarCutoffGradientField (φ ∘ q)`.  Every analytic hypothesis of the generic bound — the
membrane and smoothness data of the weight field, the derivative bound, the square integrability of
the flux, and the two negative-Besov seminorm bounds — is carried through unchanged at the
pulled-back data.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal

noncomputable section

/-- The negative-Besov duality bound (`AK.HC` Lemma A.1, (A.4)) evaluated on the reference cube
`openCubeSet (originCube d t)` at the pulled-back cutoff data.  With `q = respGrid jStar F`, the
potential is the centred pulled-back response `respCenteredPullbackH1`, the flux is the pulled-back
flux defect `q⁻¹ (b ∇v - q0)`, and the weight field is the gradient of the pulled-back cutoff
`φ ∘ q`; the two exponents take the symmetric value `s = t = 1/2`.

The conclusion is the generic bound with its four coefficient `let`s expanded: the scaled gradient
and flux seminorms, the cutoff-product coefficient built from the derivative bound `B` and the
cutoff gradient, and the flux coefficient carrying the scale weights. -/
theorem abs_cubeAverage_pullback_pairing_le
    {d : ℕ} [NeZero d] {jStar : ℕ} (hjStar : 2 * d ≤ 3 ^ jStar)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (b : CoeffField d) (u : AHarmonicFunction b (HighContrast.adaptedCell (respGrid jStar F) t))
    (Y : BlockVec d) {φ : Vec d → ℝ} {B gradWeak fluxWeak : ℝ}
    (hB : 0 ≤ B)
    (hξLp :
      MemLp (scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y))) ∞
        (normalizedCubeMeasure (originCube d t)))
    (hξ :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) x i))
    (hderiv :
      ∀ i : Fin d, ∀ z ∈ cubeSet (originCube d t),
        ‖fderiv ℝ (fun x =>
          scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) x i) z‖ ≤ B)
    (hflux :
      MemLp (fun y => matVecMul (respGrid jStar F)⁻¹
        ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
        (2 : ℝ≥0∞) (normalizedCubeMeasure (originCube d t)))
    (hgradWeak :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
        (respCenteredPullbackH1 hjStar hm t b u Y).grad ≤ gradWeak)
    (hfluxWeak :
      ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2) N
        (fun y => matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2)) ≤ fluxWeak) :
    |cubeAverage (originCube d t)
        (fun x => vecDot
          (matVecMul (respGrid jStar F)⁻¹
            ((optimizerField b u (matVecMul (respGrid jStar F) x) - Y).2))
          (((respCenteredPullbackH1 hjStar hm t b u Y x
              - cubeAverage (originCube d t)
                  (fun y => respCenteredPullbackH1 hjStar hm t b u Y y)) •
            scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)) x :
              Vec d)))| ≤
      (((2 * cubeScaleFactor (originCube d t) * B +
            3 * cubeLpNorm (originCube d t) ∞
              (scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)))) *
            ((Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) *
                (3 : ℝ) ^ ((d : ℝ) + 1)) *
              (Fintype.card (Fin d) : ℝ))) *
          ((Fintype.card (Fin d) : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + (1 - 1 / 2)) *
              cubeBesovScaleWeight (-(1 - 1 / 2 - 1 / 2)) (originCube d t)))) *
        ((cubeBesovScaleWeight (-(1 / 2)) (originCube d t) * gradWeak) *
          (cubeBesovScaleWeight (-(1 / 2)) (originCube d t) * fluxWeak)) := by
  exact abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct
    (Q := originCube d t) (s := 1 / 2) (t := 1 / 2)
    (hs_pos := by norm_num) (hs_lt_one := by norm_num) (hst := by norm_num)
    (flux := fun y => matVecMul (respGrid jStar F)⁻¹
      ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2))
    (u := respCenteredPullbackH1 hjStar hm t b u Y)
    (ξ := scalarCutoffGradientField (fun y => φ (matVecMul (respGrid jStar F) y)))
    (B := B) (gradWeak := gradWeak) (fluxWeak := fluxWeak)
    (hB := hB) (hξLp := hξLp) (hξ := hξ) (hderiv := hderiv) (hflux := hflux)
    (hgradWeak := hgradWeak) (hfluxWeak := hfluxWeak)

end

end Homogenization.HighContrast.Multiscale
