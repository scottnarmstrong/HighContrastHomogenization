import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportPullbackWeak
import HCPoly.Entry.Multiscale.ResponseInputs.H1LinearPullback

/-!
# The two negative-Besov inputs of the duality bound

The slotwise pullback bounds `partialSeminorm_pullback_fst_le_of_coords` and
`partialSeminorm_pullback_snd_le_of_coords` hold for an arbitrary doubled field `X`, subject to
coordinatewise square integrability on the adapted cell.  This file instantiates them at the
centred doubled optimizer field `X = (∇v, b∇v) − Y`.  The first slot is then the gradient of the
centred pulled-back potential, and the second the pulled-back flux defect, while the
square-integrability hypotheses are supplied by the elliptic representative of the coefficient.

Paper: the cutoff estimate `e.response.cutoff.estimate` and the scale-average seminorm bound of
`e.response.weak.estimate`.
-/

open Homogenization.HighContrast (matSqrt)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The negative-Besov seminorm on the reference cube of the gradient of the centred pulled-back
potential is bounded by the scale-average seminorm of the metric-scaled doubled optimizer state,
with the metric factor `qᵀ m^{-1/2}`.  This is the gradient slot of the duality bound, obtained by
applying `partialSeminorm_pullback_fst_le_of_coords` to the centred doubled optimizer field and
rewriting its first slot through the gradient of the pulled-back centred potential. -/
theorem cubeBesov_respCenteredPullbackH1_grad_le {d : ℕ} [NeZero d] {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (respCell jStar F t) f)
    (hbf : b =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (u : AHarmonicFunction b (respCell jStar F t)) (Y : BlockVec d) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (respCenteredPullbackH1 hjStar hm t b u Y).grad ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq
          (matTranspose (respGrid jStar F) * (matSqrt (explicitCanonicalMetric F))⁻¹)) *
        besovSeminorm t (cellAverageFamily (respGrid jStar F) t fun x =>
          (matVecMul (matSqrt (explicitCanonicalMetric F)) (optimizerField b u x - Y).1,
            matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ (optimizerField b u x - Y).2)) := by
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  obtain ⟨h1, h2⟩ :=
    memLp_two_coords_optimizerField_sub_const (q := respGrid jStar F) hq t hEll hbf u Y
  have hmain := partialSeminorm_pullback_fst_le_of_coords (q := respGrid jStar F) hq
    (explicitCanonicalMetric F) hm t N (fun x => optimizerField b u x - Y) h1 h2
  rw [respCenteredPullbackH1_grad hjStar hm t b u Y]
  exact hmain

/-- The negative-Besov seminorm on the reference cube of the pulled-back flux defect is bounded by
the scale-average seminorm of the metric-scaled doubled optimizer state, with the metric factor
`q⁻¹ m^{1/2}`.  This is the flux slot of the duality bound, obtained by applying
`partialSeminorm_pullback_snd_le_of_coords` to the centred doubled optimizer field. -/
theorem cubeBesov_pullback_fluxDefect_le {d : ℕ} [NeZero d] {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (respCell jStar F t) f)
    (hbf : b =ᵐ[volumeMeasureOn (respCell jStar F t)] f)
    (u : AHarmonicFunction b (respCell jStar F t)) (Y : BlockVec d) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm (originCube d t) (1 / 2 : ℝ) N
        (fun y => matVecMul (respGrid jStar F)⁻¹
          ((optimizerField b u (matVecMul (respGrid jStar F) y) - Y).2)) ≤
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        Real.sqrt (Book.Ch02.matrixFrobeniusNormSq
          ((respGrid jStar F)⁻¹ * matSqrt (explicitCanonicalMetric F))) *
        besovSeminorm t (cellAverageFamily (respGrid jStar F) t fun x =>
          (matVecMul (matSqrt (explicitCanonicalMetric F)) (optimizerField b u x - Y).1,
            matVecMul (matSqrt (explicitCanonicalMetric F))⁻¹ (optimizerField b u x - Y).2)) := by
  have hq : IsUnit (respGrid jStar F) := isUnit_respGrid hjStar hm
  obtain ⟨h1, h2⟩ :=
    memLp_two_coords_optimizerField_sub_const (q := respGrid jStar F) hq t hEll hbf u Y
  have hmain := partialSeminorm_pullback_snd_le_of_coords (q := respGrid jStar F) hq
    (explicitCanonicalMetric F) hm t N (fun x => optimizerField b u x - Y) h1 h2
  exact hmain

end

end Homogenization.HighContrast.Multiscale
