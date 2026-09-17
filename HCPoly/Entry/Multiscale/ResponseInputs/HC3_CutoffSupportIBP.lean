import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import Homogenization.Sobolev.PotentialSolenoidal
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.QuantCutoffLowerH1

/-!
# Integration by parts against a divergence-free field

Testing the weak solenoidal condition `Homogenization.IsSolenoidalOn` on the product of a smooth
cutoff `φ` with an `H¹(U)` function `w` moves the cutoff off the gradient of `w` and onto `w`
itself, at the cost of a sign.  This is the integration-by-parts step in the derivation of the
cutoff estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)); it turns the
cutoff-weighted pairing of the response estimate into a pairing of a centred potential against a
flux.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Integration by parts against a weakly solenoidal field `g` on an open bounded convex domain
`U`: for an `H¹(U)` function `w` and a smooth compactly supported cutoff `φ` whose support lies
in `U`, the cutoff-weighted pairing `∫_U φ (g · ∇w)` equals the negative of the pairing
`∫_U w (g · ∇φ)` in which the cutoff has been differentiated.  Both pairings are assumed
integrable on `U`.  This is the integration-by-parts step in the derivation of the cutoff
estimate `e.response.cutoff.estimate` (AK.HC Lemma A.1, (A.4)). -/
theorem integral_cutoff_vecDot_grad_eq_neg_integral_vecDot_gradCutoff {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) {g : Vec d → Vec d}
    (hsol : IsSolenoidalOn U g) (w : H1Function U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ U)
    (hint1 : MeasureTheory.IntegrableOn (fun x => φ x * vecDot (g x) (w.grad x)) U)
    (hint2 : MeasureTheory.IntegrableOn
      (fun x => w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) U) :
    (∫ x in U, φ x * vecDot (g x) (w.grad x))
      = -∫ x in U, w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j)) := by
  have hgrad :=
    WeakPoissonEquationOn.mulContDiffHasCompactSupportToH10_grad_ae w hU hφ hφ_compact hφ_sub
  have hsolψ :
      (∫ x in U, vecDot (g x)
        ((w.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub).toH1Function.grad x))
        = 0 :=
    hsol (w.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub)
  have hF : ∀ x,
      vecDot (g x) (fun j => φ x * w.grad x j + w x * (fderiv ℝ φ x) (basisVec j))
        = φ x * vecDot (g x) (w.grad x)
          + w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j)) := by
    intro x
    simp only [vecDot, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  have hzero :
      (∫ x in U,
        vecDot (g x) (fun j => φ x * w.grad x j + w x * (fderiv ℝ φ x) (basisVec j))) = 0 := by
    have hpt : (fun x => vecDot (g x)
          ((w.mulContDiffHasCompactSupportToH10 hU hφ hφ_compact hφ_sub).toH1Function.grad x))
        =ᵐ[volume.restrict U]
        (fun x => vecDot (g x)
          (fun j => φ x * w.grad x j + w x * (fderiv ℝ φ x) (basisVec j))) := by
      filter_upwards [hgrad] with x hx
      rw [hx]
    rw [← MeasureTheory.integral_congr_ae hpt, hsolψ]
  have hsplit :
      (∫ x in U, (φ x * vecDot (g x) (w.grad x)
          + w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))))
        = (∫ x in U, φ x * vecDot (g x) (w.grad x))
          + (∫ x in U, w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) :=
    MeasureTheory.integral_add hint1 hint2
  have hFsame :
      (∫ x in U, (φ x * vecDot (g x) (w.grad x)
          + w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))))
        = (∫ x in U,
          vecDot (g x) (fun j => φ x * w.grad x j + w x * (fderiv ℝ φ x) (basisVec j))) := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall fun x => (hF x).symm
  have hsum :
      (∫ x in U, φ x * vecDot (g x) (w.grad x))
        + (∫ x in U, w x * vecDot (g x) (fun j => (fderiv ℝ φ x) (basisVec j))) = 0 := by
    rw [← hsplit, hFsame]
    exact hzero
  exact eq_neg_of_add_eq_zero_left hsum

end

end Homogenization.HighContrast.Multiscale
