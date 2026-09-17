import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRowsReduction
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportEnergiesPlus

/-!
# The centred response as the annealed energy minus half the mean pairing

The centred responses `Jtilde^-(e)` and `Jtilde^+(e)` of `e.response.cutoff.estimate` are
defined on the annealed block `E_t = respMean` at the skew-shifted loads.  The recentring shear
`G = respG F` carries that block to the recentred block `Ehat_t^- = respEhatMinus`, and the
adjoint recentring carries the adjoint block to `Ehat_t^+ = respEhatPlus`.  Under that
identification the energy part of the centred response is the `P`-expectation of the recentred
pathwise response, and its remaining term is half the pairing of the two coordinates of the
annealed mean `Y^±` of AK.HC (2.32).  The two identities below record the resulting closed form
of the centred response as the annealed energy `E[J_t^±]` minus that pairing, which is the form
in which the cutoff decomposition of `e.response.cutoff.estimate` consumes it.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The centred response `Jtilde^-(e)` of `e.response.cutoff.estimate` is the annealed energy
`E[J_t^-] = respEJMinus` of the recentred coefficient `a_- = a - g` minus half the pairing of
the two coordinates of the annealed mean `Y^- = (I_{2d} + R Ehat_t^-) x^-` of AK.HC (2.32),
with `x^- = (-p, q^-)` the doubled recentred load.  The energy part is the block quadratic of the
recentred annealed block `Ehat_t^- = respEhatMinus` at that load, so the two sides agree
definitionally once the annealed energy is put in closed block form. -/
theorem respCenteredJMinus_eq_respEJMinus_sub {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respCenteredJMinus P jStar F t e
      = respEJMinus P jStar F t e
        - (1 / 2 : ℝ) * vecDot (respYMinus P jStar F t e).1 (respYMinus P jStar F t e).2 := by
  rw [respCenteredJMinus_eq_blockCenteredResponse_respEhatMinus,
    respEJMinus_eq_blockResponseEnergy P jStar F t e hq hint]
  rfl

/-- The adjoint centred response `Jtilde^+(e)` of `e.response.cutoff.estimate` is the adjoint
annealed energy `E[J_t^+] = respEJPlus` of the recentred coefficient `a_+ = a^t + g` minus half
the pairing of the two coordinates of the annealed mean `Y^+ = (I_{2d} + R Ehat_t^+) x^+` of
AK.HC (2.32), with `x^+ = (-p, q^+)` the doubled recentred load.  This is the adjoint twin of
`respCenteredJMinus_eq_respEJMinus_sub`, and the two sides agree definitionally once the adjoint
annealed energy is put in closed block form. -/
theorem respCenteredJPlus_eq_respEJPlus_sub {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) (hq : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t)) :
    respCenteredJPlus P jStar F t e
      = respEJPlus P jStar F t e
        - (1 / 2 : ℝ) * vecDot (respYPlus P jStar F t e).1 (respYPlus P jStar F t e).2 := by
  rw [respCenteredJPlus_eq_blockCenteredResponse_respEhatPlus,
    respEJPlus_eq_blockResponseEnergy P jStar F t e hq hint]
  rfl

end

end Homogenization.HighContrast.Multiscale
