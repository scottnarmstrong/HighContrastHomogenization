import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRespJIntegrable
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRespJPlus

/-!
# Nonnegativity of the pathwise and annealed response energies

The pathwise response `J(U; p, q'; b)` of AK.HC (2.9) is the supremum of the A-harmonic
variational functional over the admissible class, and the zero field is admissible for every
coefficient field `b`; hence the supremum dominates `0` without any ellipticity hypothesis.  The
two recentred coefficients `a_- = a - g` and `a_+ = aᵗ + g` are special cases.  Integrating a
pointwise nonnegative function yields a nonnegative Bochner integral for every measure, so the
annealed responses `E[J_t^-]` and `E[J_t^+]` are nonnegative as well, with no integrability
hypothesis.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The pathwise response `J(U_u; p, r; a_-)` of the recentred coefficient `a_- = a - g` is
nonnegative.  It is the response supremum of AK.HC (2.9), whose admissible class contains the
zero field, so the value at the zero competitor already witnesses nonnegativity. -/
theorem zero_le_respJ_respCoeffMinus {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (u : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ respJ q u p r (respCoeffMinus F a) := by
  have _ := hq
  exact responseJ_nonneg (HighContrast.adaptedCell q u) p r (respCoeffMinus F a)

/-- The pathwise response `J(U_u; p, r; a_+)` of the recentred coefficient `a_+ = aᵗ + g` is
nonnegative.  It is the response supremum of AK.HC (2.9), whose admissible class contains the
zero field, so the value at the zero competitor already witnesses nonnegativity. -/
theorem zero_le_respJ_respCoeffPlus {d : ℕ} [NeZero d] (q : Mat d) (hq : IsUnit q) (u : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ respJ q u p r (respCoeffPlus F a) := by
  have _ := hq
  exact responseJ_nonneg (HighContrast.adaptedCell q u) p r (respCoeffPlus F a)

/-- The annealed response `E[J_t^-] = E[J(U_t; p, q^-; a_-)]` is nonnegative.  Its integrand is
pointwise nonnegative by the pathwise nonnegativity of the response, and the Bochner integral of
a pointwise nonnegative function is nonnegative for every measure, so no integrability hypothesis
is required.  This is the sign `0 ≤ E[J_t^-]` of the printed display `e.response.energy.and.defect`. -/
theorem zero_le_respEJMinus {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hq : IsUnit (respGrid jStar F)) :
    0 ≤ respEJMinus P jStar F t e := by
  unfold respEJMinus
  exact integral_nonneg fun a =>
    zero_le_respJ_respCoeffMinus (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)

/-- The annealed response `E[J_t^+] = E[J(U_t; p, q^+; a_+)]` is nonnegative.  Its integrand is
pointwise nonnegative by the pathwise nonnegativity of the response, and the Bochner integral of
a pointwise nonnegative function is nonnegative for every measure, so no integrability hypothesis
is required.  This is the sign `0 ≤ E[J_t^+]` of the printed display `e.response.energy.and.defect`. -/
theorem zero_le_respEJPlus {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (t : ℤ) (e : Vec d) (hq : IsUnit (respGrid jStar F)) :
    0 ≤ respEJPlus P jStar F t e := by
  unfold respEJPlus
  exact integral_nonneg fun a =>
    zero_le_respJ_respCoeffPlus (respGrid jStar F) hq t F a
      (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)

end

end Homogenization.HighContrast.Multiscale
