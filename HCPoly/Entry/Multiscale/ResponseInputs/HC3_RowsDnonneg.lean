import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectDeficitNonneg
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCellPair
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# Nonnegativity of the subcell deficit at the response coefficients

On each coarse subcell of the terminal cell, the terminal optimiser restricted there is an
admissible competitor for the subcell's own response problem, so the subcell deficit of
`p.response.transfer` — the subcell response minus the average over the subcell of the terminal
optimiser's response integrand — is nonnegative, pathwise in the coefficient sample.  The response
coefficients `respCoeff∓ F a` are elliptic only almost everywhere, so the argument runs at the
pointwise elliptic representative supplied by `H8bEllipticInput` and transports both the response
and the averaged integrand back across the almost-everywhere replacement, which leaves each of them
invariant.  This is the hypothesis `hD` of the cell half of the cutoff-mean row of
`p.response.transfer`, for the minus sign and for its plus twin.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The subcell deficit is nonnegative, minus family.**  Let `a_- = respCoeffMinus F a` be the
response coefficient of the terminal cell `U_t = respCell jStar F t`, let `uM a` be a `a_-`-harmonic
field on `U_t`, and suppose that on every aligned subcell `U_s(w)` the field `v w a` maximises that
subcell's response for the loads `(p, q^-)`.  Then, for every subcell `w` of the depth-`H` partition
of `U_t` (`t = s + H`) and every sample `a`, the subcell deficit

  `J(U_s(w), p, q^-; a_-) − ⨍_{U_s(w)} g_{U_t}(uM a)`

is nonnegative: `uM a` restricted to the subcell is an admissible competitor there, and the
restriction does not change the scalar response integrand.  The coefficient is elliptic only almost
everywhere, so the competitor argument is run at the pointwise elliptic representative of `a_-` and
both terms are carried back, which leaves them unchanged. -/
theorem zero_le_subcellDeficit_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a) (v w a)) :
    ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffMinus F a)
                (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (uM a)) := by
  subst t
  intro w hw a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffMinus hjStar hm (s + (H : ℤ)) a
  have hk : (s + (H : ℤ)) - (H : ℤ) = s := by ring
  have hU : IsOpen (respCell jStar F (s + (H : ℤ))) :=
    isOpen_adaptedCell_of_isUnit hq (s + (H : ℤ))
  have hV : IsOpen (adaptedCellAtCenter (respGrid jStar F) s w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq s w
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F (s + (H : ℤ)) := by
    simpa only [hk] using!
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) (s + (H : ℤ)) H hw
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter (respGrid jStar F) s w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq s w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) s w)) := by
    simpa [volumeMeasureOn] using hdom.isFiniteMeasure_restrict_volume
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter (respGrid jStar F) s w) f :=
    hEll.mono hV.measurableSet hVU
  have haeV : respCoeffMinus F a =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) s w)] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  have hmaxV' : IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
      (respP (respMean P jStar F (s + (H : ℤ))) e)
      (respqMinus P jStar F (s + (H : ℤ)) e) f
      (aHarmonicFunctionOfAEEqCoeff haeV (v w a)) :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff haeV
      (respP (respMean P jStar F (s + (H : ℤ))) e)
      (respqMinus P jStar F (s + (H : ℤ)) e) (hv w a)
  have hlef := volumeAverage_scalarResponseIntegrand_le_responseJ hU hV hVU hEllV
    (respP (respMean P jStar F (s + (H : ℤ))) e)
    (respqMinus P jStar F (s + (H : ℤ)) e)
    (aHarmonicFunctionOfAEEqCoeff hae (uM a))
    (aHarmonicFunctionOfAEEqCoeff haeV (v w a)) hmaxV'
  rw [responseJ_congr_of_ae_eq_subset hVU hae
        (respP (respMean P jStar F (s + (H : ℤ))) e)
        (respqMinus P jStar F (s + (H : ℤ)) e),
      ← volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae
        (respP (respMean P jStar F (s + (H : ℤ))) e)
        (respqMinus P jStar F (s + (H : ℤ)) e) (uM a)]
  linarith

/-- **The subcell deficit is nonnegative, plus family.**  The transposed twin of
`zero_le_subcellDeficit_respCoeffMinus`: with the response coefficient `a_+ = respCoeffPlus F a`,
the loads `(p, q^+)` and subcell maximisers `v w a` for `a_+`, the subcell deficit

  `J(U_s(w), p, q^+; a_+) − ⨍_{U_s(w)} g_{U_t}(uM a)`

is nonnegative on every subcell of the depth-`H` partition of the terminal cell, pathwise in the
sample `a`.  The a.e.-elliptic representative of `a_+` again makes the competitor argument valid. -/
theorem zero_le_subcellDeficit_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (H : ℕ) (s t : ℤ) (ht : t = s + (H : ℤ)) (e : Vec d)
    (uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t))
    (v : (w : Fin d → ℤ) → (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) s w))
    (hv : ∀ (w : Fin d → ℤ) (a : CoeffSpace d),
      IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a) (v w a)) :
    ∀ w ∈ triadicIndexBox d H, ∀ a : CoeffSpace d,
      0 ≤ ResponseJ (adaptedCellAtCenter (respGrid jStar F) s w) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a)
          - volumeAverage (adaptedCellAtCenter (respGrid jStar F) s w)
              (scalarResponseIntegrand (respCell jStar F t) (respCoeffPlus F a)
                (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (uM a)) := by
  subst t
  intro w hw a
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCell_respCoeffPlus hjStar hm (s + (H : ℤ)) a
  have hk : (s + (H : ℤ)) - (H : ℤ) = s := by ring
  have hU : IsOpen (respCell jStar F (s + (H : ℤ))) :=
    isOpen_adaptedCell_of_isUnit hq (s + (H : ℤ))
  have hV : IsOpen (adaptedCellAtCenter (respGrid jStar F) s w) :=
    isOpen_adaptedCellAtCenter_of_isUnit hq s w
  have hVU : adaptedCellAtCenter (respGrid jStar F) s w ⊆ respCell jStar F (s + (H : ℤ)) := by
    simpa only [hk] using!
      adaptedCellAtCenter_subset_adaptedCell (respGrid jStar F) (s + (H : ℤ)) H hw
  have hdom : IsOpenBoundedConvexDomain (adaptedCellAtCenter (respGrid jStar F) s w) :=
    isOpenBoundedConvexDomain_adaptedCellAtCenter (respGrid jStar F) hq s w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) s w)) := by
    simpa [volumeMeasureOn] using hdom.isFiniteMeasure_restrict_volume
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter (respGrid jStar F) s w) f :=
    hEll.mono hV.measurableSet hVU
  have haeV : respCoeffPlus F a =ᵐ[volumeMeasureOn (adaptedCellAtCenter (respGrid jStar F) s w)] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hae
  have hmaxV' : IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) s w)
      (respP (respMean P jStar F (s + (H : ℤ))) e)
      (respqPlus P jStar F (s + (H : ℤ)) e) f
      (aHarmonicFunctionOfAEEqCoeff haeV (v w a)) :=
    isResponseMaximizer_aHarmonicFunctionOfAEEqCoeff haeV
      (respP (respMean P jStar F (s + (H : ℤ))) e)
      (respqPlus P jStar F (s + (H : ℤ)) e) (hv w a)
  have hlef := volumeAverage_scalarResponseIntegrand_le_responseJ hU hV hVU hEllV
    (respP (respMean P jStar F (s + (H : ℤ))) e)
    (respqPlus P jStar F (s + (H : ℤ)) e)
    (aHarmonicFunctionOfAEEqCoeff hae (uM a))
    (aHarmonicFunctionOfAEEqCoeff haeV (v w a)) hmaxV'
  rw [responseJ_congr_of_ae_eq_subset hVU hae
        (respP (respMean P jStar F (s + (H : ℤ))) e)
        (respqPlus P jStar F (s + (H : ℤ)) e),
      ← volumeAverage_scalarResponseIntegrand_subset_aHarmonicFunctionOfAEEqCoeff hVU hae
        (respP (respMean P jStar F (s + (H : ℤ))) e)
        (respqPlus P jStar F (s + (H : ℤ)) e) (uM a)]
  linarith

end

end Homogenization.HighContrast.Multiscale
