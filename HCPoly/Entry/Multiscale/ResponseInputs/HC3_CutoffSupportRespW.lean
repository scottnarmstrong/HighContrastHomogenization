import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportWeak

/-!
# The weak quantities of the two signs

The weak response quantities `W^-` and `W^+` of the response estimate are the weak energies of
the two recentred coefficients `a_- = a - g` and `a_+ = a^t + g` at the two response loads
`q^-` and `q^+`, evaluated on the selected grid with the self-dual metric `M_0`.  This file
records their defining equations and their nonnegativity, the two elementary facts used whenever
`W^±` is consumed.  These are the elementary parts of the weak estimate
`e.response.weak.estimate`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- `W^-` is the weak energy of the recentred coefficient `a_- = a - g` at the load `q^-`: by
definition `W^- = W(U_t, p, q^-; a_-, Y^-)` for the weak response energy `W`. -/
theorem respWMinus_eq {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) :
    respWMinus P jStar F t e
      = respWeakEnergy P (respGrid jStar F) t (respM0 F) (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F) (respYMinus P jStar F t e) := rfl

/-- `W^+` is the weak energy of the recentred coefficient `a_+ = a^t + g` at the load `q^+`: by
definition `W^+ = W(U_t, p, q^+; a_+, Y^+)` for the weak response energy `W`. -/
theorem respWPlus_eq {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (e : Vec d) :
    respWPlus P jStar F t e
      = respWeakEnergy P (respGrid jStar F) t (respM0 F) (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F) (respYPlus P jStar F t e) := rfl

/-- The weak response quantity `W^-` is nonnegative: it is the weak energy of the recentred
coefficient `a_-` at the load `q^-`. -/
theorem respWMinus_nonneg {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) : 0 ≤ respWMinus P jStar F t e := by
  rw [respWMinus_eq]
  exact respWeakEnergy_nonneg P (respGrid jStar F) t (respM0 F)
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F)
    (respYMinus P jStar F t e)

/-- The weak response quantity `W^+` is nonnegative: it is the weak energy of the recentred
coefficient `a_+` at the load `q^+`. -/
theorem respWPlus_nonneg {d : ℕ} (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (e : Vec d) : 0 ≤ respWPlus P jStar F t e := by
  rw [respWPlus_eq]
  exact respWeakEnergy_nonneg P (respGrid jStar F) t (respM0 F)
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F)
    (respYPlus P jStar F t e)

end

end Homogenization.HighContrast.Multiscale
