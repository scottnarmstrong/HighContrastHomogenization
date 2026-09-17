import HCPoly.Entry.Multiscale.ResponseInputs.OptimizerReadoutGlue
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentResponseField

/-!
# The Chapter-2 coefficient object on an aligned adapted subcell

`OptimizerReadoutGlue.lean` attaches to the parent adapted cell `⋄_t^q` a Chapter-2 coefficient
object whose raw field is the recentred response coefficient `a_- = a - g` (resp.
`a_+ = aᵀ + g`), and keeps that raw field definitionally equal to `respCoeffMinus` (resp.
`respCoeffPlus`).  This module performs the same construction on each aligned adapted subcell
`adaptedCellAtCenter q k w`, the per-`w` child carrier of the aligned subdivision.

The elliptic input on the subcell is obtained from
`Annealed.exists_elliptic_representative_adapted`, which covers every translated adapted cell
`adaptedCellTranslate q k y`, hence in particular `adaptedCellAtCenter q k w`.  The quantitative slice
cover then follows from `exists_responseSlice_of_ellipticRepresentative`.
-/

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## The elliptic representative on an aligned subcell -/

/-- The minus transformed coefficient `a_- = a - g` has, on the aligned adapted subcell
`adaptedCellAtCenter q k w`, an a.e.-equal representative that is uniformly elliptic there.  The
constants depend on the sample and on the cell only and enter no estimate. -/
theorem exists_elliptic_representative_respCoeffMinusAt [NeZero d] (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (adaptedCellAtCenter q k w) f ∧
        respCoeffMinus F a =ᵐ[volumeMeasureOn (adaptedCellAtCenter q k w)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => f x - respg F, hlam, ?_,
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0 : ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]

/-- The plus transformed coefficient `a_+ = aᵀ + g` has, on the aligned adapted subcell
`adaptedCellAtCenter q k w`, an a.e.-equal representative that is uniformly elliptic there. -/
theorem exists_elliptic_representative_respCoeffPlusAt [NeZero d] (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (adaptedCellAtCenter q k w) f ∧
        respCoeffPlus F a =ᵐ[volumeMeasureOn (adaptedCellAtCenter q k w)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq k (adaptedCellCenter q k w) a
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => matTranspose (f x) + respg F, hlam, ?_,
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0 : ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]

/-! ## The quantitative slice covers on the subcell -/

/-- The minus transformed coefficient lies in some quantitative slice on every aligned adapted
subcell. -/
theorem exists_responseSlice_selectionRespCoeffMinusRegAt [NeZero d]
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ j : ℕ, AEEQuantitativeEllipticSlice (adaptedCellAtCenter q k w) j
      (selectionRespCoeffMinusReg F a).toFun := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinusAt q hq k w F a
  exact exists_responseSlice_of_ellipticRepresentative
    (measurableSet_of_isEllipticFieldOn hEll) (selectionRespCoeffMinusReg F a)
    hlam hEll (by simpa only [selectionRespCoeffMinusReg_toFun] using hae)

/-- The plus transformed coefficient lies in some quantitative slice on every aligned adapted
subcell. -/
theorem exists_responseSlice_selectionRespCoeffPlusRegAt [NeZero d]
    (q : Mat d) (hq : IsUnit q) (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ j : ℕ, AEEQuantitativeEllipticSlice (adaptedCellAtCenter q k w) j
      (selectionRespCoeffPlusReg F a).toFun := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlusAt q hq k w F a
  exact exists_responseSlice_of_ellipticRepresentative
    (measurableSet_of_isEllipticFieldOn hEll) (selectionRespCoeffPlusReg F a)
    hlam hEll (by simpa only [selectionRespCoeffPlusReg_toFun] using hae)

/-! ## The canonical subcell coefficient objects -/

/-- Canonical Chapter-2 coefficient object for the minus transformed response field on the aligned
adapted subcell `adaptedCellAtCenter q k w`. -/
def canonicalRespCoeffMinusOnAt [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    Book.Ch02.CoeffOn (adaptedDomainAt q hq k w) :=
  responseCoeffOnFromSliceCover (adaptedDomainAt q hq k w) (selectionRespCoeffMinusReg F a)
    (exists_responseSlice_selectionRespCoeffMinusRegAt q hq k w F a)

@[simp] theorem canonicalRespCoeffMinusOnAt_toFun [NeZero d] (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    (canonicalRespCoeffMinusOnAt q hq k w F a).toCoeffField = respCoeffMinus F a := by
  show (selectionRespCoeffMinusReg F a).toFun = respCoeffMinus F a
  exact selectionRespCoeffMinusReg_toFun F a

/-- Canonical Chapter-2 coefficient object for the plus transformed response field on the aligned
adapted subcell `adaptedCellAtCenter q k w`. -/
def canonicalRespCoeffPlusOnAt [NeZero d] (q : Mat d) (hq : IsUnit q) (k : ℤ)
    (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    Book.Ch02.CoeffOn (adaptedDomainAt q hq k w) :=
  responseCoeffOnFromSliceCover (adaptedDomainAt q hq k w) (selectionRespCoeffPlusReg F a)
    (exists_responseSlice_selectionRespCoeffPlusRegAt q hq k w F a)

@[simp] theorem canonicalRespCoeffPlusOnAt_toFun [NeZero d] (q : Mat d) (hq : IsUnit q)
    (k : ℤ) (w : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    (canonicalRespCoeffPlusOnAt q hq k w F a).toCoeffField = respCoeffPlus F a := by
  show (selectionRespCoeffPlusReg F a).toFun = respCoeffPlus F a
  exact selectionRespCoeffPlusReg_toFun F a

end

end Homogenization.HighContrast.Multiscale
