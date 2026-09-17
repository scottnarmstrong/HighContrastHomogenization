import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import Homogenization.Sobolev.H1.BasicLemmas
import Homogenization.Sobolev.Foundations.MeanZero
import Mathlib.Tactic.FunProp

/-!
# The affine defect of an `H¹` function

Given an `H¹` function `u` on a bounded open convex domain `U`, a vector `P` and a
constant `c`, the affine defect `x ↦ u x - P · x - c` is again `H¹`, with gradient
`∇u - P`.  In the cutoff argument for `e.response.cutoff.estimate` the gradient
defect `∇v - P` of an optimizer is paired against a flux defect, and integration
by parts requires that this defect be the gradient of an `H¹` function: namely of
the affine defect of `v`, since the linear function `x ↦ P · x` and the constants
are `H¹` on a bounded domain and `H¹` is closed under subtraction.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The affine defect `x ↦ u x - vecDot P x - c` of an `H¹` function `u`,
packaged as an `H¹` function on `U`.  The linear function `x ↦ vecDot P x` is
globally smooth, hence `H¹` on the bounded domain `U`
(`H1Function.ofContDiffOnIsOpenBoundedConvexDomain`), and constants are `H¹` on
a finite-measure domain (`H1Function.const`). -/
def affineDefectH1 {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (u : H1Function U) (P : Vec d) (c : ℝ) : H1Function U :=
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  u - H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
        (f := fun x => vecDot P x) (by unfold vecDot; fun_prop)
    - H1Function.const c

/-- The underlying function of the affine defect is `x ↦ u x - vecDot P x - c`. -/
@[simp] theorem affineDefectH1_toFun {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (P : Vec d) (c : ℝ) :
    (affineDefectH1 hU u P c).toFun = fun x => u x - vecDot P x - c := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hlin :
      (H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
        (f := fun x => vecDot P x) (by unfold vecDot; fun_prop)).toFun =
        fun x => vecDot P x :=
    rfl
  funext x
  simp only [affineDefectH1, H1Function.sub_toFun, H1Function.const_apply, hlin]

/-- The gradient of the affine defect is `∇u - P`. -/
@[simp] theorem affineDefectH1_grad {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) (P : Vec d) (c : ℝ) :
    (affineDefectH1 hU u P c).grad = fun x => u.grad x - P := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hlin_grad :
      (H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
        (f := fun x => vecDot P x) (by unfold vecDot; fun_prop)).grad = fun _ => P := by
    funext x i
    change (fderiv ℝ (fun y : Vec d => vecDot P y) x) (basisVec i) = P i
    have hfd :
        fderiv ℝ (fun y : Vec d => vecDot P y) x =
          (∑ j : Fin d, P j • ContinuousLinearMap.proj (R := ℝ) j) := by
      rw [show (fun y : Vec d => vecDot P y) =
            (fun y => (∑ j : Fin d, P j • ContinuousLinearMap.proj (R := ℝ) j) y) by
          funext y
          simp only [vecDot, _root_.sum_apply, _root_.smul_apply,
            ContinuousLinearMap.proj_apply, smul_eq_mul]]
      exact ContinuousLinearMap.fderiv _
    rw [hfd]
    simp only [_root_.sum_apply, _root_.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [basisVec_apply, hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  funext x i
  simp only [affineDefectH1, H1Function.sub_grad, H1Function.grad_const, hlin_grad,
    Pi.sub_apply, Pi.zero_apply, sub_zero]

end

end Homogenization.HighContrast.Multiscale
