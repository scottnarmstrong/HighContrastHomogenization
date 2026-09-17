import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportProj
import HCPoly.Entry.Setup.AdaptedGrid
import HCPoly.Entry.Geometry.AdaptedCell
import HCPoly.Entry.Geometry.StandardCell
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The oscillation of a response cutoff across a descendant adapted cell

The scale gain `3^-H` of the cutoff estimate `p.response.transfer` comes from the derivative
scale carried by the cutoff class `IsResponseCutoff`: the pullback `y ↦ φ (qq y)` is Lipschitz
with constant `32 d^2 Θ 3^(-t)`, so across a cell of generation `t - n` of `q`-diameter
`3^(t-n)` a cutoff can vary by at most that constant times `3^(t-n)`, i.e. by at most
`32 d^2 Θ 3^(-n)`.  This is proved here uniformly in the generation `t`, the aligned index `w`
and the grid `qq`, together with its `n = 0` specialization to a single adapted cell.
-/

open Homogenization.HighContrast (adaptedCellCenter)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Across two points of a descendant adapted cell `adaptedCellAtCenter qq (t - n) w`, a
cutoff `φ` of the response class `IsResponseCutoff qq t φ` oscillates by at most
`32 d^2 responseCutoffProfileConst 3^(-n)`: the Lipschitz scale `3^(-t)` of the cutoff class,
applied on the cell of generation `t - n`, loses exactly the `n` generations of the descent. -/
theorem abs_sub_le_of_mem_adaptedCellAtCenter {d : ℕ} {qq : Mat d} (hq : IsUnit qq) {t : ℤ}
    {φ : Vec d → ℝ} (h : IsResponseCutoff qq t φ) (n : ℕ) (w : Fin d → ℤ)
    {x y : Vec d} (hx : x ∈ adaptedCellAtCenter qq (t - (n : ℤ)) w)
    (hy : y ∈ adaptedCellAtCenter qq (t - (n : ℤ)) w) :
    |φ x - φ y| ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := by
  obtain ⟨v, hv, hxv⟩ :=
    Geometry.mem_adaptedCellTranslate_iff.mp
      (show x ∈ HighContrast.adaptedCellTranslate qq (t - (n : ℤ))
          (adaptedCellCenter qq (t - (n : ℤ)) w) from hx)
  obtain ⟨u, hu, hyu⟩ :=
    Geometry.mem_adaptedCellTranslate_iff.mp
      (show y ∈ HighContrast.adaptedCellTranslate qq (t - (n : ℤ))
          (adaptedCellCenter qq (t - (n : ℤ)) w) from hy)
  set z : Vec d := adaptedCellCenter qq (t - (n : ℤ)) w with hzdef
  set z' : Vec d := matVecMul qq⁻¹ z with hz'def
  have hz : matVecMul qq z' = z := by
    have hdet : IsUnit qq.det := (Matrix.isUnit_iff_isUnit_det qq).mp hq
    rw [hz'def, Geometry.matVecMul_eq_mulVec, Geometry.matVecMul_eq_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv qq hdet, Matrix.one_mulVec]
  have hxv' : x = matVecMul qq (z' + v) := by
    rw [← hxv, ← hz, matVecMul_add]
  have hyu' : y = matVecMul qq (z' + u) := by
    rw [← hyu, ← hz, matVecMul_add]
  have hdist : dist (z' + v) (z' + u) = ‖v - u‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  have hvu : ‖v - u‖ ≤ (3 : ℝ) ^ (t - (n : ℤ)) := by
    rw [pi_norm_le_iff_of_nonneg (zpow_nonneg (by norm_num) _)]
    intro i
    rw [Real.norm_eq_abs]
    have hv1 : -((1 / 2 : ℝ) * (3 : ℝ) ^ (t - (n : ℤ))) < v i := by
      have h := (Geometry.mem_centeredCube_iff.mp hv i).1
      linarith
    have hv2 : v i < (1 / 2 : ℝ) * (3 : ℝ) ^ (t - (n : ℤ)) :=
      (Geometry.mem_centeredCube_iff.mp hv i).2
    have hu1 : -((1 / 2 : ℝ) * (3 : ℝ) ^ (t - (n : ℤ))) < u i := by
      have h := (Geometry.mem_centeredCube_iff.mp hu i).1
      linarith
    have hu2 : u i < (1 / 2 : ℝ) * (3 : ℝ) ^ (t - (n : ℤ)) :=
      (Geometry.mem_centeredCube_iff.mp hu i).2
    have hlt : |v i - u i| < (3 : ℝ) ^ (t - (n : ℤ)) := by
      rw [abs_lt]
      constructor <;> linarith
    exact hlt.le
  have hL : (0 : ℝ) ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t) := by
    have hd : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
    have hΘ : (0 : ℝ) ≤ responseCutoffProfileConst := responseCutoffProfileConst_pos.le
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-t) := zpow_nonneg (by norm_num) (-t)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hd) hΘ) h3
  have harith : (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) *
      (3 : ℝ) ^ (t - (n : ℤ)) =
      32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := by
    have h3 : (3 : ℝ) ≠ 0 := by norm_num
    have hrn : (3 : ℝ) ^ (-(n : ℤ)) = (3 : ℝ) ^ (-(n : ℝ)) := by
      rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ))]
      congr 1
      push_cast
      ring
    calc
      (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) *
          (3 : ℝ) ^ (t - (n : ℤ))
          = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst *
              ((3 : ℝ) ^ (-t) * (3 : ℝ) ^ (t - (n : ℤ))) := by ring
      _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst *
              (3 : ℝ) ^ (-t + (t - (n : ℤ))) := by rw [← zpow_add₀ h3]
      _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℤ)) := by
            rw [show -t + (t - (n : ℤ)) = -(n : ℤ) by ring]
      _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := by rw [hrn]
  calc
    |φ x - φ y| = dist (φ x) (φ y) := (Real.dist_eq _ _).symm
    _ = dist (φ (matVecMul qq (z' + v))) (φ (matVecMul qq (z' + u))) := by rw [hxv', hyu']
    _ ≤ (Real.toNNReal
            (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) : ℝ) *
          dist (z' + v) (z' + u) := h.lipschitz.dist_le_mul _ _
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) * ‖v - u‖ := by
          rw [Real.coe_toNNReal _ hL, hdist]
    _ ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-t)) *
          (3 : ℝ) ^ (t - (n : ℤ)) := mul_le_mul_of_nonneg_left hvu hL
    _ = 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := harith

end

end Homogenization.HighContrast.Multiscale
