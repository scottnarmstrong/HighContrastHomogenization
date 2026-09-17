import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The crossed pairing of a weighted flat average of expectations

The cell part of the cutoff-mean defect of `p.response.transfer` is a weighted flat average,
over the coarse subcells of the terminal cell, of the annealed cell means of the doubled
optimizer state.  Because the crossed pairing is bilinear and both the finite flat average and
the expectation are linear, pairing the flat average against the dual variable `Y` — the gradient
slot against `Y.2` and the flux slot against `Y.1` — is the expectation of the weighted flat
average of the pathwise crossed pairings.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The crossed pairing of a weighted flat average of expectations.**  Let `Z` be a finite
index set, `c` a real weight, `M` a family of doubled vectors indexed by `Z` and the sample space,
and let `N` be the doubled vector whose two slots are the weighted flat averages of the
expectations of the corresponding slots of `M`.  Then the crossed pairing of `N` against `Y`
(gradient slot against `Y.2`, flux slot against `Y.1`) equals the expectation of the weighted
flat average of the pathwise crossed pairings.  This is the exchange of the finite average with
the expectation used in `p.response.transfer`. -/
theorem vecDot_avsum_integral_eq_integral_avsum_pairing {d : ℕ} {ι α : Type*}
    [MeasurableSpace α] (P : Measure α) (Z : Finset ι) (c : ι → ℝ) (Y : BlockVec d)
    (M : ι → α → BlockVec d) (N : BlockVec d)
    (hN1 : N.1 = fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (M w a).1 i ∂P)
    (hN2 : N.2 = fun i => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * ∫ a, (M w a).2 i ∂P)
    (hint1 : ∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (M w a).1 i) P)
    (hint2 : ∀ w ∈ Z, ∀ i : Fin d, Integrable (fun a => (M w a).2 i) P) :
    vecDot N.1 Y.2 + vecDot Y.1 N.2
      = ∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
          c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2) ∂P := by
  -- Integrability of the two pathwise pairings at each cell.
  have hpair1 : ∀ w ∈ Z, Integrable (fun a => vecDot (M w a).1 Y.2) P := by
    intro w hw
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ fun i _ => (hint1 w hw i).mul_const (Y.2 i)
  have hpair2 : ∀ w ∈ Z, Integrable (fun a => vecDot Y.1 (M w a).2) P := by
    intro w hw
    simp only [vecDot]
    exact integrable_finsetSum Finset.univ fun i _ => (hint2 w hw i).const_mul (Y.1 i)
  have hsummand : ∀ w ∈ Z, Integrable (fun a =>
      c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2)) P :=
    fun w hw => ((hpair1 w hw).add (hpair2 w hw)).const_mul (c w)
  -- The integral of each pathwise pairing is the pairing of the expected slot.
  have hint_dot1 : ∀ w ∈ Z, (∫ a, vecDot (M w a).1 Y.2 ∂P)
      = vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2 := by
    intro w hw
    simp only [vecDot]
    rw [integral_finsetSum Finset.univ fun i _ => (hint1 w hw i).mul_const (Y.2 i)]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const]
  have hint_dot2 : ∀ w ∈ Z, (∫ a, vecDot Y.1 (M w a).2 ∂P)
      = vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P) := by
    intro w hw
    simp only [vecDot]
    rw [integral_finsetSum Finset.univ fun i _ => (hint2 w hw i).const_mul (Y.1 i)]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
  -- The pairing is linear over the weighted finite average.
  have hdot_wsum : ∀ (x : ι → Vec d) (y : Vec d),
      vecDot (fun i => ∑ w ∈ Z, c w * x w i) y = ∑ w ∈ Z, c w * vecDot (x w) y := by
    intro x y
    simp only [vecDot, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun i _ => by ring
  -- The left-hand side, with the defining averages substituted.
  have hL1 : vecDot N.1 Y.2
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2 := by
    rw [hN1]
    change vecDot (((Z.card : ℝ))⁻¹ •
        (fun i => ∑ w ∈ Z, c w * ∫ a, (M w a).1 i ∂P)) Y.2
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2
    rw [vecDot_smul_left, hdot_wsum]
  have hL2 : vecDot N.2 Y.1
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P) := by
    rw [hN2]
    change vecDot (((Z.card : ℝ))⁻¹ •
        (fun i => ∑ w ∈ Z, c w * ∫ a, (M w a).2 i ∂P)) Y.1
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w * vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P)
    rw [vecDot_smul_left, hdot_wsum]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [vecDot_comm]
  have hL : vecDot N.1 Y.2 + vecDot Y.1 N.2
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w *
          (vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2
            + vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P)) := by
    rw [vecDot_comm Y.1 N.2, hL1, hL2, ← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [← mul_add]
  -- The right-hand side, with the integral moved inside the weighted average.
  have hR : (∫ a, ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z,
        c w * (vecDot (M w a).1 Y.2 + vecDot Y.1 (M w a).2) ∂P)
      = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, c w *
          (vecDot (fun i => ∫ a, (M w a).1 i ∂P) Y.2
            + vecDot Y.1 (fun i => ∫ a, (M w a).2 i ∂P)) := by
    rw [integral_const_mul, integral_finsetSum Z hsummand]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [integral_const_mul, integral_add (hpair1 w hw) (hpair2 w hw),
      hint_dot1 w hw, hint_dot2 w hw]
  rw [hR]
  exact hL

end

end Homogenization.HighContrast.Multiscale
