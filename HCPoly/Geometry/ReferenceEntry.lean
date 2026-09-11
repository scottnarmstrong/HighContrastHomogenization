/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.DeterminantLoss
import HCPoly.Geometry.CanonicalDeterminant
import HCPoly.Geometry.ReferenceRadius

/-!
# The entry comparison against a reference block

The second half of `e.initial.geometry.bounds` compares the canonical
metric of an entry block `A_0` with that of the reference block, through the
determinant ratio `ϱ_0` between the reference block and the entry block.  The
two facts proved here are the entry comparison `1 ≤ ϱ_0 ≤ κ_{\rm ref}` together
with `d_pr([m_{\rm ref}], [m(A_0)]) ≤ (d/2) log κ_{\rm ref}`, and the entry
radius of that same display.

The comparison is `e.global.selection.metric.loss` applied with `F = A_0` and
`E = E_{\rm ref}`, together with the two determinant bounds for the canonical
metric: `det(A_0) ≥ 1` because `A_0^♯ ≤ A_0`, and
`det(E_{\rm ref}) ≤ 𝔡(E_{\rm ref})^d = κ_{\rm ref}^d`.

The entry radius additionally needs the factor-six reference-block comparison
`κ_{\rm ref} ≤ 6Π`, which `s.introduction` takes from HC and which is not proved
here; it enters as the hypothesis `hkap`.
-/

namespace Homogenization
namespace HighContrast

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-- A real step kept apart from the matrices: dividing by a factor at least one
does not increase a nonnegative quantity. -/
private theorem div_le_self_of_one_le {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) :
    x / y ≤ x := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  rw [div_le_iff₀ hy0]
  nlinarith only [hx, hy]

/-- **The entry ratio is between one and the reference imbalance**, the first
half of the entry comparison. -/
theorem canonDetRatio_le_canonImbalance (hd : 2 ≤ d) {Eref A₀ : FullBlockMat d}
    (hE : Eref.PosDef) (hA : A₀.PosDef) (hle : A₀ ≤ Eref)
    (hEsharp : fullBlockSharp Eref ≤ Eref) (hAsharp : fullBlockSharp A₀ ≤ A₀)
    [Nonempty (Fin d)] :
    1 ≤ canonDetRatio Eref A₀ ∧ canonDetRatio Eref A₀ ≤ canonImbalance Eref := by
  have hdpos : 0 < d := lt_of_lt_of_le two_pos hd
  have hquot : (0 : ℝ) ≤ Eref.det / A₀.det := (div_pos hE.det_pos hA.det_pos).le
  have hone := (canonDeterminantLoss_canonDetRatio hd hE hA hle).1
  refine ⟨hone, ?_⟩
  have hpow : canonDetRatio Eref A₀ ^ d ≤ canonImbalance Eref ^ d := by
    rw [canonDetRatio_pow hdpos.ne' hquot]
    have h1 : (1 : ℝ) ≤ A₀.det := one_le_det_of_fullBlockSharp_le hA hAsharp
    have h2 : Eref.det ≤ canonImbalance Eref ^ d :=
      det_le_canonImbalance_pow hE hEsharp
    have h3 : Eref.det / A₀.det ≤ Eref.det := div_le_self_of_one_le hE.det_pos.le h1
    linarith only [h2, h3]
  exact le_of_pow_le_pow_left₀ hdpos.ne' (canonImbalance_nonneg Eref) hpow

/-- **The entry comparison**, second half: the canonical metrics of the entry
block and of the reference block
are at projective distance at most `(d/2) log κ_{\rm ref}`. -/
theorem projDist_canonMetric_entry (hd : 2 ≤ d) {Eref A₀ : FullBlockMat d}
    (hE : Eref.PosDef) (hA : A₀.PosDef) (hle : A₀ ≤ Eref)
    (hEsharp : fullBlockSharp Eref ≤ Eref) (hAsharp : fullBlockSharp A₀ ≤ A₀)
    [Nonempty (Fin d)] :
    projDist (canonMetric Eref) (canonMetric A₀) ≤
      ((d : ℝ) / 2) * Real.log (canonImbalance Eref) := by
  obtain ⟨hone, hle'⟩ :=
    canonDetRatio_le_canonImbalance hd hE hA hle hEsharp hAsharp
  have hstep := (canonDeterminantLoss_canonDetRatio hd hE hA hle).2.2.2.2
  have hlog : Real.log (canonDetRatio Eref A₀) ≤ Real.log (canonImbalance Eref) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hone) hle'
  have hd2 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  exact hstep.trans (mul_le_mul_of_nonneg_left hlog hd2)

end

end HighContrast
end Homogenization
