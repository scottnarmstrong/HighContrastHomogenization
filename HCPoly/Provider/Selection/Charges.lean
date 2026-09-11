/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Work
import HCPoly.Provider.Selection.Transitions

/-!
# Determinant charges of selector transitions

Each nonterminal rule is charged by the determinant-root losses of the
fixed-grid intervals it reads.  A terminal decision carries no charge.  The
normalization chosen before the law dominates every determinant slope used in
the progress estimates.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-! ## The normalized structural constant -/

/-- The directional slopes selected before the law are bounded by
`C_dir`. -/
theorem directionalSlope_bounds :
    (initExpQ d g : ℝ) * (d : ℝ) ≤ c.Cdir ∧
      c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) ≤ c.Cdir ∧
        (d : ℝ) / Real.log 2 ≤ c.Cdir := by
  rw [c.Cdir_eq]
  exact ⟨le_max_left _ _,
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

/-- The normalized determinant coefficient dominates the directional,
projective, and unit slopes with the printed factors. -/
theorem normalizedConstant_bounds :
    4 * c.Cdir ≤ c.CdetBar ∧
      2 * (d : ℝ) ≤ c.CdetBar ∧ 4 ≤ c.CdetBar := by
  let M : ℝ := max c.Cdir (max ((d : ℝ) / 2) 1)
  have hM : 4 * M ≤ c.CdetBar := by
    simpa only [M] using c.CdetBar_lower
  have hdir : c.Cdir ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  have hdim : (d : ℝ) / 2 ≤ M := by
    dsimp [M]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hone : (1 : ℝ) ≤ M := by
    dsimp [M]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hfourDir := mul_le_mul_of_nonneg_left hdir (by norm_num : (0 : ℝ) ≤ 4)
  have hfourDim := mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)
  have hfourOne := mul_le_mul_of_nonneg_left hone (by norm_num : (0 : ℝ) ≤ 4)
  have hfour : (4 : ℝ) ≤ c.CdetBar := by
    simpa only [mul_one] using hfourOne.trans hM
  refine ⟨hfourDir.trans hM, ?_, hfour⟩
  nlinarith only [hfourDim, hM]

/-! ## The charge of one transition -/

/-- The normalized determinant charge attached to a selector rule. -/
def transitionCharge (P : Measure (CoeffSpace d)) (h : ℤ) (l0 H : ℕ)
    (S : State d) : TransitionRule → ℝ
  | .t1 => detLoss P S.q S.cursor (S.cursor + h)
  | .t2 => detLoss P S.q S.cursor (S.cursor + h) +
      serviceWindowCharge P S.q h S.cursor
  | .t3 => detLoss P S.q S.cursor (S.cursor + h) +
      serviceWindowCharge P S.q h S.cursor
  | .t4 => detLoss P S.q S.cursor (S.cursor + 2 * (l0 : ℤ))
  | .t5 => detLoss P S.q S.cursor (S.cursor + 2 * (l0 : ℤ)) +
      detLoss P S.q S.base (S.cursor + 2 * (l0 : ℤ))
  | .t6 => detLoss P S.q S.base (S.base + max (H : ℤ) h)
  | .t7 => 0

/-- Defining equations for the normalized transition charge. -/
theorem transitionCharge_eq (P : Measure (CoeffSpace d)) (h : ℤ) (l0 H : ℕ)
    (S : State d) (rule : TransitionRule) :
    transitionCharge P h l0 H S rule =
      match rule with
      | .t1 => detLoss P S.q S.cursor (S.cursor + h)
      | .t2 => detLoss P S.q S.cursor (S.cursor + h) +
          serviceWindowCharge P S.q h S.cursor
      | .t3 => detLoss P S.q S.cursor (S.cursor + h) +
          serviceWindowCharge P S.q h S.cursor
      | .t4 => detLoss P S.q S.cursor (S.cursor + 2 * (l0 : ℤ))
      | .t5 => detLoss P S.q S.cursor (S.cursor + 2 * (l0 : ℤ)) +
          detLoss P S.q S.base (S.cursor + 2 * (l0 : ℤ))
      | .t6 => detLoss P S.q S.base (S.base + max (H : ℤ) h)
      | .t7 => 0 := by
  cases rule <;> rfl

/-- Mean order and endpoint positivity make a determinant-root loss
nonnegative. -/
theorem detLoss_nonneg_of_meanOrder {P : Measure (CoeffSpace d)} {q : Mat d}
    {u v : ℤ}
    (hEu : Book.Ch02.BlockPosDef (adaptedMean P q u))
    (hEv : Book.Ch02.BlockPosDef (adaptedMean P q v))
    (hmono : BlockMatLoewnerLE (adaptedMean P q v) (adaptedMean P q u)) :
    0 ≤ detLoss P q u v := by
  have hU : (toFullBlockMat (adaptedMean P q u)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q u) hEu
  have hV : (toFullBlockMat (adaptedMean P q v)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q v) hEv
  have hroot := ShortHop.detRoot_le_of_blockMatLoewnerLE hV hU
    (le_of_blockMatLoewnerLE (Recurrence.isSymmetricBlockMat_adaptedMean P q v)
      (Recurrence.isSymmetricBlockMat_adaptedMean P q u) hmono)
  rw [detLoss]
  exact sub_nonneg.mpr (Real.log_le_log (ShortHop.detRoot_pos hV) hroot)

/-- The logarithm of an adapted determinant-root ratio is its normalized
determinant loss. -/
theorem log_adaptedDetRoot_div_eq_detLoss {P : Measure (CoeffSpace d)}
    {q : Mat d} {u v : ℤ}
    (hu : (toFullBlockMat (adaptedMean P q u)).PosDef)
    (hv : (toFullBlockMat (adaptedMean P q v)).PosDef) :
    Real.log (adaptedDetRoot P q u / adaptedDetRoot P q v) =
      detLoss P q u v := by
  rw [detLoss]
  exact Real.log_div (ShortHop.detRoot_pos hu).ne' (ShortHop.detRoot_pos hv).ne'

/-- A full log-determinant increment is `d` times the normalized
determinant-root loss. -/
theorem detIncrement_eq_natCast_mul_detLoss (hd : d ≠ 0)
    {P : Measure (CoeffSpace d)} {q : Mat d} {u v : ℤ}
    (hU : (toFullBlockMat (adaptedMean P q u)).PosDef)
    (hV : (toFullBlockMat (adaptedMean P q v)).PosDef) :
    detIncrement P q u v = (d : ℝ) * detLoss P q u v := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hlogU : Real.log (adaptedDetRoot P q u) =
      (d : ℝ)⁻¹ * Real.log (toFullBlockMat (adaptedMean P q u)).det := by
    rw [adaptedDetRoot, detRoot, Real.log_rpow hU.det_pos, mul_comm]
  have hlogV : Real.log (adaptedDetRoot P q v) =
      (d : ℝ)⁻¹ * Real.log (toFullBlockMat (adaptedMean P q v)).det := by
    rw [adaptedDetRoot, detRoot, Real.log_rpow hV.det_pos, mul_comm]
  change Real.log (toFullBlockMat (adaptedMean P q u)).det -
      Real.log (toFullBlockMat (adaptedMean P q v)).det = _
  rw [detLoss, hlogU, hlogV, mul_sub,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hdR, one_mul, one_mul]

/-- The portable-history synchronized charge is the unnormalized form of the
service-window charge. -/
theorem synchCharge_eq_natCast_mul_serviceWindowCharge (hd : d ≠ 0)
    {P : Measure (CoeffSpace d)} {q : Mat d} {h u : ℤ} (hh : 1 ≤ h)
    (hpos : ∀ j : ℤ, u + 1 - h ≤ j → j ≤ u + h →
      (toFullBlockMat (adaptedMean P q j)).PosDef) :
    synchCharge P q h u = (d : ℝ) * serviceWindowCharge P q h u := by
  rw [synchCharge, serviceWindowCharge_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjbounds := Finset.mem_Icc.mp hj
  rw [detIncrement_eq_natCast_mul_detLoss hd
    (hpos (j - h) (by omega) (by omega))
    (hpos j (by omega) (by omega))]

end

end Selection
end HighContrast
end Homogenization
