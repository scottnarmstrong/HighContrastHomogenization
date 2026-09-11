/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.DeterminantPrefix
import HCPoly.Provider.Selection.TransitionTrace
import HCPoly.Provider.ShortHop.PathStep

/-!
# Projective hop prefixes

The selector records projective hops only in its trace.  This file supplies the
constant-speed residual estimate for the fixed path and a proof-only
certificate for the completed hop prefix.  The certificate is not part of the
selector state or of the final theorem.
-/

namespace Homogenization.HighContrast.Selection

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

private theorem matPow_eq_rpow {A : Mat d} (hA : A.PosDef) (theta : ℝ) :
    matPow theta A = A ^ theta := by
  unfold matPow
  exact (CFC.rpow_eq_cfc_real (a := A) (y := theta)
    (ha := by exact Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef)).symm

private theorem projDist_congr [Nonempty (Fin d)] {P Q C : Mat d}
    (hP : P.PosDef) (hQ : Q.PosDef) (hC : IsUnit C) :
    projDist (Cᴴ * P * C) (Cᴴ * Q * C) = projDist P Q := by
  rw [projDist_def,
    relSize_congr hQ.posSemidef hP hC,
    relSize_congr hP.posSemidef hQ hC, projDist_def]

private theorem rpow_three {A : Mat d} (hA : A.PosDef) (x y z : ℝ) :
    A ^ x * A ^ y * A ^ z = A ^ (x + y + z) := by
  have hunit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_det_of_posDef hA)
  rw [← CFC.rpow_add hunit, ← CFC.rpow_add hunit]

private theorem projPath_one_base [Nonempty (Fin d)] (A : Mat d) (theta : ℝ) :
    projPath 1 A theta = matPow theta A := by
  rw [projPath]
  simp only [Recurrence.matSqrt_one, inv_one, Matrix.one_mul, Matrix.mul_one]

/-- The remaining distance from a path point to its target is at most the
unused fraction of the original projective distance. -/
theorem projDist_projPath_target_le [Nonempty (Fin d)] {m0 m1 : Mat d}
    (h0 : m0.PosDef) (h1 : m1.PosDef) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    projDist (projPath m0 m1 theta) m1 ≤
      (1 - theta) * projDist m0 m1 := by
  let X : Mat d := matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹
  let Y : Mat d := matPow theta X
  let Z : Mat d := matPow (theta / 2) X
  let C : Mat d := Z⁻¹
  have hX : X.PosDef := posDef_normalize h1 h0
  have hY : Y.PosDef := ShortHop.posDef_matPow hX htheta0
  have hZ : Z.PosDef := ShortHop.posDef_matPow hX (by linarith only [htheta0])
  have hC : C.PosDef := hZ.inv
  have hCunit : IsUnit C :=
    (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_det_of_posDef hC)
  have hSunit : IsUnit (matSqrt m0) := isUnit_matSqrt h0
  have hSherm : (matSqrt m0)ᴴ = matSqrt m0 :=
    (matSqrt_spec h0.posSemidef).1.isHermitian
  have hCherm : Cᴴ = C := hC.isHermitian
  have hZdet : IsUnit Z.det := isUnit_det_of_posDef hZ
  have hCZ : C * Z = 1 := by
    dsimp [C]
    exact Matrix.nonsing_inv_mul _ hZdet
  have hZC : Z * C = 1 := by
    dsimp [C]
    exact Matrix.mul_nonsing_inv _ hZdet
  have hYeq : Y = Z * Z := by
    dsimp [Y, Z]
    simp only [matPow_eq_rpow hX]
    rw [← CFC.rpow_add
      ((Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_det_of_posDef hX))]
    congr 1
    ring
  have hXeq : X = Z * matPow (1 - theta) X * Z := by
    dsimp [Z]
    simp only [matPow_eq_rpow hX]
    rw [rpow_three hX]
    have hexp : theta / 2 + (1 - theta) + theta / 2 = 1 := by ring
    rw [hexp, CFC.rpow_one X
      (ha := by exact Matrix.nonneg_iff_posSemidef.mpr hX.posSemidef)]
  have hCY : C * Y * C = 1 := by
    rw [hYeq]
    calc
      C * (Z * Z) * C = (C * Z) * (Z * C) := by noncomm_ring
      _ = 1 := by rw [hCZ, hZC, Matrix.one_mul]
  have hCX : C * X * C = matPow (1 - theta) X := by
    conv_lhs => rw [hXeq]
    calc
      C * (Z * matPow (1 - theta) X * Z) * C =
          (C * Z) * matPow (1 - theta) X * (Z * C) := by noncomm_ring
      _ = matPow (1 - theta) X := by rw [hCZ, hZC, Matrix.one_mul, Matrix.mul_one]
  have hSX : matSqrt m0 * X * matSqrt m0 = m1 := by
    dsimp [X]
    have hunit : IsUnit (matSqrt m0).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hSunit
    have hleft : matSqrt m0 * matSqrt m0⁻¹ = 1 := by
      rw [matSqrt_inv h0]
      exact Matrix.mul_nonsing_inv _ hunit
    have hright : matSqrt m0⁻¹ * matSqrt m0 = 1 := by
      rw [matSqrt_inv h0]
      exact Matrix.nonsing_inv_mul _ hunit
    calc
      matSqrt m0 * (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) * matSqrt m0 =
          (matSqrt m0 * matSqrt m0⁻¹) * m1 *
            (matSqrt m0⁻¹ * matSqrt m0) := by noncomm_ring
      _ = m1 := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
  have hpath : projPath m0 m1 theta = matSqrt m0 * Y * matSqrt m0 := rfl
  have hfirst : projDist (projPath m0 m1 theta) m1 = projDist Y X := by
    have hc := projDist_congr hY hX hSunit
    rw [hSherm, hSX] at hc
    exact (congrArg (fun A : Mat d => projDist A m1) hpath).trans hc
  have hsecond : projDist Y X = projDist 1 (matPow (1 - theta) X) := by
    have hc := projDist_congr hY hX hCunit
    rw [hCherm, hCY, hCX] at hc
    exact hc.symm
  have hthird : projDist 1 (matPow (1 - theta) X) ≤
      (1 - theta) * projDist 1 X := by
    rw [← projPath_one_base X (1 - theta)]
    exact ShortHop.projDist_projPath_le Matrix.PosDef.one hX
      (by linarith only [htheta1])
  have hbase : projDist 1 X = projDist m0 m1 := by
    have hsquare : matSqrt m0 * matSqrt m0 = m0 :=
      (matSqrt_spec h0.posSemidef).2
    have hc := projDist_congr Matrix.PosDef.one hX hSunit
    rw [hSherm, Matrix.mul_one, hsquare, hSX] at hc
    exact hc.symm
  calc
    projDist (projPath m0 m1 theta) m1 = projDist Y X := hfirst
    _ = projDist 1 (matPow (1 - theta) X) := hsecond
    _ ≤ (1 - theta) * projDist 1 X := hthird
    _ = (1 - theta) * projDist m0 m1 := by rw [hbase]

/-- The endpoint of the fixed path is the target matrix. -/
theorem projPath_one [Nonempty (Fin d)] {m0 m1 : Mat d}
    (h0 : m0.PosDef) (h1 : m1.PosDef) : projPath m0 m1 1 = m1 := by
  have hunit : IsUnit (matSqrt m0).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_matSqrt h0)
  have hleft : matSqrt m0 * matSqrt m0⁻¹ = 1 := by
    rw [matSqrt_inv h0]
    exact Matrix.mul_nonsing_inv _ hunit
  have hright : matSqrt m0⁻¹ * matSqrt m0 = 1 := by
    rw [matSqrt_inv h0]
    exact Matrix.nonsing_inv_mul _ hunit
  have hpow : matPow 1 (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) =
      matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹ := by
    rw [matPow_eq_rpow (posDef_normalize h1 h0)]
    exact CFC.rpow_one _ (ha := by
      exact Matrix.nonneg_iff_posSemidef.mpr
        (posDef_normalize h1 h0).posSemidef)
  rw [projPath, hpow]
  calc
    matSqrt m0 * (matSqrt m0⁻¹ * m1 * matSqrt m0⁻¹) * matSqrt m0 =
        (matSqrt m0 * matSqrt m0⁻¹) * m1 *
          (matSqrt m0⁻¹ * matSqrt m0) := by noncomm_ring
    _ = m1 := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]

/-- A completed path step is exactly the target endpoint. -/
theorem projPathStep_eq_target [Nonempty (Fin d)] {chop : ℝ}
    {m0 m1 : Mat d} (h0 : m0.PosDef) (h1 : m1.PosDef)
    (hfinal : projDist m0 m1 ≤ chop) : projPathStep chop m0 m1 = m1 := by
  rw [projPathStep]
  split_ifs with hz
  · rfl
  · have hD : 0 < projDist m0 m1 :=
      lt_of_le_of_ne (projDist_nonneg h0 h1) (Ne.symm hz)
    have hratio : 1 ≤ chop / projDist m0 m1 := by
      rw [le_div_iff₀ hD]
      simpa only [one_mul] using hfinal
    rw [min_eq_right hratio, projPath_one h0 h1]

/-- A nonfinal path step leaves at most the old distance minus one hop to its
target. -/
theorem projDist_projPathStep_target_le [Nonempty (Fin d)] {chop : ℝ}
    (hchop : 0 < chop) {m0 m1 : Mat d} (h0 : m0.PosDef) (h1 : m1.PosDef)
    (hnonfinal : chop < projDist m0 m1) :
    projDist (projPathStep chop m0 m1) m1 ≤ projDist m0 m1 - chop := by
  have hD : 0 < projDist m0 m1 := hchop.trans hnonfinal
  have hz : projDist m0 m1 ≠ 0 := hD.ne'
  have hratio : chop / projDist m0 m1 < 1 :=
    (div_lt_one hD).mpr hnonfinal
  rw [projPathStep, if_neg hz, min_eq_left hratio.le]
  have hpath := projDist_projPath_target_le h0 h1
    (div_nonneg hchop.le hD.le) hratio.le
  calc
    projDist (projPath m0 m1 (chop / projDist m0 m1)) m1 ≤
        (1 - chop / projDist m0 m1) * projDist m0 m1 := hpath
    _ = projDist m0 m1 - chop := by field_simp

/-- Data carried only by the proof of a finite hop prefix.  Its stages retain
the actual grids, scales, bridge errors, and completed determinant summaries. -/
structure HopPrefixCertificate (P : MeasureTheory.Measure (CoeffSpace d))
    (jStar : ℤ) (chop Khop : ℝ) (l0 : ℕ) (r0 : ℤ) (k : ℕ) where
  mus : ℕ → Mat d
  grids : ℕ → Mat d
  starts : ℕ → ℤ
  terminals : ℕ → ℤ
  eta : ℕ → ℝ
  mus_pos : ∀ i : ℕ, i ≤ k → (mus i).PosDef
  mus_zero : mus 0 = 1
  grids_eq : ∀ i : ℕ, i ≤ k → grids i = roundedGrid jStar (mus i)
  starts_zero : r0 ≤ starts 0
  scale_step : ∀ i : ℕ, i < k → starts i + (l0 : ℤ) ≤ starts (i + 1)
  hop_step : ∀ i : ℕ, i < k → projDist (mus i) (mus (i + 1)) ≤ chop
  grid_step : ∀ i : ℕ, i < k → gridRatio (grids i) (grids (i + 1)) ≤ Khop
  eta_nonneg : ∀ i : ℕ, i < k → 0 ≤ eta i
  eta_le : ∀ i : ℕ, i < k → eta i ≤ 1 / 4
  terminal_ge : ∀ i : ℕ, i < k → starts i ≤ terminals i
  completedLoss : ℝ
  completedLoss_eq : completedLoss =
    ∑ i ∈ Finset.range k, detLoss P (grids i) (starts i) (terminals i)

/-- The recorded scale recursion places the current hop start at least `k`
buffers beyond the initial entry scale. -/
theorem HopPrefixCertificate.scale_lower
    {P : MeasureTheory.Measure (CoeffSpace d)} {jStar : ℤ}
    {chop Khop : ℝ} {l0 : ℕ} {r0 : ℤ} {k : ℕ}
    (h : HopPrefixCertificate P jStar chop Khop l0 r0 k) :
    r0 + (k : ℤ) * (l0 : ℤ) ≤ h.starts k := by
  have hrec : h.starts 0 + (k : ℤ) * (l0 : ℤ) ≤ h.starts k :=
    ShortHop.scale_recursion h.scale_step
  calc
    r0 + (k : ℤ) * (l0 : ℤ) ≤
        h.starts 0 + (k : ℤ) * (l0 : ℤ) := by
      simpa only [add_comm] using
        add_le_add_right h.starts_zero ((k : ℤ) * (l0 : ℤ))
    _ ≤ h.starts k := hrec

/-- Adding the current partial loss to the completed summary gives the printed
determinant-prefix expression. -/
theorem HopPrefixCertificate.completedLoss_add_current
    {P : MeasureTheory.Measure (CoeffSpace d)} {jStar : ℤ}
    {chop Khop : ℝ} {l0 : ℕ} {r0 : ℤ} {k : ℕ}
    (h : HopPrefixCertificate P jStar chop Khop l0 r0 k) (u : ℤ) :
    h.completedLoss + detLoss P (h.grids k) (h.starts k) u =
      determinantPrefix P h.grids h.starts h.terminals k u := by
  rw [determinantPrefix_eq, h.completedLoss_eq]

end

end Homogenization.HighContrast.Selection
