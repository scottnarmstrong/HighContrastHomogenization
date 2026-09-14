/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ShiftedFillRows
import HCPoly.Provider.PortableHistory.TraceGap

/-!
# Terminal trace rows for the shifted comparison

The shifted filling is read in the inverse geometry of the old-grid terminal
mean.  Each old mean is expanded into terminal increments before any scale sum
is taken.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem sum_Icc_sub_pred {M : Type*} [AddCommGroup M] (f : ℤ → M)
    {u v : ℤ} (huv : u ≤ v) :
    ∑ j ∈ Finset.Icc (u + 1) v, (f (j - 1) - f j) = f u - f v := by
  induction v, huv using Int.leInduction with
  | base =>
    have hempty : Finset.Icc (u + 1) u = (∅ : Finset ℤ) := by
      ext x
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and,
        not_le]
      omega
    rw [hempty, Finset.sum_empty, sub_self]
  | succ w hw ih =>
    have hins : Finset.Icc (u + 1) (w + 1) =
        insert (w + 1) (Finset.Icc (u + 1) w) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (w + 1) ∉ Finset.Icc (u + 1) w := by
      simp only [Finset.mem_Icc, not_and, not_le]
      omega
    rw [hins, Finset.sum_insert hnot, ih, add_sub_cancel_right]
    abel

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ}
  {Y : CoeffSpace d → ℝ}

/-- The continued shifted filling after terminal trace normalization.  Its
principal, boundary-increment, boundary-mass, and source terms remain separate
for the subsequent finite Abel sums. -/
theorem shifted_fill_trace_le [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {j l T : ℤ} (hl : 0 ≤ l) (hjl : jStar ≤ j - l) (hjT : j ≤ T)
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
      ∀ a : ℤ, jStar ≤ a → a ≤ T →
        adaptedCell r a ⊆ centeredCube d M) :
    Matrix.trace
        ((toFullBlockMat (adaptedMean P (roundedGrid jStar mp) T))⁻¹ *
          (toFullBlockMat (adaptedMean P (roundedGrid jStar mv) j) -
            toFullBlockMat (adaptedMean P (roundedGrid jStar mp) T))) ≤
      (∑ r ∈ Finset.Icc (j - l + 1) T,
        Matrix.trace
          ((toFullBlockMat (adaptedMean P (roundedGrid jStar mp) T))⁻¹ *
            (toFullBlockMat (adaptedMean P (roundedGrid jStar mp) (r - 1)) -
              toFullBlockMat (adaptedMean P (roundedGrid jStar mp) r)))) +
      6 * (d : ℝ) * Real.sqrt d *
        gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
          ∑ a ∈ Finset.Icc jStar (j - l - 1),
            (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) *
              (2 * (d : ℝ) +
                ∑ r ∈ Finset.Icc (a + 1) T,
                  Matrix.trace
                    ((toFullBlockMat
                      (adaptedMean P (roundedGrid jStar mp) T))⁻¹ *
                      (toFullBlockMat
                          (adaptedMean P (roundedGrid jStar mp) (r - 1)) -
                        toFullBlockMat
                          (adaptedMean P (roundedGrid jStar mp) r)))) +
      18 * (d : ℝ) * Real.sqrt d *
        bridgeContCoeff Cd g E jStar mp mv mp *
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) *
            (2 * (d : ℝ)) := by
  classical
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  let U : ℤ := j - l
  let A : FullBlockMat d := toFullBlockMat (adaptedMean P qp T)
  let F : ℤ → FullBlockMat d := fun a =>
    toFullBlockMat (adaptedMean P qp a)
  let V : FullBlockMat d := toFullBlockMat (adaptedMean P qv j)
  let x : ℤ → ℝ := fun r => Matrix.trace (A⁻¹ * (F (r - 1) - F r))
  let c : ℤ → ℝ := fun a =>
    6 * (d : ℝ) * Real.sqrt d * gridRatio qp qv * (3 : ℝ) ^ (a - j)
  let s : ℝ := 18 * (d : ℝ) * Real.sqrt d *
    bridgeContCoeff Cd g E jStar mp mv mp *
      (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ)))
  have hjj : jStar ≤ j := by omega
  have hjStarT : jStar ≤ T := hjj.trans hjT
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hApos : A.PosDef := by
    dsimp only [A]
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hqp T
      (Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hmp hqp hjStarT
        (hcont qp (Or.inl rfl) T hjStarT le_rfl))
  have hAunit : IsUnit A.det := isUnit_det_of_posDef hApos
  have htraceA : Matrix.trace (A⁻¹ * A) = 2 * (d : ℝ) := by
    rw [Matrix.nonsing_inv_mul _ hAunit, Matrix.trace_one]
    simp [Fintype.card_sum, two_mul]
  have hgap : ∀ a : ℤ, jStar ≤ a → a ≤ T →
      Matrix.trace (A⁻¹ * (F a - A)) =
        ∑ r ∈ Finset.Icc (a + 1) T, x r := by
    intro a _ haT
    dsimp only [x]
    rw [← Matrix.trace_sum, ← Finset.mul_sum, sum_Icc_sub_pred F haT]
  have htraceF : ∀ a : ℤ, jStar ≤ a → a ≤ T →
      Matrix.trace (A⁻¹ * F a) =
        2 * (d : ℝ) + ∑ r ∈ Finset.Icc (a + 1) T, x r := by
    intro a hja haT
    calc
      Matrix.trace (A⁻¹ * F a) =
          Matrix.trace (A⁻¹ * (A + (F a - A))) := by
        congr 2
        abel
      _ = Matrix.trace (A⁻¹ * A) +
          Matrix.trace (A⁻¹ * (F a - A)) := by
        rw [Matrix.mul_add, Matrix.trace_add]
      _ = 2 * (d : ℝ) + ∑ r ∈ Finset.Icc (a + 1) T, x r := by
        rw [htraceA, hgap a hja haT]
  have hfill := shifted_fill_rows hd hCd hg0 hg1 hE hEpd hstat hQ hw hY
    hmp hmv hl hjl hjT hcont
  change V ≤ F U + ∑ a ∈ Finset.Icc jStar (U - 1), c a • F a + s • A
    at hfill
  have htrace := PortableHistory.trace_mul_le_trace_mul hApos.inv.posSemidef hfill
  have htraceRhs :
      Matrix.trace
          (A⁻¹ * (F U + ∑ a ∈ Finset.Icc jStar (U - 1),
            c a • F a + s • A)) =
        (2 * (d : ℝ) + ∑ r ∈ Finset.Icc (U + 1) T, x r) +
          ∑ a ∈ Finset.Icc jStar (U - 1),
            c a * (2 * (d : ℝ) + ∑ r ∈ Finset.Icc (a + 1) T, x r) +
          s * (2 * (d : ℝ)) := by
    rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_add, Matrix.trace_add,
      Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, htraceA, htraceF U (by simpa only [U] using hjl) (by
        dsimp only [U]
        omega)]
    congr 2
    exact Finset.sum_congr rfl fun a ha => by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        htraceF a (Finset.mem_Icc.mp ha).1 (by
          have := (Finset.mem_Icc.mp ha).2
          dsimp only [U] at this
          omega)]
  have hpowCast : ∀ a : ℤ,
      (3 : ℝ) ^ (a - j) = (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) := by
    intro a
    simpa only [Int.cast_sub] using (Real.rpow_intCast (3 : ℝ) (a - j)).symm
  have hexp : ∀ a : ℤ,
      (a : ℝ) - (j : ℝ) = -(j : ℝ) + (a : ℝ) := by
    intro a
    ring
  calc
    Matrix.trace (A⁻¹ * (V - A)) =
        Matrix.trace (A⁻¹ * V) - 2 * (d : ℝ) := by
      rw [Matrix.mul_sub, Matrix.trace_sub, htraceA]
    _ ≤ Matrix.trace
          (A⁻¹ * (F U + ∑ a ∈ Finset.Icc jStar (U - 1),
            c a • F a + s • A)) - 2 * (d : ℝ) :=
      sub_le_sub_right htrace _
    _ = (∑ r ∈ Finset.Icc (U + 1) T, x r) +
        ∑ a ∈ Finset.Icc jStar (U - 1),
          c a * (2 * (d : ℝ) + ∑ r ∈ Finset.Icc (a + 1) T, x r) +
        s * (2 * (d : ℝ)) := by
      rw [htraceRhs]
      ring
    _ = _ := by
      dsimp only [qp, qv, U, A, F, V, x, c, s]
      rw [Finset.mul_sum]
      simp_rw [hpowCast]
      simp_rw [hexp]
      ring_nf

end

end Bridge
end HighContrast
end Homogenization
