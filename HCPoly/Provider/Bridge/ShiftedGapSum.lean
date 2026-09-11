/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Bridge.ShiftedAuxSums
import HCPoly.Provider.Bridge.ShiftedFiniteSums
import HCPoly.Provider.Bridge.ShiftedTraceRows
import HCPoly.Provider.Bridge.SourceCoefficients
import HCPoly.Provider.ShortHop.SourceCoefficient

/-!
# Summed shifted terminal gaps

The early whole-cell rows and the continued filling rows are summed in the
fixed old-grid terminal geometry.  Principal, boundary, and source terms are
kept separate through the finite interchanges.
-/

namespace Homogenization
namespace HighContrast
namespace Bridge

open MeasureTheory

open scoped MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d}
  {Ψ : ℝ → ℝ} {K Cd Q : ℝ} {jStar M : ℤ}
  {Y : CoeffSpace d → ℝ}

/-- An early new-grid mean has a terminal trace gap bounded by its ordered
whole-cell coefficient. -/
theorem early_shifted_trace_le [NeZero d] [IsProbabilityMeasure P]
    (hCd : 1 ≤ Cd) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {j T : ℤ} (hjj : jStar ≤ j) (hjT : j ≤ T)
    (hcontv : adaptedCell (roundedGrid jStar mv) j ⊆ centeredCube d M)
    (hcontp : adaptedCell (roundedGrid jStar mp) T ⊆ centeredCube d M) :
    Matrix.trace
        ((toFullBlockMat (adaptedMean P (roundedGrid jStar mp) T))⁻¹ *
          (toFullBlockMat (adaptedMean P (roundedGrid jStar mv) j) -
            toFullBlockMat (adaptedMean P (roundedGrid jStar mp) T))) ≤
      2 * (d : ℝ) * bridgeEarlyCoeff Cd g E mv mp := by
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  let A : FullBlockMat d := toFullBlockMat (adaptedMean P qp T)
  let V : FullBlockMat d := toFullBlockMat (adaptedMean P qv j)
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hqv := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmv
  have hjStarT : jStar ≤ T := hjj.trans hjT
  have hApos : A.PosDef := by
    dsimp only [A]
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hqp T
      (Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hmp hqp hjStarT hcontp)
  have hAunit : IsUnit A.det := isUnit_det_of_posDef hApos
  have htraceA : Matrix.trace (A⁻¹ * A) = 2 * (d : ℝ) := by
    rw [Matrix.nonsing_inv_mul _ hAunit, Matrix.trace_one]
    simp [Fintype.card_sum, two_mul]
  have hmean := early_adaptedMean_le_terminal hCd hg1 hE hEpd hQ hw hY
    hmv hmp hqv hqp hjj hjStarT hcontv hcontp
  change V ≤ bridgeEarlyCoeff Cd g E mv mp • A at hmean
  have htrace := PortableHistory.trace_mul_le_trace_mul hApos.inv.posSemidef hmean
  have htrace' : Matrix.trace (A⁻¹ * V) ≤
      bridgeEarlyCoeff Cd g E mv mp * (2 * (d : ℝ)) := by
    simpa only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, htraceA] using htrace
  calc
    Matrix.trace (A⁻¹ * (V - A)) = Matrix.trace (A⁻¹ * V) - 2 * (d : ℝ) := by
      rw [Matrix.mul_sub, Matrix.trace_sub, htraceA]
    _ ≤ Matrix.trace (A⁻¹ * V) := by
      exact sub_le_self _ (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    _ ≤ 2 * (d : ℝ) * bridgeEarlyCoeff Cd g E mv mp :=
      htrace'.trans_eq (by ring)

/-- The complete old-terminal trace-gap sum has exactly the three structural
rows needed by the shifted drift: separation mass, old drift, and source. -/
theorem weighted_old_terminal_gaps_le [NeZero d] [IsProbabilityMeasure P]
    (hd : 2 ≤ d) (hCd : 1 ≤ Cd) (hg0 : 0 ≤ g) (hg1 : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mp mv : Mat d} (hmp : mp.PosDef) (hmv : mv.PosDef)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) (hrhog : rho ≤ 1 - g)
    {n l : ℤ} (hl : 1 ≤ l) (hjn : jStar ≤ n - l)
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
      ∀ a : ℤ, jStar ≤ a → a ≤ n + l →
        adaptedCell r a ⊆ centeredCube d M) :
    ∑ j ∈ Finset.Ico jStar n,
        (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ))) *
          Matrix.trace
            ((toFullBlockMat
              (adaptedMean P (roundedGrid jStar mp) (n + l)))⁻¹ *
              (toFullBlockMat (adaptedMean P (roundedGrid jStar mv) j) -
                toFullBlockMat
                  (adaptedMean P (roundedGrid jStar mp) (n + l)))) ≤
      ((6 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)) *
          (1 / (1 - (3 : ℝ) ^ (-rho))) *
          (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))))) *
        gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
          (3 : ℝ) ^ (-(l : ℝ)) +
      ((1 / (1 - (3 : ℝ) ^ (-rho))) +
          (6 * (d : ℝ) * Real.sqrt d) *
            (1 / (1 - (3 : ℝ) ^ (-rho))) *
            (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
        (1 + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)) *
          (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
            linearDrift P rho (roundedGrid jStar mp) jStar (n + l) +
      (2 * (d : ℝ) +
          (18 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ))) *
        bridgeSrcCoeff Cd g E jStar mp mv *
          (3 : ℝ) ^ (rho * (l : ℝ)) *
          (1 + ((n : ℝ) - (jStar : ℝ))) *
            (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ))) := by
  classical
  let qp := roundedGrid jStar mp
  let qv := roundedGrid jStar mv
  let T : ℤ := n + l
  let Kpv : ℝ := gridRatio qp qv
  let A : FullBlockMat d := toFullBlockMat (adaptedMean P qp T)
  let F : ℤ → FullBlockMat d := fun a => toFullBlockMat (adaptedMean P qp a)
  let V : ℤ → FullBlockMat d := fun a => toFullBlockMat (adaptedMean P qv a)
  let x : ℤ → ℝ := fun r => Matrix.trace (A⁻¹ * (F (r - 1) - F r))
  let w : ℤ → ℝ := fun j => (3 : ℝ) ^ (-rho * ((n : ℝ) - 1 - (j : ℝ)))
  let gap : ℤ → ℝ := fun j => Matrix.trace (A⁻¹ * (V j - A))
  let mass : ℤ → ℝ := fun j => ∑ a ∈ Finset.Icc jStar (j - l - 1),
    (3 : ℝ) ^ ((a : ℝ) - (j : ℝ))
  let binc : ℤ → ℝ := fun j => ∑ a ∈ Finset.Icc jStar (j - l - 1),
    (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) * ∑ r ∈ Finset.Icc (a + 1) T, x r
  have hjn0 : jStar ≤ n := by omega
  have hbln : jStar + l ≤ n := by omega
  have hjT : n ≤ T := by dsimp only [T]; omega
  have hqp := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmp
  have hqv := Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmv
  have hdef := Transport.definedness_of_isWindowMultiplier hd hstat hE hQ hw hY
    hmp hmv (b := T) (by simpa only [T] using hcont)
  have hApos : A.PosDef := by
    dsimp only [A]
    exact Recurrence.posDef_toFullBlockMat_adaptedMean hqp T
      ((hdef.1 qp (Or.inl rfl) T (by dsimp only [T]; omega) le_rfl).1)
  have hx : ∀ r ∈ Finset.Icc (jStar + 1) T, 0 ≤ x r := by
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    have hmono := Recurrence.toFullBlockMat_adaptedMean_le hstat hqp (by omega) (by omega)
      ((hdef.1 qp (Or.inl rfl) (r - 1) (by omega) (by omega)).1)
      ((hdef.1 qp (Or.inl rfl) r (by omega) hrange.2).1)
    dsimp only [x]
    exact PortableHistory.trace_mul_nonneg hApos.inv.posSemidef (Matrix.le_iff.mp hmono)
  have hdrift : ∑ r ∈ Finset.Icc (jStar + 1) T,
      (3 : ℝ) ^ (-rho * ((T : ℝ) - (r : ℝ))) * x r =
        linearDrift P rho qp jStar T := by
    simp only [linearDrift, x, F, A, blockTrace, toFullBlockMat_ofFullBlockMat,
      Recurrence.toFullBlockMat_blockSub]
  have hearly0 := ShortHop.zero_le_bridgeEarlyCoeff (le_trans zero_le_one hCd) hg1 E mv mp
  have hcont0 := ShortHop.zero_le_bridgeContCoeff (le_trans zero_le_one hCd) hg1 E
    jStar mp mv mp
  have hsrc0 : 0 ≤ bridgeSrcCoeff Cd g E jStar mp mv :=
    le_trans zero_le_one
      (ShortHop.one_le_bridgeSrcCoeff (le_trans zero_le_one hCd) hg1 E jStar mp mv)
  have hordered := (ordered_coefficients_le_bridgeSrcCoeff Cd g E jStar mp mv).1
  have hearlySrc : bridgeEarlyCoeff Cd g E mv mp ≤ bridgeSrcCoeff Cd g E jStar mp mv :=
    (le_add_of_nonneg_left hcont0).trans hordered
  have hcontSrc : bridgeContCoeff Cd g E jStar mp mv mp ≤
      bridgeSrcCoeff Cd g E jStar mp mv :=
    (le_add_of_nonneg_right hearly0).trans hordered
  have hearly : ∑ j ∈ Finset.Ico jStar (jStar + l), w j * gap j ≤
      (2 * (d : ℝ) * bridgeSrcCoeff Cd g E jStar mp mv) *
        ((1 + ((n : ℝ) - (jStar : ℝ))) *
          (3 : ℝ) ^ (rho * (l : ℝ)) *
            (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ)))) := by
    have hpoint : ∀ j ∈ Finset.Ico jStar (jStar + l),
        gap j ≤ 2 * (d : ℝ) * bridgeEarlyCoeff Cd g E mv mp := by
      intro j hj
      exact early_shifted_trace_le hCd hg1 hE hEpd hQ hw hY hmp hmv
        (Finset.mem_Ico.mp hj).1 (by have := (Finset.mem_Ico.mp hj).2; omega)
        (hcont qv (Or.inr rfl) j (Finset.mem_Ico.mp hj).1 (by
          have := (Finset.mem_Ico.mp hj).2
          omega)) (hcont qp (Or.inl rfl) T (by dsimp only [T]; omega) le_rfl)
    have hsum : ∑ j ∈ Finset.Ico jStar (jStar + l), w j * gap j ≤
        ∑ j ∈ Finset.Ico jStar (jStar + l),
          w j * (2 * (d : ℝ) * bridgeEarlyCoeff Cd g E mv mp) :=
      Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hpoint j hj) (by
          dsimp only [w]
          exact Real.rpow_nonneg (by norm_num) _)
    rw [← Finset.sum_mul] at hsum
    have hweights := shifted_early_weight_sum_le hrho (by omega : 0 ≤ l) hbln
    have hcoef0 : 0 ≤ 2 * (d : ℝ) * bridgeEarlyCoeff Cd g E mv mp := by positivity
    have hmul := mul_le_mul_of_nonneg_left hweights hcoef0
    have hnj0 : 0 ≤ (n : ℝ) - (jStar : ℝ) := by
      apply sub_nonneg.mpr
      exact_mod_cast hjn0
    have hfront0 : 0 ≤ 1 + ((n : ℝ) - (jStar : ℝ)) := by
      linarith only [hnj0]
    have hpowL0 : 0 ≤ (3 : ℝ) ^ (rho * (l : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hpowN0 : 0 ≤ (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hreplace := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hearlySrc (by positivity : (0 : ℝ) ≤ 2 * d))
      (mul_nonneg (mul_nonneg hfront0 hpowL0) hpowN0)
    calc
      _ ≤ (∑ j ∈ Finset.Ico jStar (jStar + l), w j) *
          (2 * (d : ℝ) * bridgeEarlyCoeff Cd g E mv mp) := hsum
      _ = (2 * (d : ℝ) * bridgeEarlyCoeff Cd g E mv mp) *
          ∑ j ∈ Finset.Ico jStar (jStar + l), w j := by ring
      _ ≤ (2 * (d : ℝ) * bridgeEarlyCoeff Cd g E mv mp) *
          ((1 + ((n : ℝ) - (jStar : ℝ))) *
            (3 : ℝ) ^ (rho * (l : ℝ)) *
              (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ)))) := hmul
      _ ≤ _ := by simpa only [mul_assoc] using hreplace
  have hcontinuedPoint : ∀ j ∈ Finset.Ico (jStar + l) n,
      gap j ≤
        (∑ r ∈ Finset.Icc (j - l + 1) T, x r) +
        (6 * (d : ℝ) * Real.sqrt d) * Kpv * (2 * (d : ℝ)) * mass j +
        (6 * (d : ℝ) * Real.sqrt d) * Kpv * binc j +
        (18 * (d : ℝ) * Real.sqrt d) *
          bridgeContCoeff Cd g E jStar mp mv mp *
            (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) *
              (2 * (d : ℝ)) := by
    intro j hj
    have htrace := shifted_fill_trace_le hd hCd hg0 hg1 hE hEpd hstat hQ hw hY
      hmp hmv (j := j) (l := l) (T := T) (by omega : 0 ≤ l)
      (by have := (Finset.mem_Ico.mp hj).1; omega)
      (by have := (Finset.mem_Ico.mp hj).2; omega)
      (by simpa only [T] using hcont)
    dsimp only [gap, x, mass, binc, A, F, V, qp, qv, T, Kpv] at htrace ⊢
    have hsplitMass :
        6 * (d : ℝ) * Real.sqrt d *
            gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
            ∑ a ∈ Finset.Icc jStar (j - l - 1),
              (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) *
                (2 * (d : ℝ) +
                  ∑ r ∈ Finset.Icc (a + 1) (n + l),
                    Matrix.trace
                      ((toFullBlockMat
                        (adaptedMean P (roundedGrid jStar mp) (n + l)))⁻¹ *
                        (toFullBlockMat
                            (adaptedMean P (roundedGrid jStar mp) (r - 1)) -
                          toFullBlockMat
                            (adaptedMean P (roundedGrid jStar mp) r)))) =
          6 * (d : ℝ) * Real.sqrt d *
              gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
              (2 * (d : ℝ)) *
                ∑ a ∈ Finset.Icc jStar (j - l - 1),
                  (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) +
            6 * (d : ℝ) * Real.sqrt d *
              gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
                ∑ a ∈ Finset.Icc jStar (j - l - 1),
                  (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) *
                    ∑ r ∈ Finset.Icc (a + 1) (n + l),
                      Matrix.trace
                        ((toFullBlockMat
                          (adaptedMean P (roundedGrid jStar mp) (n + l)))⁻¹ *
                          (toFullBlockMat
                              (adaptedMean P (roundedGrid jStar mp) (r - 1)) -
                            toFullBlockMat
                              (adaptedMean P (roundedGrid jStar mp) r))) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    exact htrace.trans_eq (by rw [hsplitMass]; ring)
  have hcontinued : ∑ j ∈ Finset.Ico (jStar + l) n, w j * gap j ≤
      ((6 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ)) *
          (1 / (1 - (3 : ℝ) ^ (-rho))) *
          (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))))) * Kpv *
            (3 : ℝ) ^ (-(l : ℝ)) +
      ((1 / (1 - (3 : ℝ) ^ (-rho))) +
          (6 * (d : ℝ) * Real.sqrt d) *
            (1 / (1 - (3 : ℝ) ^ (-rho))) *
            (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
        (1 + Kpv) * (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
          linearDrift P rho qp jStar T +
      ((18 * (d : ℝ) * Real.sqrt d) * (2 * (d : ℝ))) *
        bridgeSrcCoeff Cd g E jStar mp mv *
          ((1 + ((n : ℝ) - (jStar : ℝ))) *
            (3 : ℝ) ^ (rho * (l : ℝ)) *
              (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ)))) := by
    have hsum : ∑ j ∈ Finset.Ico (jStar + l) n, w j * gap j ≤
        ∑ j ∈ Finset.Ico (jStar + l) n, w j *
          ((∑ r ∈ Finset.Icc (j - l + 1) T, x r) +
            (6 * (d : ℝ) * Real.sqrt d) * Kpv * (2 * (d : ℝ)) * mass j +
            (6 * (d : ℝ) * Real.sqrt d) * Kpv * binc j +
            (18 * (d : ℝ) * Real.sqrt d) *
              bridgeContCoeff Cd g E jStar mp mv mp *
                (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) *
                  (2 * (d : ℝ))) :=
      Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hcontinuedPoint j hj) (by
          dsimp only [w]
          exact Real.rpow_nonneg (by norm_num) _)
    have hmassSum := shifted_boundary_mass_sum_le hrho (b := jStar) (n := n) (l := l)
    have hmain := shifted_main_sum_le hrho x hx (b := jStar) (n := n) (l := l)
    have hbincPad : ∑ j ∈ Finset.Ico (jStar + l) n, w j * binc j ≤
        ∑ j ∈ Finset.Ico (jStar + l) n, w j *
          ∑ a ∈ Finset.Icc jStar (j - l),
            (3 : ℝ) ^ ((a : ℝ) - (j : ℝ)) *
              ∑ r ∈ Finset.Icc (a + 1) T, x r := by
      refine Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
      dsimp only [binc]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        rw [Finset.mem_Icc] at ha ⊢
        exact ⟨ha.1, by omega⟩
      · intro a ha _
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Finset.sum_nonneg fun r hr => hx r (by
            rw [Finset.mem_Icc] at hr ⊢
            have haj := (Finset.mem_Icc.mp ha).1
            exact ⟨by omega, hr.2⟩))
    have hbinc := hbincPad.trans
      (shifted_boundary_sum_le hrho hrho1 (by omega : 0 ≤ l) x hx)
    have hsource := shifted_continued_source_sum_le hrho hrhog hl hbln
      (a := 1 - g) (b := jStar) (n := n)
    have hK0 : 0 ≤ Kpv := le_trans zero_le_one (Transport.one_le_gridRatio qp qv)
    have hD0 : 0 ≤ linearDrift P rho qp jStar T := by
      rw [← hdrift]
      exact Finset.sum_nonneg fun r hr => mul_nonneg
        (Real.rpow_nonneg (by norm_num) _) (hx r hr)
    have hnj0 : 0 ≤ (n : ℝ) - (jStar : ℝ) := by
      apply sub_nonneg.mpr
      exact_mod_cast hjn0
    have hfront0 : 0 ≤ 1 + ((n : ℝ) - (jStar : ℝ)) := by
      linarith only [hnj0]
    have hpowL0 : 0 ≤ (3 : ℝ) ^ (rho * (l : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have hpowN0 : 0 ≤ (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hsource0 : 0 ≤ (1 + ((n : ℝ) - (jStar : ℝ))) *
        (3 : ℝ) ^ (rho * (l : ℝ)) *
          (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ))) :=
      mul_nonneg (mul_nonneg hfront0 hpowL0) hpowN0
    have hsrcReplace := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcontSrc
        (by positivity : 0 ≤ (18 * (d : ℝ) * Real.sqrt d) * (2 * d))) hsource0
    -- Expand the four continued rows, then apply their scalar sum bounds.
    calc
      _ ≤ ∑ j ∈ Finset.Ico (jStar + l) n, w j *
          ((∑ r ∈ Finset.Icc (j - l + 1) T, x r) +
            (6 * (d : ℝ) * Real.sqrt d) * Kpv * (2 * d) * mass j +
            (6 * (d : ℝ) * Real.sqrt d) * Kpv * binc j +
            (18 * (d : ℝ) * Real.sqrt d) *
              bridgeContCoeff Cd g E jStar mp mv mp *
                (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) *
                  (2 * d)) := hsum
      _ = (∑ j ∈ Finset.Ico (jStar + l) n, w j *
            ∑ r ∈ Finset.Icc (j - l + 1) T, x r) +
          ((6 * (d : ℝ) * Real.sqrt d) * Kpv * (2 * d)) *
            ∑ j ∈ Finset.Ico (jStar + l) n, w j * mass j +
          ((6 * (d : ℝ) * Real.sqrt d) * Kpv) *
            ∑ j ∈ Finset.Ico (jStar + l) n, w j * binc j +
          ((18 * (d : ℝ) * Real.sqrt d) *
            bridgeContCoeff Cd g E jStar mp mv mp * (2 * d)) *
              ∑ j ∈ Finset.Ico (jStar + l) n, w j *
                (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ (1 / (1 - (3 : ℝ) ^ (-rho))) *
            (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
              linearDrift P rho qp jStar T +
          ((6 * (d : ℝ) * Real.sqrt d) * Kpv * (2 * d)) *
            ((1 / (1 - (3 : ℝ) ^ (-rho))) *
              (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
                (3 : ℝ) ^ (-(l : ℝ))) +
          ((6 * (d : ℝ) * Real.sqrt d) * Kpv) *
            ((1 / (1 - (3 : ℝ) ^ (-rho)) *
                (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
              (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
                linearDrift P rho qp jStar T) +
          ((18 * (d : ℝ) * Real.sqrt d) *
            bridgeContCoeff Cd g E jStar mp mv mp * (2 * d)) *
              ((1 + ((n : ℝ) - (jStar : ℝ))) *
                (3 : ℝ) ^ (rho * (l : ℝ)) *
                  (3 : ℝ) ^ (-rho * ((n : ℝ) - (jStar : ℝ)))) := by
        have hbinc' := hbinc
        rw [hdrift] at hbinc'
        have hmassCoef : 0 ≤
            (6 * (d : ℝ) * Real.sqrt d) * Kpv * (2 * d) := by positivity
        have hbincCoef : 0 ≤
            (6 * (d : ℝ) * Real.sqrt d) * Kpv := by positivity
        have hsourceCoef : 0 ≤
            (18 * (d : ℝ) * Real.sqrt d) *
              bridgeContCoeff Cd g E jStar mp mv mp * (2 * d) := by positivity
        exact add_le_add (add_le_add (add_le_add
          (by simpa only [w, T, hdrift] using hmain)
          (mul_le_mul_of_nonneg_left hmassSum hmassCoef))
          (mul_le_mul_of_nonneg_left hbinc' hbincCoef))
          (mul_le_mul_of_nonneg_left hsource hsourceCoef)
      _ ≤ _ := by
        have hG0 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-rho)) :=
          div_nonneg zero_le_one (sub_nonneg.mpr (PortableHistory.geom_ratio_lt_one hrho).le)
        have hG10 : 0 ≤ 1 / (1 - (3 : ℝ) ^ (-(1 - rho))) := by
          exact div_nonneg zero_le_one (sub_nonneg.mpr (PortableHistory.geom_ratio_lt_one
            (by linarith only [hrho1])).le)
        have hshift0 : 0 ≤ (3 : ℝ) ^ (2 * rho * (l : ℝ)) := by positivity
        have hmainAbs :
            (1 / (1 - (3 : ℝ) ^ (-rho))) *
                (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
                  linearDrift P rho qp jStar T +
              ((6 * (d : ℝ) * Real.sqrt d) * Kpv) *
                ((1 / (1 - (3 : ℝ) ^ (-rho)) *
                  (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
                    (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
                      linearDrift P rho qp jStar T) ≤
            ((1 / (1 - (3 : ℝ) ^ (-rho))) +
                (6 * (d : ℝ) * Real.sqrt d) *
                  (1 / (1 - (3 : ℝ) ^ (-rho))) *
                  (1 / (1 - (3 : ℝ) ^ (-(1 - rho))))) *
              (1 + Kpv) * (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
                linearDrift P rho qp jStar T := by
          have h1K : 1 ≤ 1 + Kpv := by linarith only [hK0]
          have hKK : Kpv ≤ 1 + Kpv := by linarith only [hK0]
          have hbase0 : 0 ≤ (3 : ℝ) ^ (2 * rho * (l : ℝ)) *
              linearDrift P rho qp jStar T := mul_nonneg hshift0 hD0
          have hfirst := mul_le_mul_of_nonneg_left h1K hG0
          have hsecond := mul_le_mul_of_nonneg_left hKK
            (mul_nonneg (by positivity : 0 ≤ 6 * (d : ℝ) * Real.sqrt d)
              (mul_nonneg hG0 hG10))
          nlinarith only [mul_le_mul_of_nonneg_right hfirst hbase0,
            mul_le_mul_of_nonneg_right hsecond hbase0]
        have hmassEq :
            ((6 * (d : ℝ) * Real.sqrt d) * Kpv * (2 * d)) *
              ((1 / (1 - (3 : ℝ) ^ (-rho))) *
                (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ)))) *
                  (3 : ℝ) ^ (-(l : ℝ))) =
            ((6 * (d : ℝ) * Real.sqrt d) * (2 * d) *
              (1 / (1 - (3 : ℝ) ^ (-rho))) *
              (1 / (1 - (3 : ℝ) ^ (-(1 : ℝ))))) * Kpv *
                (3 : ℝ) ^ (-(l : ℝ)) := by ring
        rw [hmassEq]
        linarith only [hmainAbs, hsrcReplace]
  have hsplit : ∑ j ∈ Finset.Ico jStar n, w j * gap j =
      (∑ j ∈ Finset.Ico jStar (jStar + l), w j * gap j) +
        ∑ j ∈ Finset.Ico (jStar + l) n, w j * gap j := by
    rw [← Finset.Ico_union_Ico_eq_Ico (by omega : jStar ≤ jStar + l) hbln,
      Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive
        jStar (jStar + l) n)]
  rw [hsplit]
  have h := add_le_add hearly hcontinued
  dsimp only [qp, qv, T, Kpv, A, F, V, w, gap] at h ⊢
  nlinarith only [h]

end

end Bridge
end HighContrast
end Homogenization
