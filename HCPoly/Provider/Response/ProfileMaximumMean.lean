/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileRecentPointwise
import HCPoly.Provider.Bridge.ComparisonMatrixRows
import HCPoly.Provider.ShortHop.DriftAccount

/-!
# The annealed part of the terminal maximum

The positive excess of a response block above the terminal mean is bounded by
the centered difference and the positive annealed mean increment.  The latter
telescopes into the fixed-grid drift with its terminal normalization.
-/

namespace Homogenization.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The positive excess above a reference is no larger than the spectral size
of the corresponding difference. -/
theorem blockExcess_le_blockSize_blockSub [NeZero d] {A E : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hApsd : (toFullBlockMat A).PosSemidef)
    (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E) :
    blockExcess A E ≤ blockSize (blockSub A E) E := by
  have hAE : IsSymmetricBlockMat (blockSub A E) :=
    isSymmetricBlockMat_blockSub hA hE
  have hnorm :
      relSize (toFullBlockMat A) (toFullBlockMat E) - 1 ≤
        ‖toFullBlockMat (normalizedBlock (blockSub A E) E)‖ := by
    rw [relSize_def, Recurrence.toFullBlockMat_normalizedBlock_blockSub,
      matSqrt_inv_conj (posDef_toFullBlockMat hE hEpd)]
    simpa using norm_sub_norm_le
      (matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat A *
        matSqrt (toFullBlockMat E)⁻¹) (1 : FullBlockMat d)
  rw [blockExcess_eq hA hE hEpd hApsd,
    PortableHistory.blockSize_eq_norm hAE hE hEpd]
  exact max_le hnorm (norm_nonneg _)

/-- A positive annealed increment is bounded by its trace in the terminal
geometry. -/
theorem blockSize_mean_sub_le_trace {P : Measure (CoeffSpace d)}
    {q : Mat d} {k t : ℤ}
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmean : BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q k)) :
    blockSize (blockSub (adaptedMean P q k) (adaptedMean P q t))
        (adaptedMean P q t) ≤
      Matrix.trace
        ((toFullBlockMat (adaptedMean P q t))⁻¹ *
          toFullBlockMat
            (blockSub (adaptedMean P q k) (adaptedMean P q t))) := by
  let Ek := adaptedMean P q k
  let Et := adaptedMean P q t
  have hEks : IsSymmetricBlockMat Ek :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q k
  have hEts : IsSymmetricBlockMat Et :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hEtfull : (toFullBlockMat Et).PosDef :=
    posDef_toFullBlockMat hEts hEt
  have hflat : toFullBlockMat Et ≤ toFullBlockMat Ek :=
    (blockMatLoewnerLE_iff_le hEts hEks).mp hmean
  have hG :
      (toFullBlockMat (blockSub Ek Et)).PosSemidef := by
    rw [Recurrence.toFullBlockMat_blockSub]
    exact Matrix.le_iff.mp hflat
  have htrace0 :
      0 ≤ Matrix.trace
        ((toFullBlockMat Et)⁻¹ * toFullBlockMat (blockSub Ek Et)) :=
    PortableHistory.trace_mul_nonneg hEtfull.inv.posSemidef hG
  have hupper :
      toFullBlockMat (blockSub Ek Et) ≤
        Matrix.trace
          ((toFullBlockMat Et)⁻¹ * toFullBlockMat (blockSub Ek Et)) •
            toFullBlockMat Et :=
    Bridge.posSemidef_le_trace_inv_smul hEtfull hG
  exact Transport.blockSize_le_of_blockMatLoewnerLE_blockScale
    (isSymmetricBlockMat_blockSub hEks hEts) hG hEts hEt htrace0
      (blockMatLoewnerLE_of_le (by
        rw [toFullBlockMat_blockScale]
        exact hupper))

/-- A backward difference telescopes over an integer interval. -/
private theorem sum_Icc_sub_pred {M : Type*} [AddCommGroup M] (f : ℤ → M)
    {u v : ℤ} (huv : u ≤ v) :
    ∑ r ∈ Finset.Icc (u + 1) v, (f (r - 1) - f r) = f u - f v := by
  induction v, huv using Int.leInduction with
  | base =>
    have hempty : Finset.Icc (u + 1) u = (∅ : Finset ℤ) := by
      ext x
      simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and, not_le]
      omega
    rw [hempty, Finset.sum_empty, sub_self]
  | succ v huv ih =>
    have hins : Finset.Icc (u + 1) (v + 1) =
        insert (v + 1) (Finset.Icc (u + 1) v) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : (v + 1) ∉ Finset.Icc (u + 1) v := by
      simp only [Finset.mem_Icc, not_and, not_le]
      omega
    rw [hins, Finset.sum_insert hnot, ih, add_sub_cancel_right]
    abel

/-- The terminal trace of the total mean increment is the unweighted sum of
the terminal traces of its one-scale increments. -/
theorem trace_mean_sub_eq_sum {P : Measure (CoeffSpace d)} {q : Mat d}
    {k t : ℤ} (hkt : k ≤ t) :
    Matrix.trace
        ((toFullBlockMat (adaptedMean P q t))⁻¹ *
          toFullBlockMat
            (blockSub (adaptedMean P q k) (adaptedMean P q t))) =
      ∑ r ∈ Finset.Icc (k + 1) t,
        blockTrace
          (ofFullBlockMat
            ((toFullBlockMat (adaptedMean P q t))⁻¹ *
              toFullBlockMat
                (blockSub (adaptedMean P q (r - 1))
                  (adaptedMean P q r)))) := by
  simp only [blockTrace, toFullBlockMat_ofFullBlockMat]
  rw [← Matrix.trace_sum, ← Finset.mul_sum,
    show ∑ r ∈ Finset.Icc (k + 1) t,
        toFullBlockMat
          (blockSub (adaptedMean P q (r - 1)) (adaptedMean P q r)) =
        toFullBlockMat
          (blockSub (adaptedMean P q k) (adaptedMean P q t)) by
      simp only [Recurrence.toFullBlockMat_blockSub]
      exact sum_Icc_sub_pred (fun r => toFullBlockMat (adaptedMean P q r)) hkt]

/-- The weighted annealed mean increment at any retained scale is bounded by
the terminal fixed-grid drift. -/
theorem weighted_mean_sub_le_linearDrift {P : Measure (CoeffSpace d)}
    {rhoDr rhoWn : ℝ} (hrhoDr : 0 ≤ rhoDr) (hrhos : rhoDr ≤ rhoWn)
    {q : Mat d} {jStar k t : ℤ} (hjk : jStar ≤ k) (hkt : k ≤ t)
    (hEt : BlockPosDef (adaptedMean P q t))
    (hmono : ∀ r : ℤ, jStar + 1 ≤ r → r ≤ t →
      BlockMatLoewnerLE (adaptedMean P q r) (adaptedMean P q (r - 1))) :
    (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) *
        blockSize (blockSub (adaptedMean P q k) (adaptedMean P q t))
          (adaptedMean P q t) ≤
      linearDrift P rhoDr q jStar t := by
  let trTerm : ℤ → ℝ := fun r =>
    blockTrace
      (ofFullBlockMat
        ((toFullBlockMat (adaptedMean P q t))⁻¹ *
          toFullBlockMat
            (blockSub (adaptedMean P q (r - 1)) (adaptedMean P q r))))
  have htrace0 : ∀ r ∈ Finset.Icc (jStar + 1) t, 0 ≤ trTerm r := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hG :
        (toFullBlockMat
          (blockSub (adaptedMean P q (r - 1))
            (adaptedMean P q r))).PosSemidef := by
      rw [Recurrence.toFullBlockMat_blockSub]
      have hrs := hmono r hr.1 hr.2
      exact Matrix.le_iff.mp
        ((blockMatLoewnerLE_iff_le
          (Recurrence.isSymmetricBlockMat_adaptedMean P q r)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q (r - 1))).mp hrs)
    dsimp only [trTerm, blockTrace]
    rw [toFullBlockMat_ofFullBlockMat]
    exact PortableHistory.trace_mul_nonneg
      (posDef_toFullBlockMat
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt).inv.posSemidef hG
  have hmean : BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q k) := by
    refine blockMatLoewnerLE_of_le (Matrix.le_iff.mpr ?_)
    rw [← sum_Icc_sub_pred
      (fun r => toFullBlockMat (adaptedMean P q r)) hkt]
    exact Matrix.posSemidef_sum (Finset.Icc (k + 1) t) fun r hr => by
      rw [Finset.mem_Icc] at hr
      exact Matrix.le_iff.mp
        ((blockMatLoewnerLE_iff_le
          (Recurrence.isSymmetricBlockMat_adaptedMean P q r)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q (r - 1))).mp
            (hmono r (by omega) hr.2))
  have hsize := blockSize_mean_sub_le_trace hEt hmean
  have hweight0 : 0 ≤
      (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsize' := mul_le_mul_of_nonneg_left hsize hweight0
  rw [trace_mean_sub_eq_sum hkt] at hsize'
  have hsub : Finset.Icc (k + 1) t ⊆ Finset.Icc (jStar + 1) t := by
    intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  have hterm : ∀ r ∈ Finset.Icc (k + 1) t,
      (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) * trTerm r ≤
        (3 : ℝ) ^ (-rhoDr * ((t : ℝ) - (r : ℝ))) * trTerm r := by
    intro r hr
    have hrI := Finset.mem_Icc.mp hr
    have hgap : (0 : ℝ) ≤ (t : ℝ) - (r : ℝ) := by
      exact_mod_cast sub_nonneg.mpr hrI.2
    have hrk : (k : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (by omega : k ≤ r)
    have hprod :
        rhoDr * ((t : ℝ) - (r : ℝ)) ≤
          rhoWn * ((t : ℝ) - (k : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_right hrhos hgap
      have hdist : (t : ℝ) - (r : ℝ) ≤ (t : ℝ) - (k : ℝ) := by
        linarith only [hrk]
      have h2 := mul_le_mul_of_nonneg_left hdist (le_trans hrhoDr hrhos)
      linarith only [h1, h2]
    have hexp :
        -rhoWn * ((t : ℝ) - (k : ℝ)) ≤
          -rhoDr * ((t : ℝ) - (r : ℝ)) := by
      linarith only [hprod]
    have hw :
        (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) ≤
          (3 : ℝ) ^ (-rhoDr * ((t : ℝ) - (r : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    exact mul_le_mul_of_nonneg_right hw (htrace0 r (hsub hr))
  have hsum :
      ∑ r ∈ Finset.Icc (k + 1) t,
          (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) * trTerm r ≤
        ∑ r ∈ Finset.Icc (jStar + 1) t,
          (3 : ℝ) ^ (-rhoDr * ((t : ℝ) - (r : ℝ))) * trTerm r := by
    calc
      ∑ r ∈ Finset.Icc (k + 1) t,
          (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) * trTerm r ≤
          ∑ r ∈ Finset.Icc (k + 1) t,
            (3 : ℝ) ^ (-rhoDr * ((t : ℝ) - (r : ℝ))) * trTerm r :=
        Finset.sum_le_sum hterm
      _ ≤ ∑ r ∈ Finset.Icc (jStar + 1) t,
          (3 : ℝ) ^ (-rhoDr * ((t : ℝ) - (r : ℝ))) * trTerm r := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
        intro r hrBig hrSmall
        exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (htrace0 r hrBig)
  calc
    (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) *
          blockSize (blockSub (adaptedMean P q k) (adaptedMean P q t))
            (adaptedMean P q t)
        ≤ (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) *
            ∑ r ∈ Finset.Icc (k + 1) t, trTerm r := hsize'
    _ = ∑ r ∈ Finset.Icc (k + 1) t,
          (3 : ℝ) ^ (-rhoWn * ((t : ℝ) - (k : ℝ))) * trTerm r := by
      rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ Finset.Icc (jStar + 1) t,
          (3 : ℝ) ^ (-rhoDr * ((t : ℝ) - (r : ℝ))) * trTerm r := hsum
    _ = linearDrift P rhoDr q jStar t := rfl

end

end Homogenization.HighContrast.Response
