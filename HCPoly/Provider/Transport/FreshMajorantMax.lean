/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FiniteFamilyMaxMoment
import HCPoly.Provider.Transport.HistoryDischarge
import HCPoly.Provider.Transport.WhitneySquareWeights
import HCPoly.Provider.Transport.CenteredUpper
import HCPoly.Provider.Transport.CenteredSplit

/-!
# The fresh filling rows of a finite target family

This file discharges the fresh part of the unshifted filling majorant.  The
geometric input is only the exact filling index and exact relative-volume
weight of each target cell.  Boundary rows use the printed square-weight
estimate, while the endpoint row is its unconditional bulk counterpart with
buffer zero.  The resulting scalar boundary kernel is then summed once over
the finite target family.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Pulling a deterministic nonnegative weight through the moment of a mixed
Schatten size. -/
private theorem lintegral_weighted_schattenSize_rpow_eq
    {P : Measure (CoeffSpace d)} {Q weight : ℝ} (hQ : 0 < Q)
    (hweight : 0 ≤ weight) {W : CoeffSpace d → BlockMat d}
    (hW : ∀ x, IsSymmetricBlockMat (W x)) (F : BlockMat d) :
    ∫⁻ x, ENNReal.ofReal (weight * schattenSize Q (W x) F) ^ Q ∂P =
      (ENNReal.ofReal weight * lqSchattenSize P Q W F) ^ Q := by
  calc
    ∫⁻ x, ENNReal.ofReal (weight * schattenSize Q (W x) F) ^ Q ∂P =
        ∫⁻ x, ENNReal.ofReal weight ^ Q *
          ENNReal.ofReal (schattenSize Q (W x) F) ^ Q ∂P := by
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_mul hweight,
        ENNReal.mul_rpow_of_nonneg _ _ hQ.le]
    _ = ENNReal.ofReal weight ^ Q *
        ∫⁻ x, ENNReal.ofReal (schattenSize Q (W x) F) ^ Q ∂P := by
      rw [lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg hQ.le ENNReal.ofReal_ne_top)]
    _ = ENNReal.ofReal weight ^ Q * lqSchattenSize P Q W F ^ Q := by
      rw [lqSchattenSize_rpow_eq hQ hW F]
    _ = (ENNReal.ofReal weight * lqSchattenSize P Q W F) ^ Q := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hQ.le]

/-- The exact number of targets at a level converts the terminal root weight
to the printed target-multiplicity coefficient. -/
private theorem fresh_target_multiplicity {ι : Type*} {Q rho K f : ℝ}
    {j n : ℤ} {Z : Finset ι} (hj : j ≤ n)
    (hZ : Z.card = 3 ^ (d * (n - j).toNat))
    (hK : 0 ≤ K) (hf : 0 ≤ f) :
    (Z.card : ℝ) *
        ((3 : ℝ) ^ (rho * ((j : ℝ) - (n : ℝ))) * (K * f)) ^ Q =
      K ^ Q *
        ((3 : ℝ) ^ (-(Q * rho - (d : ℝ)) *
          ((n : ℝ) - (j : ℝ))) * f ^ Q) := by
  have hnj : 0 ≤ n - j := sub_nonneg.mpr hj
  have hcardR : (Z.card : ℝ) =
      (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) - (j : ℝ))) := by
    rw [hZ]
    push_cast
    rw [← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_mul]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hnj
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hweight : 0 ≤ (3 : ℝ) ^ (rho * ((j : ℝ) - (n : ℝ))) :=
    Real.rpow_nonneg h3 _
  have hexp : (d : ℝ) * ((n : ℝ) - (j : ℝ)) +
        rho * ((j : ℝ) - (n : ℝ)) * Q =
      -(Q * rho - (d : ℝ)) * ((n : ℝ) - (j : ℝ)) := by
    ring
  have hweightQ :
      (((3 : ℝ) ^ (rho * ((j : ℝ) - (n : ℝ)))) ^ Q) =
        (3 : ℝ) ^ (rho * ((j : ℝ) - (n : ℝ)) * Q) :=
    (Real.rpow_mul h3 _ _).symm
  calc
    (Z.card : ℝ) *
          ((3 : ℝ) ^ (rho * ((j : ℝ) - (n : ℝ))) * (K * f)) ^ Q =
        (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) - (j : ℝ))) *
          (((3 : ℝ) ^ (rho * ((j : ℝ) - (n : ℝ)))) ^ Q *
            (K ^ Q * f ^ Q)) := by
      rw [hcardR, Real.mul_rpow hweight (mul_nonneg hK hf),
        Real.mul_rpow hK hf]
    _ = ((3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) - (j : ℝ))) *
          (3 : ℝ) ^ (rho * ((j : ℝ) - (n : ℝ)) * Q)) *
          (K ^ Q * f ^ Q) := by
      rw [hweightQ]
      ring
    _ = (3 : ℝ) ^ ((d : ℝ) * ((n : ℝ) - (j : ℝ)) +
          rho * ((j : ℝ) - (n : ℝ)) * Q) * (K ^ Q * f ^ Q) := by
      rw [Real.rpow_add h3pos]
    _ = K ^ Q *
        ((3 : ℝ) ^ (-(Q * rho - (d : ℝ)) *
          ((n : ℝ) - (j : ℝ))) * f ^ Q) := by
      rw [hexp]
      ring

/-! ## One target cell -/

/-- The fresh rows in the exact filling of one target cell, after exchanging
the old terminal normalization for the new one. -/
theorem fresh_filling_lqSchattenSize_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hPs : HCPoly.Frozen.IsStationaryLaw P)
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {Q : ℝ} (hQ : 2 ≤ Q)
    {jStar b j n t : ℤ} {q q' : Mat d}
    (hd : 1 ≤ d) (hq : IsRoundedGrid jStar q) (hq' : IsRoundedGrid jStar q')
    (hjb : jStar ≤ b) {Khop etaX : ℝ} (hK : gridRatio q q' ≤ Khop)
    (heta1 : etaX < 1)
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    (hEn : Book.Ch02.BlockPosDef (adaptedMean P q' n))
    (hlo : BlockMatLoewnerLE
      (blockScale (1 - etaX) (adaptedMean P q t)) (adaptedMean P q' n))
    {z : Fin d → ℤ} {Z : ℤ → Finset (Fin d → ℤ)} {c : ℤ → ℝ}
    (hZ : ∀ r ∈ Finset.Icc (b + 1) j,
      (↑(Z r) : Set (Fin d → ℤ)) =
        fillingIndex q j (adaptedCellAt q' j z) r)
    (hc : ∀ r ∈ Finset.Icc (b + 1) j, 0 ≤ c r)
    (hcratio : ∀ r ∈ Finset.Icc (b + 1) j, ∀ w ∈ Z r,
      (volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellAt q' j z)).toReal = c r)
    (hint : ∀ r ∈ Finset.Icc (b + 1) j, HasFiniteAdaptedMean P q r)
    (hEr : ∀ r ∈ Finset.Icc (b + 1) j,
      Book.Ch02.BlockPosDef (adaptedMean P q r))
    (hmean : ∀ r ∈ Finset.Icc (b + 1) j,
      BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q r))
    (hfin : ∀ r ∈ Finset.Icc (b + 1) j, centeredMoment P Q q r ≠ ⊤) :
    lqSchattenSize P Q (fun x => ofFullBlockMat
        (∑ r ∈ Finset.Icc (b + 1) j, ∑ w ∈ Z r,
          c r • toFullBlockMat
            (blockSub (coarseBlock (adaptedCellAt q r w) x)
              (adaptedMean P q r)))) (adaptedMean P q' n) ≤
      ENNReal.ofReal
        (((2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹) *
          (2 * (d : ℝ) *
            ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst *
                Real.sqrt Q) * Real.sqrt ((3 : ℝ) ^ d))) *
          Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
            (Real.sqrt d * Khop) ^ d) *
          (2 * (d : ℝ)) ^ Q⁻¹ *
          ∑ r ∈ Finset.Icc (b + 1) j,
            (3 : ℝ) ^ (-(((d : ℝ) + 1) / 2) *
                ((j : ℝ) - (r : ℝ))) *
              (Real.exp (detIncrement P q r t) *
                (centeredMoment P Q q r).toReal)) := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hq'PD : q'.PosDef := Recurrence.posDef_of_isRoundedGrid hq'
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_two hQ
  have hcell : adaptedCellAt q' j z =
      adaptedCellTranslate q' j (adaptedCellCenter q' j z) :=
    adaptedCellAt_eq_adaptedCellTranslate q' j z
  have hsqrt : ∀ r ∈ Finset.Icc (b + 1) j,
      Real.sqrt (∑ _w ∈ Z r, c r ^ 2) ≤
        Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
            (Real.sqrt d * Khop) ^ d) *
          (3 : ℝ) ^ (-(((d : ℝ) + 1) / 2) *
            ((j : ℝ) - (r : ℝ))) := by
    intro r hr
    have hsum : ∑ _w ∈ Z r, c r ^ 2 =
        ∑ w ∈ Z r, ((volume (adaptedCellAt q r w)).toReal /
          (volume (adaptedCellAt q' j z)).toReal) ^ 2 := by
      exact Finset.sum_congr rfl fun w hw => congrArg (fun x : ℝ => x ^ 2)
        (hcratio r hr w hw).symm
    rcases lt_or_eq_of_le (Finset.mem_Icc.mp hr).2 with hrj | rfl
    · have hZ' : (↑(Z r) : Set (Fin d → ℤ)) =
          fillingIndex q j
            (adaptedCellTranslate q' j (adaptedCellCenter q' j z)) r := by
        simpa only [hcell] using hZ r hr
      have hsq := boundary_square_weights hd hq'PD hqPD hrj hZ' hK
      rw [hsum, hcell]
      refine hsq.trans_eq ?_
      congr 2
      ring
    · have hZ' : (↑(Z r) : Set (Fin d → ℤ)) =
          fillingIndex q r
            (adaptedCellTranslate q' r (adaptedCellCenter q' r z)) (r - 0) := by
        simpa only [hcell, sub_zero] using hZ r hr
      have hsq := bulk_square_weights hd hq'PD hqPD hZ' hK
      rw [hsum, hcell]
      simpa only [sub_zero, Int.cast_zero, mul_zero, neg_zero, zero_div,
        Real.rpow_zero, mul_one, sub_self] using hsq
  have hfactor0 : 0 ≤ (2 * (d : ℝ)) ^ Q⁻¹ := Real.rpow_nonneg (by positivity) _
  have hrows :
      ∑ r ∈ Finset.Icc (b + 1) j,
          Real.sqrt (∑ _w ∈ Z r, c r ^ 2) *
              ((2 * (d : ℝ)) ^ Q⁻¹ * Real.exp (detIncrement P q r t)) *
            (centeredMoment P Q q r).toReal ≤
        Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
            (Real.sqrt d * Khop) ^ d) *
          (2 * (d : ℝ)) ^ Q⁻¹ *
          ∑ r ∈ Finset.Icc (b + 1) j,
            (3 : ℝ) ^ (-(((d : ℝ) + 1) / 2) *
                ((j : ℝ) - (r : ℝ))) *
              (Real.exp (detIncrement P q r t) *
                (centeredMoment P Q q r).toReal) := by
    calc
      ∑ r ∈ Finset.Icc (b + 1) j,
          Real.sqrt (∑ _w ∈ Z r, c r ^ 2) *
              ((2 * (d : ℝ)) ^ Q⁻¹ * Real.exp (detIncrement P q r t)) *
            (centeredMoment P Q q r).toReal ≤
        ∑ r ∈ Finset.Icc (b + 1) j,
          (Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
              (Real.sqrt d * Khop) ^ d) *
            (3 : ℝ) ^ (-(((d : ℝ) + 1) / 2) *
              ((j : ℝ) - (r : ℝ)))) *
              ((2 * (d : ℝ)) ^ Q⁻¹ * Real.exp (detIncrement P q r t)) *
            (centeredMoment P Q q r).toReal := by
          refine Finset.sum_le_sum fun r hr =>
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hsqrt r hr) ?_) ENNReal.toReal_nonneg
          exact mul_nonneg hfactor0 (Real.exp_nonneg _)
      _ = Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
            (Real.sqrt d * Khop) ^ d) *
          (2 * (d : ℝ)) ^ Q⁻¹ *
          ∑ r ∈ Finset.Icc (b + 1) j,
            (3 : ℝ) ^ (-(((d : ℝ) + 1) / 2) *
                ((j : ℝ) - (r : ℝ))) *
              (Real.exp (detIncrement P q r t) *
                (centeredMoment P Q q r).toReal) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
  have hl : ∀ r ∈ Finset.Icc (b + 1) j, jStar ≤ r := by
    intro r hr
    have hbr := (Finset.mem_Icc.mp hr).1
    omega
  have hold := centered_filling_rows_le_ofReal (Z := Z) (c := c)
    hPs hP hQ hq hc hl hint hEr hEt hmean hfin
  have hC0 : 0 ≤ 2 * (d : ℝ) *
      ((2 * Q + 4 * IndependentSums.rosenthalBennettIntegralConst *
        Real.sqrt Q) * Real.sqrt ((3 : ℝ) ^ d)) := by
    have hRB : 0 ≤ IndependentSums.rosenthalBennettIntegralConst := by
      simp only [IndependentSums.rosenthalBennettIntegralConst]
      positivity
    positivity
  have hold' := hold.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hrows hC0))
  have hsym : ∀ x : CoeffSpace d, IsSymmetricBlockMat (ofFullBlockMat
      (∑ r ∈ Finset.Icc (b + 1) j, ∑ w ∈ Z r,
        c r • toFullBlockMat
          (blockSub (coarseBlock (adaptedCellAt q r w) x)
            (adaptedMean P q r)))) := by
    intro x
    refine isSymmetricBlockMat_of_isSymm ?_
    ext gamma delta
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w _ =>
      congrArg _ ((isSymm_toFullBlockMat_of_isSymmetricBlockMat
        (Recurrence.isSymmetricBlockMat_coarseBlock_sub x
          (Recurrence.isSymmetricBlockMat_adaptedMean P q r))).apply gamma delta)
  have hbridge := lqSchattenSize_bridge_le heta1
    (Recurrence.isSymmetricBlockMat_adaptedMean P q t) hEt
    (Recurrence.isSymmetricBlockMat_adaptedMean P q' n) hEn hlo hsym hQ0
  have hbridgeC0 : 0 ≤ (2 * (d : ℝ)) ^ Q⁻¹ * (1 - etaX)⁻¹ := by
    have heta0 : 0 < 1 - etaX := by linarith only [heta1]
    exact mul_nonneg hfactor0 (inv_nonneg.mpr heta0.le)
  refine hbridge.trans (le_trans (mul_le_mul' le_rfl hold') ?_)
  rw [← ENNReal.ofReal_mul hbridgeC0]
  refine ENNReal.ofReal_le_ofReal ?_
  ring_nf
  exact le_rfl

/-! ## The finite target maximum -/

/-- The moment of the weighted finite maximum of all fresh filling rows is
bounded by the old-grid centered fresh-row profile.  The target family is the
exact sigma family used by `centeredHistory`; no target-count upper bound or
abstract row hypothesis is assumed. -/
theorem fresh_majorant_max_moment_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hPs : HCPoly.Frozen.IsStationaryLaw P)
    (hP : HCPoly.Frozen.IsUnitRangeLaw P)
    {Q : ℕ} (hQ : 2 ≤ Q) (hQeven : Even Q)
    {g rhoMax a : ℝ} (hg : 0 ≤ g)
    (hadef : a = (Q : ℝ) * (rhoMax - g) - (d : ℝ))
    (hkernel : 0 < ((d : ℝ) + 1) / 2 - a / (Q : ℝ))
    {jStar b n t : ℤ} {l0 : ℕ} (ht : t = n + (l0 : ℤ))
    {q q' : Mat d} (hd : 1 ≤ d)
    (hq : IsRoundedGrid jStar q) (hq' : IsRoundedGrid jStar q')
    (hjb : jStar ≤ b) {Khop etaX : ℝ} (hK : gridRatio q q' ≤ Khop)
    (heta1 : etaX < 1)
    (hEt : Book.Ch02.BlockPosDef (adaptedMean P q t))
    (hEn : Book.Ch02.BlockPosDef (adaptedMean P q' n))
    (hlo : BlockMatLoewnerLE
      (blockScale (1 - etaX) (adaptedMean P q t)) (adaptedMean P q' n))
    {Ztarget : ℤ → Finset (Fin d → ℤ)}
    (hs : ((Finset.Icc jStar n).sigma Ztarget :
      Finset (Sigma fun _ : ℤ => (Fin d → ℤ))).Nonempty)
    (hcard : ∀ j ∈ Finset.Icc jStar n,
      (Ztarget j).card = 3 ^ (d * (n - j).toNat))
    {Zfill : (Sigma fun _ : ℤ => (Fin d → ℤ)) →
      ℤ → Finset (Fin d → ℤ)}
    {c : (Sigma fun _ : ℤ => (Fin d → ℤ)) → ℤ → ℝ}
    (hZfill : ∀ i ∈ ((Finset.Icc jStar n).sigma Ztarget :
        Finset (Sigma fun _ : ℤ => (Fin d → ℤ))),
      ∀ r ∈ Finset.Icc (b + 1) i.1,
        (↑(Zfill i r) : Set (Fin d → ℤ)) =
          fillingIndex q i.1 (adaptedCellAt q' i.1 i.2) r)
    (hc : ∀ i ∈ ((Finset.Icc jStar n).sigma Ztarget :
        Finset (Sigma fun _ : ℤ => (Fin d → ℤ))),
      ∀ r ∈ Finset.Icc (b + 1) i.1, 0 ≤ c i r)
    (hcratio : ∀ i ∈ ((Finset.Icc jStar n).sigma Ztarget :
        Finset (Sigma fun _ : ℤ => (Fin d → ℤ))),
      ∀ r ∈ Finset.Icc (b + 1) i.1, ∀ w ∈ Zfill i r,
        (volume (adaptedCellAt q r w)).toReal /
            (volume (adaptedCellAt q' i.1 i.2)).toReal = c i r)
    (hint : ∀ r ∈ Finset.Icc (b + 1) t, HasFiniteAdaptedMean P q r)
    (hEr : ∀ r ∈ Finset.Icc (b + 1) t,
      Book.Ch02.BlockPosDef (adaptedMean P q r))
    (hmean : ∀ r ∈ Finset.Icc (b + 1) t,
      BlockMatLoewnerLE (adaptedMean P q t) (adaptedMean P q r))
    (hfin : ∀ r ∈ Finset.Icc (b + 1) t,
      centeredMoment P (Q : ℝ) q r ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal
        (((Finset.Icc jStar n).sigma Ztarget).sup' hs fun i =>
          (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize (Q : ℝ) (ofFullBlockMat
              (∑ r ∈ Finset.Icc (b + 1) i.1, ∑ w ∈ Zfill i r,
                c i r • toFullBlockMat
                  (blockSub (coarseBlock (adaptedCellAt q r w) x)
                    (adaptedMean P q r)))) (adaptedMean P q' n)) ^ (Q : ℝ) ∂P ≤
      ENNReal.ofReal
        (((((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * (1 - etaX)⁻¹) *
            (2 * (d : ℝ) *
              ((2 * (Q : ℝ) +
                4 * IndependentSums.rosenthalBennettIntegralConst *
                  Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d))) *
            Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
              (Real.sqrt d * Khop) ^ d) *
            (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) ^ (Q : ℝ)) *
          (3 : ℝ) ^ (a * (l0 : ℝ)) *
          (1 / (1 - (3 : ℝ) ^
            (-(((d : ℝ) + 1) / 2 - a / (Q : ℝ))))) ^ (Q : ℝ) *
          ∑ r ∈ Finset.Icc (b + 1) t,
            (3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
              Real.exp ((Q : ℝ) * detIncrement P q r t) *
                (centeredMoment P (Q : ℝ) q r).toReal ^ (Q : ℝ)) := by
  classical
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := lt_of_lt_of_le zero_lt_two hQR
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := le_trans (by norm_num) hQR
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := hQ0.le
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hl0nn : (0 : ℤ) ≤ (l0 : ℤ) := Int.natCast_nonneg l0
  have hnt : n ≤ t := by omega
  have htR : (t : ℝ) = (n : ℝ) + (l0 : ℝ) := by
    rw [ht]
    push_cast
    rfl
  let W : (Sigma fun _ : ℤ => (Fin d → ℤ)) → CoeffSpace d → BlockMat d :=
    fun i x => ofFullBlockMat
      (∑ r ∈ Finset.Icc (b + 1) i.1, ∑ w ∈ Zfill i r,
        c i r • toFullBlockMat
          (blockSub (coarseBlock (adaptedCellAt q r w) x)
            (adaptedMean P q r)))
  let row : ℤ → ℝ := fun j =>
    ∑ r ∈ Finset.Icc (b + 1) j,
      (3 : ℝ) ^ (-(((d : ℝ) + 1) / 2) * ((j : ℝ) - (r : ℝ))) *
        (Real.exp (detIncrement P q r t) *
          (centeredMoment P (Q : ℝ) q r).toReal)
  let Kcell : ℝ :=
    ((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * (1 - etaX)⁻¹) *
      (2 * (d : ℝ) *
        ((2 * (Q : ℝ) +
          4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d))) *
      Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
        (Real.sqrt d * Khop) ^ d) *
      (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹
  have hrow0 : ∀ j, 0 ≤ row j := by
    intro j
    simp only [row]
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg)
  have hRB : 0 ≤ IndependentSums.rosenthalBennettIntegralConst := by
    simp only [IndependentSums.rosenthalBennettIntegralConst]
    positivity
  have heta0 : 0 < 1 - etaX := by linarith only [heta1]
  have hKcell0 : 0 ≤ Kcell := by
    simp only [Kcell]
    positivity
  have hsym : ∀ i, ∀ x, IsSymmetricBlockMat (W i x) := by
    intro i x
    simp only [W]
    refine isSymmetricBlockMat_of_isSymm ?_
    ext gamma delta
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w _ =>
      congrArg _ ((isSymm_toFullBlockMat_of_isSymmetricBlockMat
        (Recurrence.isSymmetricBlockMat_coarseBlock_sub x
          (Recurrence.isSymmetricBlockMat_adaptedMean P q r))).apply gamma delta)
  have hentry : ∀ i, ∀ alpha beta : BlockCoord d,
      AEStronglyMeasurable (fun x => toFullBlockMat (W i x) alpha beta) P := by
    intro i alpha beta
    simp only [W, toFullBlockMat_ofFullBlockMat, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine Finset.aestronglyMeasurable_fun_sum _ fun r _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun w _ => ?_
    have hm := Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hqPD r w alpha beta
    have hm' : AEStronglyMeasurable
        (fun x => toFullBlockMat (coarseBlock (adaptedCellAt q r w) x) alpha beta) P := by
      simpa only [toFullBlockMat_eq_blockMatEntry] using hm
    have hsub : AEStronglyMeasurable
        (fun x => toFullBlockMat
          (blockSub (coarseBlock (adaptedCellAt q r w) x)
            (adaptedMean P q r)) alpha beta) P := by
      simpa only [Recurrence.toFullBlockMat_blockSub_apply] using
        hm'.sub (aestronglyMeasurable_const
          (b := toFullBlockMat (adaptedMean P q r) alpha beta))
    exact hsub.const_mul (c i r)
  have hmax := lintegral_finset_sup'_rpow_le_sum P
    ((Finset.Icc jStar n).sigma Ztarget) hs
    (Q := (Q : ℝ))
    (fun i x => (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
      schattenSize (Q : ℝ) (W i x) (adaptedMean P q' n)) (by
      intro i hi
      have hm := aestronglyMeasurable_schattenSize
        (F := adaptedMean P q' n) hQeven (hsym i) (hentry i)
      have hmweighted : AEStronglyMeasurable (fun x =>
          (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize (Q : ℝ) (W i x) (adaptedMean P q' n)) P :=
        hm.const_mul ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))))
      have hmof : AEMeasurable (fun x => ENNReal.ofReal
          ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize (Q : ℝ) (W i x) (adaptedMean P q' n))) P :=
        ENNReal.measurable_ofReal.comp_aemeasurable hmweighted.aemeasurable
      have hmpow : AEMeasurable (fun x => ENNReal.ofReal
          ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize (Q : ℝ) (W i x) (adaptedMean P q' n)) ^ (Q : ℝ)) P :=
        ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmof
      exact hmpow)
  have hcellMoment : ∀ i ∈ ((Finset.Icc jStar n).sigma Ztarget :
      Finset (Sigma fun _ : ℤ => (Fin d → ℤ))),
      ∫⁻ x, ENNReal.ofReal
          ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize (Q : ℝ) (W i x) (adaptedMean P q' n)) ^ (Q : ℝ) ∂P ≤
        ENNReal.ofReal
          (((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            (Kcell * row i.1)) ^ (Q : ℝ)) := by
    intro i hi
    have hij := Finset.mem_sigma.mp hi
    have hjn : i.1 ≤ n := (Finset.mem_Icc.mp hij.1).2
    have hsub : Finset.Icc (b + 1) i.1 ⊆ Finset.Icc (b + 1) t := by
      intro r hr
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
        (Finset.mem_Icc.mp hr).2.trans (hjn.trans hnt)⟩
    have hcellNorm := fresh_filling_lqSchattenSize_le hPs hP hQR hd hq hq' hjb
      hK heta1 hEt hEn hlo (z := i.2) (Z := Zfill i) (c := c i)
      (hZfill i hi) (hc i hi) (hcratio i hi)
      (fun r hr => hint r (hsub hr))
      (fun r hr => hEr r (hsub hr))
      (fun r hr => hmean r (hsub hr))
      (fun r hr => hfin r (hsub hr))
    have hcellNorm' : lqSchattenSize P (Q : ℝ) (W i) (adaptedMean P q' n) ≤
        ENNReal.ofReal (Kcell * row i.1) := by
      simpa only [W, Kcell, row] using hcellNorm
    have hweight0 : 0 ≤
        (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    calc
      ∫⁻ x, ENNReal.ofReal
          ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize (Q : ℝ) (W i x) (adaptedMean P q' n)) ^ (Q : ℝ) ∂P =
          (ENNReal.ofReal
              ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ)))) *
            lqSchattenSize P (Q : ℝ) (W i) (adaptedMean P q' n)) ^ (Q : ℝ) :=
        lintegral_weighted_schattenSize_rpow_eq hQ0 hweight0 (hsym i)
          (adaptedMean P q' n)
      _ ≤ (ENNReal.ofReal
              ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ)))) *
            ENNReal.ofReal (Kcell * row i.1)) ^ (Q : ℝ) :=
        ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hcellNorm') hQnn
      _ = ENNReal.ofReal
          (((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            (Kcell * row i.1)) ^ (Q : ℝ)) := by
        rw [← ENNReal.ofReal_mul hweight0,
          ENNReal.ofReal_rpow_of_nonneg
            (mul_nonneg hweight0 (mul_nonneg hKcell0 (hrow0 i.1))) hQnn]
  have hsumReal :
      ∑ i ∈ ((Finset.Icc jStar n).sigma Ztarget :
          Finset (Sigma fun _ : ℤ => (Fin d → ℤ))),
        (((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
          (Kcell * row i.1)) ^ (Q : ℝ)) =
        Kcell ^ (Q : ℝ) *
          ∑ j ∈ Finset.Icc jStar n,
            (3 : ℝ) ^ (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                ((n : ℝ) - (j : ℝ))) * row j ^ (Q : ℝ) := by
    rw [Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    change (∑ _s ∈ Ztarget j,
      ((3 : ℝ) ^ (rhoMax * ((j : ℝ) - (n : ℝ))) *
        (Kcell * row j)) ^ (Q : ℝ)) = _
    rw [Finset.sum_const, nsmul_eq_mul]
    exact fresh_target_multiplicity (d := d) (Q := (Q : ℝ))
      (rho := rhoMax) (K := Kcell) (f := row j)
      (Finset.mem_Icc.mp hj).2 (hcard j hj) hKcell0 (hrow0 j)
  have hv : ∀ j ∈ Finset.Icc jStar n,
      Finset.Icc (b + 1) j ⊆ Finset.Icc (b + 1) t := by
    intro j hj r hr
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      (Finset.mem_Icc.mp hr).2.trans ((Finset.mem_Icc.mp hj).2.trans hnt)⟩
  have hlevel := fresh_centered_boundary_le (P := P) (q := q)
    (Q := (Q : ℝ)) (g := g) (rhoMax := rhoMax) (a := a)
    hQ1 hg hadef hkernel (l0 := (l0 : ℤ)) (n := n) (t := t) htR
    (s := Finset.Icc jStar n) (T := Finset.Icc (b + 1) t)
    (v := fun j => Finset.Icc (b + 1) j) hv
    (fun j _ r hr => (Finset.mem_Icc.mp hr).2)
    (fun j hj => (Finset.mem_Icc.mp hj).2)
    (vr := fun r => (centeredMoment P (Q : ℝ) q r).toReal)
    (f := row) (fun _ => ENNReal.toReal_nonneg) (fun j _ => hrow0 j)
    (fun _ _ => le_rfl)
  have hlevel' := mul_le_mul_of_nonneg_left hlevel
    (Real.rpow_nonneg hKcell0 (Q : ℝ))
  calc
    ∫⁻ x, ENNReal.ofReal
        (((Finset.Icc jStar n).sigma Ztarget).sup' hs fun i =>
          (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize (Q : ℝ) (ofFullBlockMat
              (∑ r ∈ Finset.Icc (b + 1) i.1, ∑ w ∈ Zfill i r,
                c i r • toFullBlockMat
                  (blockSub (coarseBlock (adaptedCellAt q r w) x)
                    (adaptedMean P q r)))) (adaptedMean P q' n)) ^ (Q : ℝ) ∂P ≤
        ∑ i ∈ ((Finset.Icc jStar n).sigma Ztarget :
            Finset (Sigma fun _ : ℤ => (Fin d → ℤ))),
          ∫⁻ x, ENNReal.ofReal
            ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
              schattenSize (Q : ℝ) (W i x)
                (adaptedMean P q' n)) ^ (Q : ℝ) ∂P := by
      simpa only [W] using hmax
    _ ≤ ∑ i ∈ ((Finset.Icc jStar n).sigma Ztarget :
          Finset (Sigma fun _ : ℤ => (Fin d → ℤ))),
        ENNReal.ofReal
          (((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            (Kcell * row i.1)) ^ (Q : ℝ)) :=
      Finset.sum_le_sum hcellMoment
    _ = ENNReal.ofReal
        (∑ i ∈ ((Finset.Icc jStar n).sigma Ztarget :
            Finset (Sigma fun _ : ℤ => (Fin d → ℤ))),
          (((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            (Kcell * row i.1)) ^ (Q : ℝ))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact Real.rpow_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (mul_nonneg hKcell0 (hrow0 i.1))) _
    _ = ENNReal.ofReal
        (Kcell ^ (Q : ℝ) *
          ∑ j ∈ Finset.Icc jStar n,
            (3 : ℝ) ^ (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                ((n : ℝ) - (j : ℝ))) * row j ^ (Q : ℝ)) := by
      rw [hsumReal]
    _ ≤ ENNReal.ofReal
        (Kcell ^ (Q : ℝ) *
          ((3 : ℝ) ^ (a * (l0 : ℝ)) *
            (1 / (1 - (3 : ℝ) ^
              (-(((d : ℝ) + 1) / 2 - a / (Q : ℝ))))) ^ (Q : ℝ) *
            ∑ r ∈ Finset.Icc (b + 1) t,
              (3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
                Real.exp ((Q : ℝ) * detIncrement P q r t) *
                  (centeredMoment P (Q : ℝ) q r).toReal ^ (Q : ℝ))) :=
      ENNReal.ofReal_le_ofReal hlevel'
    _ = ENNReal.ofReal
        (((((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * (1 - etaX)⁻¹) *
            (2 * (d : ℝ) *
              ((2 * (Q : ℝ) +
                4 * IndependentSums.rosenthalBennettIntegralConst *
                  Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d))) *
            Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
              (Real.sqrt d * Khop) ^ d) *
            (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) ^ (Q : ℝ)) *
          (3 : ℝ) ^ (a * (l0 : ℝ)) *
          (1 / (1 - (3 : ℝ) ^
            (-(((d : ℝ) + 1) / 2 - a / (Q : ℝ))))) ^ (Q : ℝ) *
          ∑ r ∈ Finset.Icc (b + 1) t,
            (3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
              Real.exp ((Q : ℝ) * detIncrement P q r t) *
                (centeredMoment P (Q : ℝ) q r).toReal ^ (Q : ℝ)) := by
      refine congrArg ENNReal.ofReal ?_
      simp only [Kcell]
      ring

end

end Transport
end HighContrast
end Homogenization
