/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FreshMajorantMax
import HCPoly.Provider.Transport.CenteredBound

/-!
# The fresh target maximum against the portable profile

The finite fresh-row maximum is placed directly in the centered-moment row of
the old-grid portable profile.  The bridge coefficient is made uniform by the
transport range `etaX <= 1 / 4`.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The fresh part of the finite target majorants, with its old-grid row sum
absorbed by the portable profile and its bridge inverse bounded by `4 / 3`. -/
theorem fresh_majorant_max_moment_le_portableProfile [NeZero d]
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
    (heta4 : etaX ≤ 1 / 4)
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
          ((((((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * (4 / 3 : ℝ)) *
              (2 * (d : ℝ) *
                ((2 * (Q : ℝ) +
                  4 * IndependentSums.rosenthalBennettIntegralConst *
                    Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d))) *
              Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
                (Real.sqrt d * Khop) ^ d) *
              (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) ^ (Q : ℝ)) *
            (1 / (1 - (3 : ℝ) ^
              (-(((d : ℝ) + 1) / 2 - a / (Q : ℝ))))) ^ (Q : ℝ)) *
          (3 : ℝ) ^ (a * (l0 : ℝ))) *
        portableProfile P (Q : ℝ) a rhoMax q jStar b t := by
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := le_trans zero_le_two hQR
  have heta1 : etaX < 1 := by linarith only [heta4]
  have hden : 0 < 1 - etaX := sub_pos.mpr heta1
  have hinv : (1 - etaX)⁻¹ ≤ (4 / 3 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith only [heta4]
  have hKhop0 : 0 ≤ Khop :=
    le_trans (le_trans zero_le_one (one_le_gridRatio q q')) hK
  have hRB : 0 ≤ IndependentSums.rosenthalBennettIntegralConst := by
    simp only [IndependentSums.rosenthalBennettIntegralConst]
    positivity
  let L : ℝ := (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹
  let R : ℝ := 2 * (d : ℝ) *
    ((2 * (Q : ℝ) +
      4 * IndependentSums.rosenthalBennettIntegralConst * Real.sqrt (Q : ℝ)) *
        Real.sqrt ((3 : ℝ) ^ d))
  let S : ℝ := Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
    (Real.sqrt d * Khop) ^ d)
  let Keta : ℝ := L * (1 - etaX)⁻¹ * R * S * L
  let Kbar : ℝ := L * (4 / 3 : ℝ) * R * S * L
  let J : ℝ := 1 / (1 - (3 : ℝ) ^
    (-(((d : ℝ) + 1) / 2 - a / (Q : ℝ))))
  let rows : ℝ := ∑ r ∈ Finset.Icc (b + 1) t,
    (3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
      Real.exp ((Q : ℝ) * detIncrement P q r t) *
        (centeredMoment P (Q : ℝ) q r).toReal ^ (Q : ℝ)
  have hL0 : 0 ≤ L := Real.rpow_nonneg (by positivity) _
  have hR0 : 0 ≤ R := by
    simp only [R]
    positivity
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hKeta0 : 0 ≤ Keta := by
    simp only [Keta]
    positivity
  have hKbar0 : 0 ≤ Kbar := by
    simp only [Kbar]
    positivity
  have hKle : Keta ≤ Kbar := by
    simp only [Keta, Kbar]
    gcongr
  have hJ0 : 0 ≤ J := by
    have hpow : (3 : ℝ) ^
        (-(((d : ℝ) + 1) / 2 - a / (Q : ℝ))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hkernel])
    simp only [J]
    exact one_div_nonneg.mpr (sub_nonneg.mpr hpow.le)
  have hrows0 : 0 ≤ rows := by
    simp only [rows]
    exact Finset.sum_nonneg fun r _ =>
      mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _))
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hrowsProfile : ENNReal.ofReal rows ≤
      portableProfile P (Q : ℝ) a rhoMax q jStar b t := by
    have hrowsEq : ENNReal.ofReal rows =
        ∑ r ∈ Finset.Icc (b + 1) t,
          ENNReal.ofReal
              ((3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
                Real.exp ((Q : ℝ) * detIncrement P q r t)) *
            centeredMoment P (Q : ℝ) q r ^ (Q : ℝ) := by
      simp only [rows]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl fun r hr => ?_
        have hcoef0 : 0 ≤
            (3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
              Real.exp ((Q : ℝ) * detIncrement P q r t) :=
          mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _)
        rw [ENNReal.ofReal_mul hcoef0,
          ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hQ0,
          ENNReal.ofReal_toReal (hfin r hr)]
      · intro r _
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _))
          (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    rw [hrowsEq]
    calc
      (∑ r ∈ Finset.Icc (b + 1) t,
          ENNReal.ofReal
              ((3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
                Real.exp ((Q : ℝ) * detIncrement P q r t)) *
            centeredMoment P (Q : ℝ) q r ^ (Q : ℝ)) ≤
          ENNReal.ofReal
              ((3 : ℝ) ^ (-a * ((t : ℝ) - (b : ℝ))) *
                (1 + frakH (Q : ℝ) (relMean P q b t))) *
              centeredHistory P (Q : ℝ) rhoMax q jStar b +
            ∑ r ∈ Finset.Icc (b + 1) t,
              ENNReal.ofReal
                  ((3 : ℝ) ^ (-a * ((t : ℝ) - (r : ℝ))) *
                    Real.exp ((Q : ℝ) * detIncrement P q r t)) *
                centeredMoment P (Q : ℝ) q r ^ (Q : ℝ) := le_add_left le_rfl
      _ ≤ portableProfile P (Q : ℝ) a rhoMax q jStar b t :=
        upper_centered_le_profile P (Q : ℝ) a rhoMax q jStar b t
  have hraw := fresh_majorant_max_moment_le hPs hP hQ hQeven hg hadef hkernel
    ht hd hq hq' hjb hK heta1 hEt hEn hlo hs hcard hZfill hc hcratio
    hint hEr hmean hfin
  have hcoef : Keta ^ (Q : ℝ) * (3 : ℝ) ^ (a * (l0 : ℝ)) * J ^ (Q : ℝ) ≤
      (Kbar ^ (Q : ℝ) * J ^ (Q : ℝ)) *
        (3 : ℝ) ^ (a * (l0 : ℝ)) := by
    have hKpow := Real.rpow_le_rpow hKeta0 hKle hQ0
    calc
      Keta ^ (Q : ℝ) * (3 : ℝ) ^ (a * (l0 : ℝ)) * J ^ (Q : ℝ) =
          (Keta ^ (Q : ℝ) * J ^ (Q : ℝ)) *
            (3 : ℝ) ^ (a * (l0 : ℝ)) := by ring
      _ ≤ (Kbar ^ (Q : ℝ) * J ^ (Q : ℝ)) *
            (3 : ℝ) ^ (a * (l0 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKpow (Real.rpow_nonneg hJ0 _))
          (Real.rpow_nonneg (by norm_num) _)
  have hfactor0 : 0 ≤ Keta ^ (Q : ℝ) *
      (3 : ℝ) ^ (a * (l0 : ℝ)) * J ^ (Q : ℝ) := by positivity
  refine hraw.trans ?_
  change ENNReal.ofReal
      ((Keta ^ (Q : ℝ) * (3 : ℝ) ^ (a * (l0 : ℝ)) * J ^ (Q : ℝ)) * rows) ≤ _
  rw [ENNReal.ofReal_mul hfactor0]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) hrowsProfile).trans_eq ?_
  congr 2

end

end Transport
end HighContrast
end Homogenization
