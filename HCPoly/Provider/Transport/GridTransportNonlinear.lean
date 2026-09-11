/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.NonlinearLevelFamilies
import HCPoly.Provider.Transport.RowDischarge
import HCPoly.Provider.Transport.SourceConvolution
import HCPoly.Provider.Transport.TransportConclusion

/-!
# The nonlinear half of grid transport

This file closes the nonlinear-history half of the random-source grid transport
directly from the proposition's binders.  Its constants are selected before the
buffer, source constant, law, reference block, and grid witnesses.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder

noncomputable section

/-- The nonlinear history on the transported grid is bounded uniformly by the
incoming portable profile, the bridge error, and the transported source
remainder.  The source coefficient pays the filling-row inflation only once,
through its `Q`-th power in the final source majorant. -/
theorem exists_grid_transport_nonlinear_bound
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Q : ℕ) (hQ : 2 ≤ Q) (rhoMax a : ℝ)
    (hadef : a = (Q : ℝ) * (rhoMax - g) - (d : ℝ))
    (halo : 0 < a) (hahi : a < 1 - g) (Khop : ℝ) (hKhop : 1 ≤ Khop) :
    ∃ Cnl CnlS : ℝ, 0 ≤ Cnl ∧ 0 ≤ CnlS ∧
      ∀ l0 : ℕ, 1 ≤ l0 →
      ∀ Cd : ℝ, 1 ≤ Cd →
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ, IsCoupledWindow d Q K jStar M →
        ∀ Y : CoeffSpace d → ℝ, IsWindowMultiplier P g E Ψ K Cd jStar M Y →
        ∀ mu mu' : Mat d, mu.PosDef → mu'.PosDef →
        gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop →
        ∀ rchk u : ℤ, jStar ≤ rchk → rchk ≤ u →
        (∀ r : Mat d, r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
          ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
            adaptedCell r j ⊆ centeredCube d M) →
        ∀ etaX : ℝ, 0 ≤ etaX → etaX ≤ 1 / 4 →
        BlockMatLoewnerLE
          (blockScale (1 - etaX)
            (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ))))
          (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))) →
        BlockMatLoewnerLE
          (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))
          (blockScale (1 + etaX)
            (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ)))) →
        nonlinearHistory P (Q : ℝ) a (roundedGrid jStar mu') jStar
            (u + (l0 : ℤ)) ≤
          ENNReal.ofReal (Cnl * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
              portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu)
                jStar rchk (u + 2 * (l0 : ℤ)) +
            ENNReal.ofReal (Cnl * etaX) +
            ENNReal.ofReal
              (CnlS * (3 : ℝ) ^ (a * (l0 : ℝ)) *
                transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                  (u + (l0 : ℤ))) := by
  haveI : NeZero d := ⟨by omega⟩
  have hd1 : 1 ≤ d := le_trans (by omega) hd
  have hdR0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hQR0 : (0 : ℝ) ≤ (Q : ℝ) := le_trans zero_le_one hQ1
  have hQR : (0 : ℝ) < (Q : ℝ) := lt_of_lt_of_le zero_lt_one hQ1
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hadm : a ≤ (Q : ℝ) * rhoMax - (d : ℝ) := by
    have hQg : (0 : ℝ) ≤ (Q : ℝ) * g := mul_nonneg hQR0 hg0
    rw [hadef]
    linarith only [hQg]
  set A : ℝ := 2 ^ (2 * (Q : ℝ) + 1) * (1 + 2 * (d : ℝ)) ^ (Q : ℝ) with hA
  set Cnl : ℝ := max 0
    ((2 * A +
        (A * (6 * (d : ℝ) * Real.sqrt d * Khop)) *
          ((3 : ℝ) ^ (-(1 - g - a)) /
            (1 - (3 : ℝ) ^ (-(1 - g - a)))) +
        4 * A + A) /
      (1 - (3 : ℝ) ^ (-a))) with hCnl
  set Csrc : ℝ := max 0
    ((3 : ℝ) ^ a *
      (1 / (1 - (3 : ℝ) ^ (-a)) +
        1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
        1 / (1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a))))) with hCsrc
  set Lam : ℝ := 18 * (d : ℝ) * Real.sqrt d * Khop with hLam
  set CnlS : ℝ := Cnl * Csrc * Lam ^ (Q : ℝ) with hCnlS
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by linarith only [hdR0]) _)
  have hCnl0 : 0 ≤ Cnl := by rw [hCnl]; exact le_max_left _ _
  have hCsrc0 : 0 ≤ Csrc := by rw [hCsrc]; exact le_max_left _ _
  have hCnlAdeq :
      (2 * A +
          (A * (6 * (d : ℝ) * Real.sqrt d * Khop)) *
            ((3 : ℝ) ^ (-(1 - g - a)) /
              (1 - (3 : ℝ) ^ (-(1 - g - a)))) +
          4 * A + A) /
        (1 - (3 : ℝ) ^ (-a)) ≤ Cnl := by
    rw [hCnl]
    exact le_max_right _ _
  have hCsrcAdeq :
      (3 : ℝ) ^ a *
          (1 / (1 - (3 : ℝ) ^ (-a)) +
            1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
            1 / (1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a)))) ≤ Csrc := by
    rw [hCsrc]
    exact le_max_right _ _
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hdR1
  have hLam1 : 1 ≤ Lam := by
    rw [hLam]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hdR1) hsqrt1)
      hKhop
  have hLam0 : 0 ≤ Lam := le_trans zero_le_one hLam1
  have hCnlS0 : 0 ≤ CnlS := by
    rw [hCnlS]
    exact mul_nonneg (mul_nonneg hCnl0 hCsrc0)
      (Real.rpow_nonneg hLam0 (Q : ℝ))
  refine ⟨Cnl, CnlS, hCnl0, hCnlS0, ?_⟩
  intro l0 hl0 Cd hCd P E Ψ K S hPprob hPstat hced jStar M hw Y hY mu mu'
    hmu hmu' hKgrid rchk u hjr hru hcont etaX heta0 heta4 hlo hhi
  letI : IsProbabilityMeasure P := hPprob
  have hl0z : (1 : ℤ) ≤ (l0 : ℤ) := by exact_mod_cast hl0
  have hl0z0 : (0 : ℤ) ≤ (l0 : ℤ) := le_trans (by omega) hl0z
  have hCd0 : (0 : ℝ) ≤ Cd := le_trans zero_le_one hCd
  have hCdpos : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hjn : jStar ≤ u + (l0 : ℤ) := by omega
  have hjt : jStar ≤ u + 2 * (l0 : ℤ) := by omega
  have hnt : u + (l0 : ℤ) ≤ u + 2 * (l0 : ℤ) := by omega
  have hq := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  have hq' := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu'
  have hq'pd : (roundedGrid jStar mu').PosDef := Recurrence.posDef_of_isRoundedGrid hq'
  obtain ⟨hdef, _, hbridge⟩ :=
    transport_definedness_and_bridge d hd g Q hQ l0 Cd P E Ψ K S hPprob hPstat
      hced jStar M hw Y hY mu mu' hmu hmu' rchk u hjr hru hcont
  obtain ⟨_, _, _, hgram, _, _⟩ := hbridge etaX heta0 heta4 hlo hhi
  have hHpd : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ))) :=
    (hdef _ (Or.inl rfl) _ hjt le_rfl).2.1
  have hFpd : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))) :=
    (hdef _ (Or.inr rfl) _ hjn hnt).2.1
  have hFfull :
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu')
        (u + (l0 : ℤ)))).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _) hFpd
  have hS :
      (bridgeMap (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ)))
          (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))))ᵀ *
          bridgeMap (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ)))
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))) ≤
        (1 + etaX / (1 - etaX)) • (1 : FullBlockMat d) :=
    bridgeMap_gram_le_of_clause hgram
      (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _) hHpd hFfull
  have hfin : ∀ r : ℤ, jStar ≤ r → r ≤ u + 2 * (l0 : ℤ) →
      HasFiniteAdaptedMean P (roundedGrid jStar mu) r := by
    intro r hr hrt
    exact (hdef _ (Or.inl rfl) r hr hrt).1
  have hfin' : ∀ r : ℤ, jStar ≤ r → r ≤ u + 2 * (l0 : ℤ) →
      HasFiniteAdaptedMean P (roundedGrid jStar mu') r := by
    intro r hr hrt
    exact (hdef _ (Or.inr rfl) r hr hrt).1
  have hIP : ∀ {j : ℤ}, jStar ≤ j → j ≤ u + (l0 : ℤ) →
      (1 : FullBlockMat d) ≤
        toFullBlockMat (relMean P (roundedGrid jStar mu') j (u + (l0 : ℤ))) := by
    intro j hj hjn'
    exact PortableHistory.one_le_relMean_window hPstat hq' le_rfl hfin' hj hjn' hnt
  have hcontt : adaptedCell (roundedGrid jStar mu) (u + 2 * (l0 : ℤ)) ⊆
      centeredCube d M := hcont _ (Or.inl rfl) _ hjt le_rfl
  have hcontn : adaptedCell (roundedGrid jStar mu') (u + (l0 : ℤ)) ⊆
      centeredCube d M := hcont _ (Or.inr rfl) _ hjn hnt
  obtain ⟨lam, hlam, _, _⟩ := exists_adaptive_depth rchk (l0 : ℤ)
  set U : ℝ := ∫ a, Y a ∂P with hU
  have hU0 : 0 ≤ U := by
    rw [hU]
    exact le_trans zero_le_one (one_le_integral_of_isWindowMultiplier hY)
  have hU2 : U ≤ 2 := by
    have hnorm := le_trans (ofReal_integral_le_lqNorm hY hQ1)
      (lqNorm_le_two hQ1 hw hY)
    have hof : ENNReal.ofReal U ≤ ENNReal.ofReal 2 := by
      simpa only [hU, show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 by norm_num] using hnorm
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hof
  set Dcont : ℝ :=
    6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu * zetaG g * U *
      (kappaRef E * (boundaryConst Cd g mu' * U)) with hDcont
  have hKhop0 : 0 ≤ Khop := le_trans zero_le_one hKhop
  have hB0 : 0 ≤ boundaryConst Cd g mu := zero_le_boundaryConst hCd0 hg1 mu
  have hB0' : 0 ≤ boundaryConst Cd g mu' := zero_le_boundaryConst hCd0 hg1 mu'
  have hzeta0 : 0 ≤ zetaG g := (zero_lt_zetaG hg1).le
  have hkappa0 : 0 ≤ kappaRef E := by
    rw [kappaRef, blockSize]
    exact Real.sInf_nonneg fun _ hx => hx.1
  have hDcont0 : 0 ≤ Dcont := by
    rw [hDcont]
    positivity
  have hDcontRow : Dcont ≤ Lam * transportContCoeff Cd g E jStar mu mu' := by
    simpa only [hDcont, hLam, hU] using
      srcRow_coefficient_absorbed hd1 hg0 hg1 hCd E mu mu' hKgrid hU0 hU2
  set Dsrc : ℝ := Lam * transportSrcCoeff Cd g E jStar mu mu' with hDsrc
  have hSrc1 : 1 ≤ transportSrcCoeff Cd g E jStar mu mu' :=
    one_le_transportSrcCoeff hCd0 hg1 E jStar mu mu'
  have hSrc0 : 0 ≤ transportSrcCoeff Cd g E jStar mu mu' :=
    le_trans zero_le_one hSrc1
  have hDsrc0 : 0 ≤ Dsrc := by
    rw [hDsrc]
    exact mul_nonneg hLam0 hSrc0
  have hDcontSrc : Dcont ≤ Dsrc := by
    rw [hDsrc]
    exact hDcontRow.trans (mul_le_mul_of_nonneg_left
      (transportContCoeff_le_transportSrcCoeff hCd0 hg1 E jStar mu mu') hLam0)
  have hEarlySrc : transportEarlyCoeff Cd g E mu' ≤ Dsrc := by
    rw [hDsrc]
    calc transportEarlyCoeff Cd g E mu'
        ≤ transportSrcCoeff Cd g E jStar mu mu' :=
          transportEarlyCoeff_le_transportSrcCoeff hCd0 hg1 E jStar mu mu'
      _ = 1 * transportSrcCoeff Cd g E jStar mu mu' := by ring
      _ ≤ Lam * transportSrcCoeff Cd g E jStar mu mu' :=
        mul_le_mul_of_nonneg_right hLam1 hSrc0
  have hearlyStep : ∀ j : ℤ, ∃ e : ℝ, 0 ≤ e ∧
      (j ∈ Finset.Ico jStar (jStar + (l0 : ℤ)) →
        e ≤ transportEarlyCoeff Cd g E mu' ∧
          toFullBlockMat
              (relMean P (roundedGrid jStar mu') j (u + (l0 : ℤ))) ≤
            1 + e • (1 : FullBlockMat d)) := by
    intro j
    by_cases hj : j ∈ Finset.Ico jStar (jStar + (l0 : ℤ))
    · obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      obtain ⟨e, he0, he1, he2⟩ :=
        exists_early_level_upper_mean (P := P) (E := E) (Ψ := Ψ) (K := K)
          (Cd := Cd) (Y := Y) (nu' := mu') (n := u + (l0 : ℤ)) (j := j)
          hQ1 hCd hg1 hced.refBlock_isSymm hced.refBlock_posDef hw hY hmu' hq'
          hjn hj1 hcontn
          (hcont _ (Or.inr rfl) j hj1 (by omega))
      exact ⟨e, he0, fun _ => ⟨he1, he2⟩⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose epsE hepsE using hearlyStep
  let eps : ℤ → ℝ := fun j =>
    if j < jStar + (l0 : ℤ) then epsE j else Dcont * (3 : ℝ) ^ (jStar - j)
  have heps0 : ∀ j : ℤ, 0 ≤ eps j := by
    intro j
    by_cases hj : j < jStar + (l0 : ℤ)
    · simp only [eps, if_pos hj]
      exact (hepsE j).1
    · simp only [eps, if_neg hj]
      exact mul_nonneg hDcont0 (zpow_nonneg (by norm_num) _)
  have hearlyCoeff : ∀ j : ℤ, jStar ≤ j → j < jStar + (l0 : ℤ) →
      eps j ≤ transportEarlyCoeff Cd g E mu' := by
    intro j hj1 hj2
    simpa only [eps, if_pos hj2] using
      (hepsE j).2 (Finset.mem_Ico.mpr ⟨hj1, hj2⟩) |>.1
  have hcontCoeff : ∀ j : ℤ, jStar + (l0 : ℤ) ≤ j →
      eps j ≤ Dcont *
        (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) := by
    intro j hj
    simp only [eps, if_neg (not_lt_of_ge hj)]
    exact mul_le_mul_of_nonneg_left
      (zpow_le_rpow_boundary_rate hg0 (by omega : jStar ≤ j)) hDcont0
  have hconst : (2 : ℝ) ^ (Q : ℝ) *
      (2 * 2 ^ (Q : ℝ) * (1 + 2 * (d : ℝ)) ^ (Q : ℝ)) = A := by
    rw [hA, show 2 * (Q : ℝ) + 1 = (Q : ℝ) + ((Q : ℝ) + 1) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  have hnl : nonlinearHistory P (Q : ℝ) a (roundedGrid jStar mu') jStar
        (u + (l0 : ℤ)) ≤
      ENNReal.ofReal (Cnl * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
          portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu) jStar rchk
            (u + 2 * (l0 : ℤ)) +
        ENNReal.ofReal (Cnl * etaX) +
        ENNReal.ofReal (Cnl * ∑ j ∈ Finset.Ico jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) *
            (eps j + eps j ^ (Q : ℝ))) := by
    refine nonlinear_bound (P := P) (q := roundedGrid jStar mu)
      (q' := roundedGrid jStar mu') (jStar := jStar) (TMax := u + 2 * (l0 : ℤ))
      hQR halo hahi hadm hl0z (by omega) hPstat hq le_rfl hfin hjr (by omega)
      le_rfl hlam hA0 (mul_nonneg hA0 (by positivity)) (by linarith only [hA0])
      hA0 heta0 (fun j => add_nonneg (heps0 j) (Real.rpow_nonneg (heps0 j) _))
      hCnlAdeq ?_ ?_
    · intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hOne := hIP hj1 (by omega)
      have h1 := frakH_le_gapG_of_le (by omega : 0 < d) hQ1 hOne le_rfl
      have hUpper :
          toFullBlockMat
              (relMean P (roundedGrid jStar mu') j (u + (l0 : ℤ))) ≤
            1 + eps j • (1 : FullBlockMat d) := by
        simpa only [eps, if_pos hj2] using ((hepsE j).2 hj).2
      have h2 := cell_gap_early hd1 hQ1 (heps0 j) hOne hUpper
      have h3 := mul_le_mul_of_nonneg_left h2
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Q : ℝ))
      have hE : (2 : ℝ) ^ (Q : ℝ) *
          (2 * 2 ^ (Q : ℝ) * (1 + 2 * (d : ℝ)) ^ (Q : ℝ) *
            (eps j + eps j ^ (Q : ℝ))) =
          A * (eps j + eps j ^ (Q : ℝ)) := by
        rw [← hconst]
        ring
      linarith only [h1, h3, hE]
    · intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      have hdep := one_le_depth_and_le hl0z hlam j
      obtain ⟨Z, Pbar, Mblk, Phat, KW, Rm, hZ, hPbar, hM, hPhat, hKW, hPK, hR⟩ :=
        exists_continued_level_filling (P := P) (E := E) (Ψ := Ψ) (K := K)
          (Cd := Cd) (Y := Y) (nu := mu) (nu' := mu') (Khop := Khop)
          (t := u + 2 * (l0 : ℤ)) (n := u + (l0 : ℤ)) (j := j)
          (m := j - lam j) hd1 hCdpos hg1 hced.refBlock_isSymm
          hced.refBlock_posDef hPstat hY hmu hmu' hq hq' hKgrid hjt hjn
          (by omega) (by omega) 0 hcontt hcontn
          (by
            rw [PortableHistory.adaptedCellAt_zero]
            exact hcont _ (Or.inr rfl) j (by omega) (by omega))
      have hReps : toFullBlockMat Rm ≤ eps j • (1 : FullBlockMat d) := by
        rw [show eps j = Dcont * (3 : ℝ) ^ (jStar - j) by
          simp only [eps, if_neg (not_lt_of_ge hj1)]]
        rw [hDcont, hU]
        convert hR using 1
        ring_nf
      exact nonlinear_row_of_filling hd1 hQ1 hg0 hPstat hq'pd hq le_rfl hKgrid
        (by omega) (by omega) (by omega) hfin hZ heta0 heta4 (heps0 j) hS hReps
        hPbar hM hPhat hKW (hIP (by omega) (by omega)) hPK
  have hrows := source_rows_le halo hahi hQ1 hDcont0 hDsrc0 hDcontSrc hEarlySrc
    heps0 hl0z0 hearlyCoeff hcontCoeff (u + (l0 : ℤ))
    (Finset.Ico jStar (u + (l0 : ℤ)))
    (fun j hj => (Finset.mem_Ico.mp hj).1)
  have hbuf0 : 0 ≤ (3 : ℝ) ^ (a * ((l0 : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmass0 : 0 ≤
      (Dsrc + Dsrc ^ (Q : ℝ)) *
        (3 : ℝ) ^
          (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - (jStar : ℝ))) := by
    exact mul_nonneg
      (add_nonneg hDsrc0 (Real.rpow_nonneg hDsrc0 (Q : ℝ)))
      (Real.rpow_nonneg (by norm_num) _)
  have hrowsC :
      ∑ j ∈ Finset.Ico jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) *
            (eps j + eps j ^ (Q : ℝ)) ≤
        Csrc * (3 : ℝ) ^ (a * ((l0 : ℤ) : ℝ)) *
          ((Dsrc + Dsrc ^ (Q : ℝ)) *
            (3 : ℝ) ^
              (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - (jStar : ℝ)))) := by
    refine hrows.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCsrcAdeq hbuf0) hmass0
  have hrem :
      (Dsrc + Dsrc ^ (Q : ℝ)) *
          (3 : ℝ) ^
            (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - (jStar : ℝ))) ≤
        Lam ^ (Q : ℝ) *
          transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
            (u + (l0 : ℤ)) := by
    refine srcRemainder_absorbed hQ1 hLam1 hDsrc0 E mu mu'
      (u + (l0 : ℤ)) hCd0 hg1 ?_
    rw [hDsrc]
  have hrowsFinal :
      ∑ j ∈ Finset.Ico jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) *
            (eps j + eps j ^ (Q : ℝ)) ≤
        Csrc * (3 : ℝ) ^ (a * ((l0 : ℤ) : ℝ)) *
          (Lam ^ (Q : ℝ) *
            transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
              (u + (l0 : ℤ))) := by
    exact hrowsC.trans (mul_le_mul_of_nonneg_left hrem (mul_nonneg hCsrc0 hbuf0))
  refine hnl.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  calc Cnl *
        (∑ j ∈ Finset.Ico jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) *
            (eps j + eps j ^ (Q : ℝ)))
      ≤ Cnl *
          (Csrc * (3 : ℝ) ^ (a * ((l0 : ℤ) : ℝ)) *
            (Lam ^ (Q : ℝ) *
              transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                (u + (l0 : ℤ)))) := mul_le_mul_of_nonneg_left hrowsFinal hCnl0
    _ = CnlS * (3 : ℝ) ^ (a * (l0 : ℝ)) *
          transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
            (u + (l0 : ℤ)) := by
      rw [hCnlS]
      norm_num
      ring

end

end Transport
end HighContrast
end Homogenization
