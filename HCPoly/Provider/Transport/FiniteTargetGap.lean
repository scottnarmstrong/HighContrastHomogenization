/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FiniteTargetHistory
import HCPoly.Provider.Transport.CellMajorantGapAt
import HCPoly.Provider.Transport.NonlinearLevelFamilies
import HCPoly.Provider.Transport.UnshiftedNonlinearRows
import HCPoly.Provider.Transport.SourceConvolution
import HCPoly.Provider.Transport.TransportConclusion
import HCPoly.Provider.Transport.WindowMomentBound

/-!
# The weighted gap of the finite transported target family

The exact number of target cells at each scale converts the target weight into
the centered row weight.  The direct and lower nonlinear rows are then paid by
the unshifted convolution, while the bridge and source rows are discharged
separately.  The source row uses split depth zero, so its filling inflation is
paid exactly once.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Exact target-cell cardinalities convert the powered target weights into
the centered level weights. -/
theorem finite_target_weight_sum_eq {Q rhoMax : ℝ} {jStar n : ℤ}
    (Z : ℤ → Finset (Fin d → ℤ))
    (hcard : ∀ j ∈ Finset.Icc jStar n,
      (Z j).card = 3 ^ (d * (n - j).toNat)) (b : ℤ → ℝ) :
    ∑ i ∈ (Finset.Icc jStar n).sigma Z,
        ((3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ)))) ^ Q * b i.1 =
      ∑ j ∈ Finset.Icc jStar n,
        (3 : ℝ) ^ (-(Q * rhoMax - (d : ℝ)) *
          ((n : ℝ) - (j : ℝ))) * b j := by
  rw [← Finset.sum_sigma' (Finset.Icc jStar n) Z
    (fun j _z => ((3 : ℝ) ^ (rhoMax * ((j : ℝ) - (n : ℝ)))) ^ Q * b j)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [smul_eq_mul, hcard j hj]
  have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
  have hdiff : ((n - j).toNat : ℝ) = (n : ℝ) - (j : ℝ) := by
    have hz : ((n - j).toNat : ℤ) = n - j :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hjn)
    exact_mod_cast hz
  rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [← mul_assoc]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  rw [Nat.cast_mul, hdiff]
  congr 1
  ring_nf

/-- The exact finite target family admits simultaneous raw majorants whose
powered weighted `gapG` total is controlled by the incoming nonlinear rows,
the bridge error, and the transported source remainder.  The returned order
data is in the normalized form consumed by `finite_family_positive_gap`. -/
theorem exists_finite_target_majorants_gap_sum_le
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Q : ℕ) (hQ : 2 ≤ Q) (rhoMax a : ℝ)
    (hadef : a = (Q : ℝ) * (rhoMax - g) - (d : ℝ))
    (halo : 0 < a) (hahi : a < 1 - g) (Khop : ℝ) (hKhop : 1 ≤ Khop)
    (l0 : ℕ) (hl0 : 1 ≤ l0) (Cd : ℝ) (hCd : 1 ≤ Cd)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hPprob : IsProbabilityMeasure P)
    (hPstat : HCPoly.Frozen.IsStationaryLaw P)
    (hced : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (jStar M : ℤ) (hw : IsCoupledWindow d Q K jStar M)
    (Y : CoeffSpace d → ℝ)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (mu mu' : Mat d) (hmu : mu.PosDef) (hmu' : mu'.PosDef)
    (hKgrid : gridRatio (roundedGrid jStar mu)
      (roundedGrid jStar mu') ≤ Khop)
    (rchk u : ℤ) (hjr : jStar ≤ rchk) (hru : rchk ≤ u)
    (hcont : ∀ r : Mat d,
      r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
      ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
        adaptedCell r j ⊆ centeredCube d M)
    (etaX : ℝ) (heta0 : 0 ≤ etaX) (heta4 : etaX ≤ 1 / 4)
    (hlo : BlockMatLoewnerLE
      (blockScale (1 - etaX)
        (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ))))
      (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))))
    (hhi : BlockMatLoewnerLE
      (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))
      (blockScale (1 + etaX)
        (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ))))) :
    ∃ (Z : ℤ → Finset (Fin d → ℤ))
        (hs : ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))).Nonempty)
        (Zfill : ((_ : ℤ) × (Fin d → ℤ)) →
          ℤ → Finset (Fin d → ℤ))
        (cfill : ((_ : ℤ) × (Fin d → ℤ)) → ℤ → ℝ)
        (Gmajor : ((_ : ℤ) × (Fin d → ℤ)) → CoeffSpace d → BlockMat d)
        (Kmajor : ((_ : ℤ) × (Fin d → ℤ)) → BlockMat d),
      (∀ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
        (↑(Z j) : Set (Fin d → ℤ)) =
            {w | adaptedCellCenter (roundedGrid jStar mu') j w ∈
              adaptedCell (roundedGrid jStar mu') (u + (l0 : ℤ))} ∧
          (Z j).card = 3 ^ (d * (u + (l0 : ℤ) - j).toNat)) ∧
      (∀ i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))),
        adaptedCellAt (roundedGrid jStar mu') i.1 i.2 ⊆
          adaptedCell (roundedGrid jStar mu') (u + (l0 : ℤ))) ∧
      (∀ i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))),
        0 < (3 : ℝ) ^
          (rhoMax * ((i.1 : ℝ) - ((u + (l0 : ℤ) : ℤ) : ℝ)))) ∧
      centeredHistory P (Q : ℝ) rhoMax (roundedGrid jStar mu') jStar
          (u + (l0 : ℤ)) ≤
        ∫⁻ x, ENNReal.ofReal
          (((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z).sup' hs fun i =>
            (3 : ℝ) ^
                (rhoMax * ((i.1 : ℝ) - ((u + (l0 : ℤ) : ℤ) : ℝ))) *
              schattenSize (Q : ℝ)
                (blockSub
                  (adaptedResponse (roundedGrid jStar mu') i.1 i.2 x)
                  (adaptedMean P (roundedGrid jStar mu') i.1))
                (adaptedMean P (roundedGrid jStar mu')
                  (u + (l0 : ℤ)))) ^ (Q : ℝ) ∂P ∧
      (∀ i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))),
        (∀ r, ↑(Zfill i r) =
          fillingIndex (roundedGrid jStar mu) i.1
            (adaptedCellAt (roundedGrid jStar mu') i.1 i.2) r) ∧
        (∀ r, ∀ w ∈ Zfill i r,
          adaptedCellAt (roundedGrid jStar mu) r w ⊆
            adaptedCellAt (roundedGrid jStar mu') i.1 i.2) ∧
        (∀ r, 0 ≤ cfill i r) ∧
        (∀ r, ∀ w ∈ Zfill i r,
          (volume (adaptedCellAt (roundedGrid jStar mu) r w)).toReal /
              (volume (adaptedCellAt
                (roundedGrid jStar mu') i.1 i.2)).toReal = cfill i r) ∧
        (∑ r ∈ Finset.Icc jStar i.1,
          ∑ _w ∈ Zfill i r, cfill i r) ≤ 1 ∧
        (∀ r ∈ Finset.Icc jStar i.1, r < i.1 →
          (∑ _w ∈ Zfill i r, cfill i r) ≤
            6 * (d : ℝ) * Real.sqrt d * Khop *
              (3 : ℝ) ^ ((r : ℝ) - (i.1 : ℝ))) ∧
        (∀ x, toFullBlockMat
            (adaptedResponse (roundedGrid jStar mu') i.1 i.2 x) ≤
          toFullBlockMat (Gmajor i x)) ∧
        (∀ x, IsSymmetricBlockMat (Gmajor i x)) ∧
        (∀ α β : BlockCoord d,
          AEStronglyMeasurable
            (fun x => toFullBlockMat (Gmajor i x) α β) P) ∧
        Integrable (fun x => toFullBlockMat (Gmajor i x)) P ∧
        (∫ x, toFullBlockMat (Gmajor i x) ∂P) =
          toFullBlockMat (Kmajor i) ∧
        IsSymmetricBlockMat (Kmajor i) ∧
        (toFullBlockMat (Kmajor i) =
          (∑ r ∈ Finset.Icc jStar i.1,
              (∑ _w ∈ Zfill i r, cfill i r) •
                toFullBlockMat
                  (adaptedMean P (roundedGrid jStar mu) r)) +
            (6 * (d : ℝ) * Real.sqrt d * Khop *
              boundaryConst Cd g mu * zetaG g *
              (3 : ℝ) ^ (jStar - i.1) * ∫ x, Y x ∂P) •
                toFullBlockMat E) ∧
        (∀ᵐ x ∂P, toFullBlockMat (blockSub (Gmajor i x) (Kmajor i)) =
          (∑ r ∈ Finset.Icc jStar i.1,
            ∑ w ∈ Zfill i r, cfill i r •
              toFullBlockMat (blockSub
                (coarseBlock
                  (adaptedCellAt (roundedGrid jStar mu) r w) x)
                (adaptedMean P (roundedGrid jStar mu) r))) +
            (6 * (d : ℝ) * Real.sqrt d * Khop *
              boundaryConst Cd g mu * zetaG g *
              (3 : ℝ) ^ (jStar - i.1) *
                (Y x - ∫ y, Y y ∂P)) • toFullBlockMat E) ∧
        toFullBlockMat (adaptedMean P (roundedGrid jStar mu') i.1) ≤
          toFullBlockMat (Kmajor i) ∧
        (1 : FullBlockMat d) ≤ toFullBlockMat
          (normalizedBlock
            (adaptedMean P (roundedGrid jStar mu') i.1)
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ∧
        toFullBlockMat
            (normalizedBlock
              (adaptedMean P (roundedGrid jStar mu') i.1)
              (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ≤
          toFullBlockMat
            (normalizedBlock (Kmajor i)
              (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))))) ∧
      (let B : ℝ :=
          (2 * 2 ^ (Q : ℝ) * (1 + 2 * (d : ℝ)) ^ (Q : ℝ)) *
            ((1 + (6 * (d : ℝ) * Real.sqrt d * Khop) *
                ((3 : ℝ) ^ (-(1 - g - a)) /
                  (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
                (3 : ℝ) ^ (a * (l0 : ℝ)) *
                ∑ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
                  (3 : ℝ) ^
                      (-a * (((u + 2 * (l0 : ℤ) : ℤ) : ℝ) - 1 - (r : ℝ))) *
                    frakH (Q : ℝ)
                      (relMean P (roundedGrid jStar mu) r
                        (u + 2 * (l0 : ℤ))) +
              6 * (1 / (1 - (3 : ℝ) ^
                (-((Q : ℝ) * rhoMax - (d : ℝ))))) * etaX +
              ((3 : ℝ) ^ a *
                (1 / (1 - (3 : ℝ) ^ (-a)) +
                  1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
                  1 / (1 - (3 : ℝ) ^
                    (-((Q : ℝ) * (1 - g) - a))))) *
                (18 * (d : ℝ) * Real.sqrt d * Khop) ^ (Q : ℝ) *
                transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                  (u + (l0 : ℤ)));
        0 ≤ B ∧
          ∑ i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
              Finset ((_ : ℤ) × (Fin d → ℤ))),
            ((3 : ℝ) ^
              (rhoMax * ((i.1 : ℝ) - ((u + (l0 : ℤ) : ℤ) : ℝ)))) ^
                (Q : ℝ) *
              gapG (Q : ℝ)
                (normalizedBlock (Kmajor i)
                  (adaptedMean P (roundedGrid jStar mu')
                    (u + (l0 : ℤ)))) ≤ B) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  letI : IsProbabilityMeasure P := hPprob
  have hd1 : 1 ≤ d := le_trans (by omega) hd
  have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := le_trans zero_le_one hQ1
  have hg0 : 0 ≤ g := hg.1
  have hg1 : g < 1 := hg.2
  have hCd0 : (0 : ℝ) ≤ Cd := le_trans zero_le_one hCd
  have hCdpos : (0 : ℝ) < Cd := lt_of_lt_of_le zero_lt_one hCd
  have hKhop0 : 0 ≤ Khop := le_trans zero_le_one hKhop
  have hl0z : (1 : ℤ) ≤ (l0 : ℤ) := by exact_mod_cast hl0
  have hjn : jStar ≤ u + (l0 : ℤ) := by omega
  have hjt : jStar ≤ u + 2 * (l0 : ℤ) := by omega
  have hnt : u + (l0 : ℤ) ≤ u + 2 * (l0 : ℤ) := by omega
  have hq := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu
  have hq' := isRoundedGrid_roundedGrid_of_isCoupledWindow hw hmu'
  have hq'pd : (roundedGrid jStar mu').PosDef := Recurrence.posDef_of_isRoundedGrid hq'
  obtain ⟨hdef, _, hbridge⟩ :=
    transport_definedness_and_bridge d hd g Q hQ l0 Cd P E Ψ K S hPprob
      hPstat hced jStar M hw Y hY mu mu' hmu hmu' rchk u hjr hru hcont
  obtain ⟨_, _, _, hgram, _, _⟩ := hbridge etaX heta0 heta4 hlo hhi
  have hHpd : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ))) :=
    (hdef _ (Or.inl rfl) _ hjt le_rfl).2.1
  have hFpd : Book.Ch02.BlockPosDef
      (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))) :=
    (hdef _ (Or.inr rfl) _ hjn hnt).2.1
  have hHfull :
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu)
        (u + 2 * (l0 : ℤ)))).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _) hHpd
  have hFfull :
      (toFullBlockMat (adaptedMean P (roundedGrid jStar mu')
        (u + (l0 : ℤ)))).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _) hFpd
  let eta : ℝ := etaX / (1 - etaX)
  have hdenEta : 0 < 1 - etaX := by linarith only [heta4]
  have heta0' : 0 ≤ eta := by
    simp only [eta]
    positivity
  have heta3 : eta ≤ 1 / 3 := by
    simp only [eta]
    apply (div_le_iff₀ hdenEta).2
    nlinarith only [heta4]
  have heta2 : eta ≤ 2 * etaX := by
    simp only [eta]
    apply (div_le_iff₀ hdenEta).2
    nlinarith only [heta0, heta4]
  have hS :
      (bridgeMap
          (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ)))
          (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))))ᵀ *
          bridgeMap
            (adaptedMean P (roundedGrid jStar mu) (u + 2 * (l0 : ℤ)))
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))) ≤
        (1 + eta) • (1 : FullBlockMat d) := by
    simp only [eta]
    exact bridgeMap_gram_le_of_clause hgram
      (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _) hHpd hFfull
  have hfin : ∀ r : ℤ, jStar ≤ r → r ≤ u + 2 * (l0 : ℤ) →
      HasFiniteAdaptedMean P (roundedGrid jStar mu) r := by
    intro r hr hrt
    exact (hdef _ (Or.inl rfl) r hr hrt).1
  have hfin' : ∀ r : ℤ, jStar ≤ r → r ≤ u + 2 * (l0 : ℤ) →
      HasFiniteAdaptedMean P (roundedGrid jStar mu') r := by
    intro r hr hrt
    exact (hdef _ (Or.inr rfl) r hr hrt).1
  have hIP : ∀ {r : ℤ}, jStar ≤ r → r ≤ u + 2 * (l0 : ℤ) →
      (1 : FullBlockMat d) ≤
        toFullBlockMat
          (relMean P (roundedGrid jStar mu) r (u + 2 * (l0 : ℤ))) := by
    intro r hr hrt
    exact PortableHistory.one_le_relMean_window hPstat hq le_rfl hfin hr hrt le_rfl
  have hIP' : ∀ {j : ℤ}, jStar ≤ j → j ≤ u + (l0 : ℤ) →
      (1 : FullBlockMat d) ≤
        toFullBlockMat
          (relMean P (roundedGrid jStar mu') j (u + (l0 : ℤ))) := by
    intro j hj hjn'
    exact PortableHistory.one_le_relMean_window hPstat hq' le_rfl hfin' hj hjn' hnt
  have hcontn : adaptedCell (roundedGrid jStar mu') (u + (l0 : ℤ)) ⊆
      centeredCube d M := hcont _ (Or.inr rfl) _ hjn hnt
  set U : ℝ := ∫ x, Y x ∂P with hU
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
  have hB0 : 0 ≤ boundaryConst Cd g mu := zero_le_boundaryConst hCd0 hg1 mu
  have hB0' : 0 ≤ boundaryConst Cd g mu' := zero_le_boundaryConst hCd0 hg1 mu'
  have hzeta0 : 0 ≤ zetaG g := (zero_lt_zetaG hg1).le
  have hkappa0 : 0 ≤ kappaRef E := by
    rw [kappaRef, blockSize]
    exact Real.sInf_nonneg fun _ hx => hx.1
  have hDcont0 : 0 ≤ Dcont := by
    rw [hDcont]
    positivity
  set Lam : ℝ := 18 * (d : ℝ) * Real.sqrt d * Khop with hLam
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hdR1
  have hLam1 : 1 ≤ Lam := by
    rw [hLam]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (by norm_num) hdR1) hsqrt1)
      hKhop
  have hLam0 : 0 ≤ Lam := le_trans zero_le_one hLam1
  have hDcontRow : Dcont ≤
      Lam * transportContCoeff Cd g E jStar mu mu' := by
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
  let hold : ℤ → ℝ := fun r => frakH (Q : ℝ)
    (relMean P (roundedGrid jStar mu) r (u + 2 * (l0 : ℤ)))
  let eps : ℤ → ℝ := fun j => Dcont * (3 : ℝ) ^ (jStar - j)
  let Crow : ℝ := 6 * (d : ℝ) * Real.sqrt d * Khop
  let row : ℤ → ℝ := fun j => hold j + Crow *
    ∑ r ∈ Finset.Ico jStar j,
      (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * hold r
  let src : ℤ → ℝ := fun j => eps j + eps j ^ (Q : ℝ)
  let A : ℝ := 2 * 2 ^ (Q : ℝ) * (1 + 2 * (d : ℝ)) ^ (Q : ℝ)
  have hCrow0 : 0 ≤ Crow := by
    simp only [Crow]
    positivity
  have hA0 : 0 ≤ A := by
    simp only [A]
    positivity
  have heps0 : ∀ j : ℤ, 0 ≤ eps j := by
    intro j
    exact mul_nonneg hDcont0 (zpow_nonneg (by norm_num) _)
  obtain ⟨Z, hs, hZcard, hZsub, hwt, hhistory⟩ :=
    exists_finite_target_family_centeredHistory_le
      (Q := (Q : ℝ)) (rhoMax := rhoMax) hq'pd hjn
      (lt_of_lt_of_le zero_lt_one hQ1) hFpd
  have hchoice : ∀ i : ((_ : ℤ) × (Fin d → ℤ)),
      ∃ (Zi : ℤ → Finset (Fin d → ℤ)) (ci : ℤ → ℝ)
          (Gm : CoeffSpace d → BlockMat d) (KG : BlockMat d),
        i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
            Finset ((_ : ℤ) × (Fin d → ℤ))) →
          (∀ r, ↑(Zi r) = fillingIndex (roundedGrid jStar mu) i.1
            (adaptedCellAt (roundedGrid jStar mu') i.1 i.2) r) ∧
          (∀ r, ∀ w ∈ Zi r,
            adaptedCellAt (roundedGrid jStar mu) r w ⊆
              adaptedCellAt (roundedGrid jStar mu') i.1 i.2) ∧
          (∀ r, 0 ≤ ci r) ∧
          (∀ r, ∀ w ∈ Zi r,
            (volume (adaptedCellAt (roundedGrid jStar mu) r w)).toReal /
                (volume (adaptedCellAt
                  (roundedGrid jStar mu') i.1 i.2)).toReal = ci r) ∧
          (∑ r ∈ Finset.Icc jStar i.1, ∑ _w ∈ Zi r, ci r) ≤ 1 ∧
          (∀ r ∈ Finset.Icc jStar i.1, r < i.1 →
            (∑ _w ∈ Zi r, ci r) ≤
              Crow * (3 : ℝ) ^ ((r : ℝ) - (i.1 : ℝ))) ∧
          (∀ x, toFullBlockMat
              (adaptedResponse (roundedGrid jStar mu') i.1 i.2 x) ≤
            toFullBlockMat (Gm x)) ∧
          (∀ x, IsSymmetricBlockMat (Gm x)) ∧
          (∀ α β : BlockCoord d,
            AEStronglyMeasurable (fun x => toFullBlockMat (Gm x) α β) P) ∧
          Integrable (fun x => toFullBlockMat (Gm x)) P ∧
          (∫ x, toFullBlockMat (Gm x) ∂P) = toFullBlockMat KG ∧
          IsSymmetricBlockMat KG ∧
          (toFullBlockMat KG =
            (∑ r ∈ Finset.Icc jStar i.1,
                (∑ _w ∈ Zi r, ci r) •
                  toFullBlockMat
                    (adaptedMean P (roundedGrid jStar mu) r)) +
              (Crow * boundaryConst Cd g mu * zetaG g *
                (3 : ℝ) ^ (jStar - i.1) * U) • toFullBlockMat E) ∧
          (∀ᵐ x ∂P, toFullBlockMat (blockSub (Gm x) KG) =
            (∑ r ∈ Finset.Icc jStar i.1,
              ∑ w ∈ Zi r, ci r •
                toFullBlockMat (blockSub
                  (coarseBlock
                    (adaptedCellAt (roundedGrid jStar mu) r w) x)
                  (adaptedMean P (roundedGrid jStar mu) r))) +
              (Crow * boundaryConst Cd g mu * zetaG g *
                (3 : ℝ) ^ (jStar - i.1) *
                  (Y x - U)) • toFullBlockMat E) ∧
          toFullBlockMat (adaptedMean P (roundedGrid jStar mu') i.1) ≤
            toFullBlockMat KG ∧
          (1 : FullBlockMat d) ≤ toFullBlockMat
            (normalizedBlock
              (adaptedMean P (roundedGrid jStar mu') i.1)
              (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ∧
          toFullBlockMat
              (normalizedBlock
                (adaptedMean P (roundedGrid jStar mu') i.1)
                (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ≤
            toFullBlockMat
              (normalizedBlock KG
                (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ∧
          gapG (Q : ℝ)
              (normalizedBlock KG
                (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ≤
            A * (row i.1 + 3 * eta + src i.1) := by
    intro i
    by_cases hi : i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
        Finset ((_ : ℤ) × (Fin d → ℤ)))
    · obtain ⟨hij, hiz⟩ := Finset.mem_sigma.mp hi
      obtain ⟨hij0, hijn⟩ := Finset.mem_Icc.mp hij
      have hconti : adaptedCellAt (roundedGrid jStar mu') i.1 i.2 ⊆
          centeredCube d M := (hZsub i hi).trans hcontn
      have hPold : ∀ r ∈ Finset.Icc jStar i.1,
          (1 : FullBlockMat d) ≤ toFullBlockMat
            (relMean P (roundedGrid jStar mu) r (u + 2 * (l0 : ℤ))) := by
        intro r hr
        obtain ⟨hr0, hri⟩ := Finset.mem_Icc.mp hr
        exact hIP hr0 (hri.trans (hijn.trans hnt))
      have hPnew : (1 : FullBlockMat d) ≤ toFullBlockMat
          (relMean P (roundedGrid jStar mu') i.1 (u + (l0 : ℤ))) :=
        hIP' hij0 hijn
      obtain ⟨Zi, ci, Gm, KG, hZi, hZisub, hci, hciratio, hmass, hboundary,
          hdom, hGsym, hGmeas, hGint, hGmean, hKGsym, hKG, hcentered,
          hmean, hgap⟩ :=
        exists_cell_majorant_gap_at (P := P) (g := g) (E := E) (Ψ := Ψ)
          (K := K) (Cd := Cd) (Y := Y) (mu := mu) (mu' := mu')
          (Khop := Khop) (t := u + 2 * (l0 : ℤ))
          (n := u + (l0 : ℤ)) (j := i.1) hd1 hCdpos hg0 hg1
          hced.refBlock_isSymm hced.refBlock_posDef hPstat hY hmu hmu' hq hq'
          hKgrid hjn hij0 i.2 hcontn hconti hQ1 heta0' heta3 hHfull hFfull hS
          hPold hPnew
      have hIH : (1 : FullBlockMat d) ≤ toFullBlockMat
          (normalizedBlock
            (adaptedMean P (roundedGrid jStar mu') i.1)
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) := by
        simpa only [Recurrence.toFullBlockMat_normalizedBlock,
          Recurrence.toFullBlockMat_relMean] using hPnew
      have hHK : toFullBlockMat
            (normalizedBlock
              (adaptedMean P (roundedGrid jStar mu') i.1)
              (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ≤
          toFullBlockMat
              (normalizedBlock KG
                (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) := by
        rw [Recurrence.toFullBlockMat_normalizedBlock,
          Recurrence.toFullBlockMat_normalizedBlock]
        exact conj_le_conj' (C := matSqrt
          (toFullBlockMat (adaptedMean P (roundedGrid jStar mu')
            (u + (l0 : ℤ))))⁻¹)
          (by
            rw [conjTranspose_eq_transpose']
            exact transpose_matSqrt_inv hFfull) hmean
      refine ⟨Zi, ci, Gm, KG, ?_⟩
      intro _
      refine ⟨hZi, hZisub, hci, hciratio, hmass, ?_, ?_, hGsym, hGmeas,
        hGint, hGmean, hKGsym, ?_, ?_, hmean, hIH, hHK, ?_⟩
      · simpa only [Crow] using hboundary
      · simpa only [adaptedResponse] using hdom
      · simpa only [Crow, U] using hKG
      · simpa only [Crow, U] using hcentered
      · have hepsCell : eps i.1 =
            (6 * (d : ℝ) * Real.sqrt d * Khop * boundaryConst Cd g mu *
              zetaG g * (3 : ℝ) ^ (jStar - i.1) * U) *
                (kappaRef E * (boundaryConst Cd g mu' * U)) := by
          simp only [eps, Dcont]
          ring
        simpa only [A, row, hold, Crow, eta, src, hepsCell, U] using hgap
    · refine ⟨fun _ => ∅, fun _ => 0,
        fun _ : CoeffSpace d => E, E, ?_⟩
      intro hi'
      exact (hi hi').elim
  choose Zfill cfill Gmajor Kmajor hmajor using hchoice
  have hmajorOut : ∀ i ∈
      ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
        Finset ((_ : ℤ) × (Fin d → ℤ))),
      (∀ r, ↑(Zfill i r) =
        fillingIndex (roundedGrid jStar mu) i.1
          (adaptedCellAt (roundedGrid jStar mu') i.1 i.2) r) ∧
      (∀ r, ∀ w ∈ Zfill i r,
        adaptedCellAt (roundedGrid jStar mu) r w ⊆
          adaptedCellAt (roundedGrid jStar mu') i.1 i.2) ∧
      (∀ r, 0 ≤ cfill i r) ∧
      (∀ r, ∀ w ∈ Zfill i r,
        (volume (adaptedCellAt (roundedGrid jStar mu) r w)).toReal /
            (volume (adaptedCellAt
              (roundedGrid jStar mu') i.1 i.2)).toReal = cfill i r) ∧
      (∑ r ∈ Finset.Icc jStar i.1,
        ∑ _w ∈ Zfill i r, cfill i r) ≤ 1 ∧
      (∀ r ∈ Finset.Icc jStar i.1, r < i.1 →
        (∑ _w ∈ Zfill i r, cfill i r) ≤
          6 * (d : ℝ) * Real.sqrt d * Khop *
            (3 : ℝ) ^ ((r : ℝ) - (i.1 : ℝ))) ∧
      (∀ x, toFullBlockMat
          (adaptedResponse (roundedGrid jStar mu') i.1 i.2 x) ≤
        toFullBlockMat (Gmajor i x)) ∧
      (∀ x, IsSymmetricBlockMat (Gmajor i x)) ∧
      (∀ α β : BlockCoord d,
        AEStronglyMeasurable
          (fun x => toFullBlockMat (Gmajor i x) α β) P) ∧
      Integrable (fun x => toFullBlockMat (Gmajor i x)) P ∧
      (∫ x, toFullBlockMat (Gmajor i x) ∂P) =
        toFullBlockMat (Kmajor i) ∧
      IsSymmetricBlockMat (Kmajor i) ∧
      (toFullBlockMat (Kmajor i) =
        (∑ r ∈ Finset.Icc jStar i.1,
            (∑ _w ∈ Zfill i r, cfill i r) •
              toFullBlockMat
                (adaptedMean P (roundedGrid jStar mu) r)) +
          (6 * (d : ℝ) * Real.sqrt d * Khop *
            boundaryConst Cd g mu * zetaG g *
            (3 : ℝ) ^ (jStar - i.1) * ∫ x, Y x ∂P) •
              toFullBlockMat E) ∧
      (∀ᵐ x ∂P, toFullBlockMat (blockSub (Gmajor i x) (Kmajor i)) =
        (∑ r ∈ Finset.Icc jStar i.1,
          ∑ w ∈ Zfill i r, cfill i r •
            toFullBlockMat (blockSub
              (coarseBlock
                (adaptedCellAt (roundedGrid jStar mu) r w) x)
              (adaptedMean P (roundedGrid jStar mu) r))) +
          (6 * (d : ℝ) * Real.sqrt d * Khop *
            boundaryConst Cd g mu * zetaG g *
            (3 : ℝ) ^ (jStar - i.1) *
              (Y x - ∫ y, Y y ∂P)) • toFullBlockMat E) ∧
      toFullBlockMat (adaptedMean P (roundedGrid jStar mu') i.1) ≤
        toFullBlockMat (Kmajor i) ∧
      (1 : FullBlockMat d) ≤ toFullBlockMat
        (normalizedBlock
          (adaptedMean P (roundedGrid jStar mu') i.1)
          (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ∧
      toFullBlockMat
          (normalizedBlock
            (adaptedMean P (roundedGrid jStar mu') i.1)
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ≤
        toFullBlockMat
          (normalizedBlock (Kmajor i)
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) := by
    intro i hi
    rcases hmajor i hi with
      ⟨hZi, hZisub, hci, hciratio, hmass, hboundary, hdom, hsym,
        hmeas, hint, hmean, hKsym, hKG, hcentered, hraw, hIH, hHK, _⟩
    refine ⟨hZi, hZisub, hci, hciratio, hmass, ?_, hdom, hsym, hmeas,
      hint, hmean, hKsym, ?_, ?_, hraw, hIH, hHK⟩
    · simpa only [Crow] using hboundary
    · simpa only [Crow, U] using hKG
    · simpa only [Crow, U] using hcentered
  have hmajorOrder : ∀ i ∈
      ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
        Finset ((_ : ℤ) × (Fin d → ℤ))),
      (1 : FullBlockMat d) ≤ toFullBlockMat
          (normalizedBlock
            (adaptedMean P (roundedGrid jStar mu') i.1)
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ∧
        toFullBlockMat
            (normalizedBlock
              (adaptedMean P (roundedGrid jStar mu') i.1)
              (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ≤
          toFullBlockMat
            (normalizedBlock (Kmajor i)
              (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) := by
    intro i hi
    rcases hmajor i hi with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hIH, hHK, _⟩
    exact ⟨hIH, hHK⟩
  have hmajorGap : ∀ i ∈
      ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
        Finset ((_ : ℤ) × (Fin d → ℤ))),
      gapG (Q : ℝ)
          (normalizedBlock (Kmajor i)
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ≤
        A * (row i.1 + 3 * eta + src i.1) := by
    intro i hi
    rcases hmajor i hi with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hgap⟩
    exact hgap
  have hhold0 : ∀ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
      0 ≤ hold r := by
    intro r hr
    obtain ⟨hr0, hrt⟩ := Finset.mem_Ico.mp hr
    exact zero_le_frakH hQ0
      (hIP hr0 hrt.le)
  have hrow0 : ∀ j ∈ Finset.Icc jStar (u + (l0 : ℤ)), 0 ≤ row j := by
    intro j hj
    obtain ⟨hj0, hjn'⟩ := Finset.mem_Icc.mp hj
    simp only [row]
    exact add_nonneg
      (zero_le_frakH hQ0 (hIP hj0 (hjn'.trans hnt)))
      (mul_nonneg hCrow0 (Finset.sum_nonneg fun r hr =>
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hhold0 r
          (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hr).1,
            (Finset.mem_Ico.mp hr).2.trans_le (hjn'.trans hnt)⟩))))
  have hsrc0 : ∀ j : ℤ, 0 ≤ src j := by
    intro j
    exact add_nonneg (heps0 j) (Real.rpow_nonneg (heps0 j) (Q : ℝ))
  have hrowWeighted :
      ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) * row j ≤
        (1 + Crow *
            ((3 : ℝ) ^ (-(1 - g - a)) /
              (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
          (3 : ℝ) ^ (a * (l0 : ℝ)) *
            (∑ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
              (3 : ℝ) ^
                  (-a * (((u + 2 * (l0 : ℤ) : ℤ) : ℝ) - 1 - (r : ℝ))) *
                hold r) := by
    have hcoef :
        ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
            (3 : ℝ) ^
                (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                  (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) * row j ≤
          ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
            (3 : ℝ) ^
                (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) * row j := by
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right
          (power_weight_le_row_weight hg0 hQ0 halo hadef
            (by exact_mod_cast (Finset.mem_Icc.mp hj).2)) (hrow0 j hj)
    refine hcoef.trans (unshifted_nonlinear_rows_le hahi hCrow0
      (by omega : u + 2 * (l0 : ℤ) = u + (l0 : ℤ) + (l0 : ℤ)) hl0z
      hhold0 ?_)
    intro j hj
    exact le_rfl
  have hbetaPos : 0 < (Q : ℝ) * rhoMax - (d : ℝ) := by
    rw [show (Q : ℝ) * rhoMax - (d : ℝ) = a + (Q : ℝ) * g by
      rw [hadef]
      ring]
    exact add_pos_of_pos_of_nonneg halo (mul_nonneg hQ0 hg0)
  have hbetaDen : 0 < 1 - (3 : ℝ) ^
      (-((Q : ℝ) * rhoMax - (d : ℝ))) := by
    have hneg : -((Q : ℝ) * rhoMax - (d : ℝ)) < 0 := neg_neg_of_pos hbetaPos
    have hlt : (3 : ℝ) ^ (-((Q : ℝ) * rhoMax - (d : ℝ))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
    linarith only [hlt]
  have hbetaGeom0 : 0 ≤ 1 / (1 - (3 : ℝ) ^
      (-((Q : ℝ) * rhoMax - (d : ℝ)))) := by
    positivity
  have hbridgeWeighted :
      ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
            (3 * eta) ≤
        6 * (1 / (1 - (3 : ℝ) ^
          (-((Q : ℝ) * rhoMax - (d : ℝ))))) * etaX := by
    have hgeom := bridge_error_centered hg0 hQ0 halo hadef heta0' jStar
      (u + (l0 : ℤ))
    have hmul := mul_le_mul_of_nonneg_left hgeom (by norm_num : (0 : ℝ) ≤ 3)
    calc
      ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) * (3 * eta)
          = 3 * ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
              (3 : ℝ) ^
                  (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                    (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) * eta := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ 3 * (1 / (1 - (3 : ℝ) ^
            (-((Q : ℝ) * rhoMax - (d : ℝ)))) * eta) := hmul
      _ ≤ 6 * (1 / (1 - (3 : ℝ) ^
            (-((Q : ℝ) * rhoMax - (d : ℝ))))) * etaX := by
          have h := mul_le_mul_of_nonneg_left heta2 hbetaGeom0
          ring_nf at h ⊢
          linarith only [h]
  have hcontEps : ∀ j : ℤ, jStar + (0 : ℤ) ≤ j →
      eps j ≤ Dcont *
        (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (jStar : ℝ))) := by
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (zpow_le_rpow_boundary_rate hg0 (by omega : jStar ≤ j)) hDcont0
  have hsourceRows :
      ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) * src j ≤
        ((3 : ℝ) ^ a *
          (1 / (1 - (3 : ℝ) ^ (-a)) +
            1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
            1 / (1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a))))) *
          ((Dsrc + Dsrc ^ (Q : ℝ)) *
            (3 : ℝ) ^
              (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - (jStar : ℝ)))) := by
    simpa only [src, Int.cast_zero, mul_zero, Real.rpow_zero, mul_one] using
      source_rows_le halo hahi hQ1 hDcont0 hDsrc0 hDcontSrc le_rfl heps0
        (by omega : (0 : ℤ) ≤ 0)
        (fun j hj hj' => by omega) hcontEps (u + (l0 : ℤ))
        (Finset.Icc jStar (u + (l0 : ℤ)))
        (fun j hj => (Finset.mem_Icc.mp hj).1)
  have hsourceCoef :
      ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) * src j ≤
        ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-a * (((u + (l0 : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ))) * src j := by
    exact Finset.sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_right
        (power_weight_le_row_weight hg0 hQ0 halo hadef
          (by exact_mod_cast (Finset.mem_Icc.mp hj).2)) (hsrc0 j)
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
  have hCsrc0 : 0 ≤ (3 : ℝ) ^ a *
      (1 / (1 - (3 : ℝ) ^ (-a)) +
        1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
        1 / (1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a)))) := by
    have hneg0 : -a < 0 := neg_neg_of_pos halo
    have hden0 : 0 < 1 - (3 : ℝ) ^ (-a) := by
      have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
        (by norm_num) hneg0
      linarith only [hlt]
    have hpos1 : 0 < 1 - g - a := by linarith only [hahi]
    have hneg1 : -(1 - g - a) < 0 := neg_neg_of_pos hpos1
    have hden1 : 0 < 1 - (3 : ℝ) ^ (-(1 - g - a)) := by
      have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
        (by norm_num) hneg1
      linarith only [hlt]
    have hOneg : 0 < 1 - g := by linarith only [hg1]
    have hmulQ : 1 - g ≤ (Q : ℝ) * (1 - g) :=
      (le_mul_iff_one_le_left hOneg).2 hQ1
    have hrate : 0 < (Q : ℝ) * (1 - g) - a := by
      linarith only [hahi, hmulQ]
    have hneg2 : -((Q : ℝ) * (1 - g) - a) < 0 := neg_neg_of_pos hrate
    have hden2 : 0 < 1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a)) := by
      have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
        (by norm_num) hneg2
      linarith only [hlt]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) a)
      (add_nonneg
        (add_nonneg (one_div_nonneg.mpr hden0.le) (one_div_nonneg.mpr hden1.le))
        (one_div_nonneg.mpr hden2.le))
  have hsourceWeighted :
      ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) * src j ≤
        ((3 : ℝ) ^ a *
          (1 / (1 - (3 : ℝ) ^ (-a)) +
            1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
            1 / (1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a))))) *
          (Lam ^ (Q : ℝ) *
            transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
              (u + (l0 : ℤ))) :=
    hsourceCoef.trans (hsourceRows.trans
      (mul_le_mul_of_nonneg_left hrem hCsrc0))
  have hlevels :
      ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
          (3 : ℝ) ^
              (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
            (row j + 3 * eta + src j) ≤
        ((1 + Crow *
            ((3 : ℝ) ^ (-(1 - g - a)) /
              (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
            (3 : ℝ) ^ (a * (l0 : ℝ)) *
              ∑ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
                (3 : ℝ) ^
                    (-a * (((u + 2 * (l0 : ℤ) : ℤ) : ℝ) - 1 - (r : ℝ))) *
                  hold r +
          6 * (1 / (1 - (3 : ℝ) ^
            (-((Q : ℝ) * rhoMax - (d : ℝ))))) * etaX +
          ((3 : ℝ) ^ a *
            (1 / (1 - (3 : ℝ) ^ (-a)) +
              1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
              1 / (1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a))))) *
            (Lam ^ (Q : ℝ) *
              transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                (u + (l0 : ℤ)))) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hsum := add_le_add (add_le_add hrowWeighted hbridgeWeighted)
      hsourceWeighted
    convert hsum using 1
    ring
  have hcellWeighted :
      ∑ i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))),
          ((3 : ℝ) ^
            (rhoMax * ((i.1 : ℝ) - ((u + (l0 : ℤ) : ℤ) : ℝ)))) ^
              (Q : ℝ) *
            gapG (Q : ℝ)
              (normalizedBlock (Kmajor i)
                (adaptedMean P (roundedGrid jStar mu')
                  (u + (l0 : ℤ)))) ≤
        A * (((1 + Crow *
              ((3 : ℝ) ^ (-(1 - g - a)) /
                (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
              (3 : ℝ) ^ (a * (l0 : ℝ)) *
                ∑ r ∈ Finset.Ico jStar (u + 2 * (l0 : ℤ)),
                  (3 : ℝ) ^
                      (-a * (((u + 2 * (l0 : ℤ) : ℤ) : ℝ) - 1 - (r : ℝ))) *
                    hold r +
            6 * (1 / (1 - (3 : ℝ) ^
              (-((Q : ℝ) * rhoMax - (d : ℝ))))) * etaX +
            ((3 : ℝ) ^ a *
              (1 / (1 - (3 : ℝ) ^ (-a)) +
                1 / (1 - (3 : ℝ) ^ (-(1 - g - a))) +
                1 / (1 - (3 : ℝ) ^ (-((Q : ℝ) * (1 - g) - a))))) *
              (Lam ^ (Q : ℝ) *
                transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                  (u + (l0 : ℤ))))) := by
    have hcells :
        ∑ i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
            Finset ((_ : ℤ) × (Fin d → ℤ))),
            ((3 : ℝ) ^
              (rhoMax * ((i.1 : ℝ) - ((u + (l0 : ℤ) : ℤ) : ℝ)))) ^
                (Q : ℝ) *
              gapG (Q : ℝ)
                (normalizedBlock (Kmajor i)
                  (adaptedMean P (roundedGrid jStar mu')
                    (u + (l0 : ℤ)))) ≤
          ∑ i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
              Finset ((_ : ℤ) × (Fin d → ℤ))),
            ((3 : ℝ) ^
              (rhoMax * ((i.1 : ℝ) - ((u + (l0 : ℤ) : ℤ) : ℝ)))) ^
                (Q : ℝ) * (A * (row i.1 + 3 * eta + src i.1)) := by
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hmajorGap i hi)
          (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num) _) (Q : ℝ))
    refine hcells.trans ?_
    rw [finite_target_weight_sum_eq Z (fun j hj => (hZcard j hj).2)
      (fun j => A * (row j + 3 * eta + src j))]
    have hfactor :
        ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
            (3 : ℝ) ^
                (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                  (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
              (A * (row j + 3 * eta + src j)) =
          A * ∑ j ∈ Finset.Icc jStar (u + (l0 : ℤ)),
            (3 : ℝ) ^
                (-((Q : ℝ) * rhoMax - (d : ℝ)) *
                  (((u + (l0 : ℤ) : ℤ) : ℝ) - (j : ℝ))) *
              (row j + 3 * eta + src j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left hlevels hA0
  refine ⟨Z, hs, Zfill, cfill, Gmajor, Kmajor, hZcard, hZsub, hwt,
    hhistory, hmajorOut, ?_⟩
  dsimp only
  have hsum0 : 0 ≤
      ∑ i ∈ ((Finset.Icc jStar (u + (l0 : ℤ))).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))),
        ((3 : ℝ) ^
          (rhoMax * ((i.1 : ℝ) - ((u + (l0 : ℤ) : ℤ) : ℝ)))) ^
            (Q : ℝ) *
          gapG (Q : ℝ)
            (normalizedBlock (Kmajor i)
              (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) := by
    exact Finset.sum_nonneg fun i hi => mul_nonneg
      (Real.rpow_nonneg (Real.rpow_nonneg (by norm_num) _) (Q : ℝ))
      (zero_le_gapG ((hmajorOrder i hi).1.trans (hmajorOrder i hi).2))
  constructor
  · exact hsum0.trans (by
      simpa only [A, Crow, hold, Lam, mul_assoc] using hcellWeighted)
  · simpa only [A, Crow, hold, Lam, mul_assoc] using hcellWeighted

end

end Transport
end HighContrast
end Homogenization
