/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Geometry.ReferenceAspectRatio
import HCPoly.Provider.Initialization.ReferenceComparison
import HCPoly.Provider.Persistence.AdaptedPersistence
import HCPoly.Provider.Persistence.EuclideanTransfer
import HCPoly.Provider.Persistence.TransferCost

/-!
# The assembly of `p.response.transfer`

Random-source persistence and Euclidean transfer, composed from the persistence
development.  The gap constant is exhibited: the witness is the reference-free
part of the exact cost, `4 + 2log_3^+(6UC_AE C_src/η_min · ζ_g 2^g/(1-g))`, plus
`2(1 + 2A_rad)`, the coefficient the aspect ratio contributes once it has been
divided out of the envelope.  It is a function of the structural data alone, so
it may be, and is, produced before the law.

The composition is clause by clause.  The persistence clause is the adapted
persistence of the selected grid, read at the terminal mean whose finiteness the
window multiplier supplies.  The near-isometry and the Euclidean imbalance are
the Euclidean transfer, applied to the two adapter comparisons the statement
carries as data: the forward one on the strict chain `t - 1 < t < m_ent`, the
reverse one on `m_ent < m_aux < m_aux + 1`, each with its error exponent read as
the gap that defines it, and each congruenced by the entry mean through the
deterministic comparison size.  The two cost bounds are the exact and the
logarithmic transfer cost, whose common envelope needs the terminal
normalization `κ_𝐄 ≤ 6 Π`, the radius bound, and the gauge bound above the
alignment scale.  The factor-three clause is the Euclidean imbalance composed
with the printed hierarchy.

There are no definitions in this file.
-/

open Homogenization Homogenization.HighContrast MeasureTheory in
theorem Homogenization.HighContrast.Persistence.persistence_transfer_assembly
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Cd : ℝ) (hCd : 1 ≤ Cd) (CAE : ℝ) (hCAElo : 0 < CAE)
    (hCAE :
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
        (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ lAl : ℤ, (Homogenization.HighContrast.kZero d : ℤ) ≤ lAl →
          ∀ mAl : Homogenization.Mat d, mAl.PosDef →
            ∀ k n m : ℤ, 0 ≤ k → k < n → n < m →
              Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.blockSub
                    (Homogenization.HighContrast.adaptedMean P
                      (Homogenization.HighContrast.roundedGrid lAl mAl) n)
                    (Homogenization.HighContrast.annealedBlock P
                      (Homogenization.HighContrast.centeredCube d k)))
                  (Homogenization.HighContrast.blockScale
                    (CAE * Homogenization.HighContrast.witnessEccentricity mAl *
                      Homogenization.HighContrast.transferGauge g K k *
                      (3 : ℝ) ^ (-((n : ℝ) - (k : ℝ)))) E) ∧
                (lAl ≤ n →
                  Homogenization.BlockMatLoewnerLE
                    (Homogenization.HighContrast.blockSub
                      (Homogenization.HighContrast.annealedBlock P
                        (Homogenization.HighContrast.centeredCube d m))
                      (Homogenization.HighContrast.adaptedMean P
                        (Homogenization.HighContrast.roundedGrid lAl mAl) n))
                    (Homogenization.HighContrast.blockScale
                      (CAE *
                        Homogenization.HighContrast.witnessEccentricity mAl *
                        Homogenization.HighContrast.transferGauge g K n *
                        (3 : ℝ) ^ (-((m : ℝ) - (n : ℝ)))) E)))
    (U : ℝ) (hU : 1 ≤ U)
    (deltaAd : ℝ) (hdeltaAdLo : 0 ≤ deltaAd) (hdeltaAdHi : deltaAd ≤ 1)
    (etaPlus etaMinus etaIso : ℝ)
    (hetaPlusLo : 0 < etaPlus) (hetaPlusHi : etaPlus < 1)
    (hetaMinusLo : 0 < etaMinus) (hetaMinusHi : etaMinus < 1)
    (hetaIsoLo : 0 < etaIso) (hetaIsoHi : etaIso < 1)
    (hetaPlusIso : etaPlus ≤ etaIso)
    (hetaMinusIso : 1 - etaIso ≤ (1 + deltaAd) ^ (-(d : ℤ)) - etaMinus)
    (Arad : ℝ) (hArad : 0 ≤ Arad) :
    ∃ Cgap : ℝ, 0 < Cgap ∧
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
        (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ,
          Homogenization.HighContrast.IsCoupledWindow d
            (Homogenization.HighContrast.initExpQ d g : ℝ) K jStar M →
          ∀ m0 q : Homogenization.Mat d, m0.PosDef →
            q = Homogenization.HighContrast.roundedGrid jStar m0 →
            ∀ t : ℤ, max jStar 1 ≤ t →
              Homogenization.HighContrast.adaptedCell q t ⊆
                Homogenization.HighContrast.centeredCube d M →
              ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
                Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar
                  M Y →
                ∫ a, Y a ∂P ≤ U →
                -- `e.response.adapted.conclusion`
                Homogenization.HighContrast.blockImbalance
                    (Homogenization.HighContrast.adaptedMean P q t) ≤
                  1 + deltaAd →
                -- the forward and reverse gaps `e.response.transfer.gaps`
                ∀ l ment r maux : ℤ,
                  l =
                    ⌈max 1
                      (max 0
                        (Real.logb 3
                          (Homogenization.HighContrast.transferSizeBar U CAE Cd g
                              K E m0 t / etaPlus)))⌉ →
                  ment = t + l →
                  r =
                    ⌈max 1
                      (max 0
                        (Real.logb 3
                          (Homogenization.HighContrast.transferSizeBar U CAE Cd g
                              K E m0 ment / etaMinus)))⌉ →
                  maux = ment + r →
        -- the persistence of the adapted block above the response scale
        ((∀ u : ℤ, t ≤ u →
            Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.adaptedMean P q u)
                (Homogenization.HighContrast.adaptedMean P q t) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.adaptedMean P q t)
                (Homogenization.HighContrast.blockScale ((1 + deltaAd) ^ d)
                  (Homogenization.HighContrast.adaptedMean P q u))) ∧
          -- `e.response.transfer.block.comparison`
          Homogenization.BlockMatLoewnerLE
            (Homogenization.HighContrast.blockScale (1 - etaIso)
              (Homogenization.HighContrast.adaptedMean P q t))
            (Homogenization.HighContrast.annealedBlock P
              (Homogenization.HighContrast.centeredCube d ment)) ∧
          Homogenization.BlockMatLoewnerLE
            (Homogenization.HighContrast.annealedBlock P
              (Homogenization.HighContrast.centeredCube d ment))
            (Homogenization.HighContrast.blockScale (1 + etaIso)
              (Homogenization.HighContrast.adaptedMean P q t)) ∧
          -- the Euclidean imbalance after the transfer
          Homogenization.HighContrast.blockImbalance
              (Homogenization.HighContrast.annealedBlock P
                (Homogenization.HighContrast.centeredCube d ment)) ≤
            (1 + etaIso) ^ 3 / (1 - etaIso) *
              Homogenization.HighContrast.blockImbalance
                (Homogenization.HighContrast.adaptedMean P q t) ∧
          (1 + etaIso) ^ 3 / (1 - etaIso) *
              Homogenization.HighContrast.blockImbalance
                (Homogenization.HighContrast.adaptedMean P q t) ≤
            (1 + etaIso) ^ 3 / (1 - etaIso) * (1 + deltaAd)) ∧
        -- `e.global.selection.eccentricity`
        (Homogenization.HighContrast.witnessEccentricity m0 ≤
            (2 + Homogenization.HighContrast.aspectRatio E) ^ Arad →
          -- `e.response.transfer.gaps`
          ((l : ℝ) + (r : ℝ) ≤
              4 +
                2 *
                  max 0
                    (Real.logb 3
                      (6 * U * CAE * Cd / min etaPlus etaMinus *
                        Homogenization.HighContrast.aspectRatio E *
                        (2 + Homogenization.HighContrast.aspectRatio E) ^
                          (2 * Arad) *
                        Homogenization.HighContrast.zetaG g *
                        ((2 : ℝ) ^ g / (1 - g)))) ∧
            -- `e.response.transfer.gaps`
            (l : ℝ) + (r : ℝ) ≤
              Cgap *
                Real.logb 3
                  (2 + Homogenization.HighContrast.aspectRatio E))) ∧
        -- the factor-three hierarchy of the transfer and the
        -- factor-three-ready conclusion
        ∀ cStar : ℝ,
          3 * ((1 + etaIso) ^ 3 / (1 - etaIso) * (1 + deltaAd) - 1) ≤ cStar →
          3 *
              (Homogenization.HighContrast.blockImbalance
                  (Homogenization.HighContrast.annealedBlock P
                    (Homogenization.HighContrast.centeredCube d ment)) -
                1) ≤
            cStar
    := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hg0, hg1⟩ := hg
  -- The printed upper halves of the two tolerances and of the adapted
  -- imbalance are recorded; the transfer consumes only their lower halves
  -- together with the two tolerance relations.
  have _hprintedCaps : deltaAd ≤ 1 ∧ etaPlus < 1 ∧ etaMinus < 1 :=
    ⟨hdeltaAdHi, hetaPlusHi, hetaMinusHi⟩
  -- The gap constant: the reference-free part of the exact cost, plus the
  -- coefficient of `log_3(2 + Π)` that the radius exponent contributes.
  refine ⟨4 + 2 * max 0 (Real.logb 3
        (6 * U * CAE * Cd / min etaPlus etaMinus * zetaG g *
          ((2 : ℝ) ^ g / (1 - g)))) + 2 * (1 + 2 * Arad),
    Persistence.zero_lt_gapConst hArad, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar M hwin m0 q hm0 hq t ht hcont Y hY
    hUmean himb l ment r maux hl hment hr hmaux
  haveI := hP
  subst hq
  set q : Mat d := roundedGrid jStar m0
  have hqr : IsRoundedGrid jStar q :=
    Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hwin hm0
  have hjt : jStar ≤ t := le_trans (le_max_left _ _) ht
  have h1t : (1 : ℤ) ≤ t := le_trans (le_max_right _ _) ht
  -- the terminal mean is an expectation, from the window multiplier
  have hfin_t : HasFiniteAdaptedMean P q t :=
    Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hm0 hqr hjt hcont
  -- the persistence of the adapted block above the response scale
  have hpers : ∀ u : ℤ, t ≤ u →
      BlockMatLoewnerLE (adaptedMean P q u) (adaptedMean P q t) ∧
        BlockMatLoewnerLE (adaptedMean P q t)
          (blockScale ((1 + deltaAd) ^ d) (adaptedMean P q u)) := fun u hu =>
    Persistence.adapted_persistence hd hstat hqr hjt hfin_t himb hu
  -- the two adapter chains, and the gap each of them is discounted by
  have hk0 : (kZero d : ℤ) ≤ jStar := le_trans (le_max_left _ _) hwin.1
  have hl1 : (1 : ℤ) ≤ l := hl ▸ Persistence.one_le_gapCeil _
  have hr1 : (1 : ℤ) ≤ r := hr ▸ Persistence.one_le_gapCeil _
  have hecc0 : (0 : ℝ) ≤ witnessEccentricity m0 :=
    (Transport.zero_lt_witnessEccentricity hm0).le
  have hfwd := (hCAE P E Ψ K S hP hstat hunit hdag jStar hk0 m0 hm0 (t - 1) t ment
    (by omega) (by omega) (by omega)).2 hjt
  rw [Persistence.rpow_neg_sub_eq_zpow hment] at hfwd
  have hrev := (hCAE P E Ψ K S hP hstat hunit hdag jStar hk0 m0 hm0 ment maux
    (maux + 1) (by omega) (by omega) (by omega)).1
  rw [Persistence.rpow_neg_sub_eq_zpow hmaux] at hrev
  have hcf : (0 : ℝ) ≤
      CAE * witnessEccentricity m0 * transferGauge g K t * (3 : ℝ) ^ (-l) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCAElo.le hecc0)
      (Persistence.zero_lt_transferGauge hg1 K t).le) (by positivity)
  have hcr : (0 : ℝ) ≤
      CAE * witnessEccentricity m0 * transferGauge g K ment * (3 : ℝ) ^ (-r) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCAElo.le hecc0)
      (Persistence.zero_lt_transferGauge hg1 K ment).le) (by positivity)
  have hgapf := Persistence.transferError_le (by linarith only [hCd]) hg1 hCAElo.le
    hdag.refBlock_isSymm hdag.refBlock_posDef hY hm0 hqr hjt hcont hUmean hetaPlusLo hl
  have hgapr := Persistence.transferError_le (by linarith only [hCd]) hg1 hCAElo.le
    hdag.refBlock_isSymm hdag.refBlock_posDef hY hm0 hqr hjt hcont hUmean hetaMinusLo hr
  -- `e.response.transfer.block.comparison` and
  -- the Euclidean imbalance after the transfer
  obtain ⟨hlower, hupper, hEuclImb⟩ :=
    Persistence.euclidean_transfer hd hstat hdag.refBlock_isSymm hdag.refBlock_posDef hqr hjt
      hfin_t hdeltaAdLo himb (by omega : t ≤ maux) hcf hcr hfwd hrev hgapf hgapr
      hetaIsoLo.le hetaIsoHi hetaPlusIso hetaMinusIso
  have hfac : (0 : ℝ) ≤ (1 + etaIso) ^ 3 / (1 - etaIso) := by
    have hpos : (0 : ℝ) < 1 - etaIso := by linarith only [hetaIsoHi]
    positivity
  have hImb2 :
      (1 + etaIso) ^ 3 / (1 - etaIso) * blockImbalance (adaptedMean P q t) ≤
        (1 + etaIso) ^ 3 / (1 - etaIso) * (1 + deltaAd) :=
    mul_le_mul_of_nonneg_left himb hfac
  -- the structural inputs of the two cost bounds
  have hkap : kappaRef E ≤ 6 * aspectRatio E :=
    Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
  have hPi : (1 : ℝ) ≤ aspectRatio E :=
    one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hgt : transferGauge g K t ≤ (2 : ℝ) ^ g / (1 - g) :=
    Persistence.transferGauge_le hg0 hg1 hdag.one_lt_growthWitness hwin hjt
  have hgm : transferGauge g K ment ≤ (2 : ℝ) ^ g / (1 - g) :=
    Persistence.transferGauge_le hg0 hg1 hdag.one_lt_growthWitness hwin (by omega)
  refine ⟨⟨hpers, hlower, hupper, hEuclImb, hImb2⟩, fun hrad => ⟨?_, ?_⟩, ?_⟩
  · -- `e.response.transfer.gaps`
    exact Persistence.exact_cost (by linarith only [hU]) hCAElo.le (by linarith only [hCd]) hg1
      hkap hPi hecc0 hrad hgt hgm hetaPlusLo hetaMinusLo hl hr
  · -- `e.response.transfer.gaps`
    exact Persistence.logarithmic_cost (by linarith only [hU]) hCAElo (by linarith only [hCd])
      hg1 hkap hPi hecc0 hArad hrad hgt hgm hetaPlusLo hetaMinusLo hl hr
  · -- the factor-three-ready conclusion
    intro cStar hstar
    linarith only [hstar, hEuclImb, hImb2]
