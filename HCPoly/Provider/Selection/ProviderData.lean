/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Exponents
import HCPoly.Provider.ShortHop.Normalization
import HCPoly.Provider.ShortHop.PrefixScales
import HCPoly.Provider.ShortHop.WindowGuard
import HCPoly.Setup.SelectionObjects

/-!
# Analytic transport data used by the selector

The grid-transport constants are fixed before every tolerance and law-dependent
choice.  This record carries those constants together with the full conclusion
that their provider must discharge; it does not cite a draft theorem.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

noncomputable section

/-- The upward-closed grid-transport constants and their exact analytic
consumer conclusion. -/
structure TransportProviderData (d : ℕ) (g : ℝ) (Q : ℕ) (rhoMax a Khop Ctr : ℝ)
    (Ltr : ℕ) where
  one_le_Ltr : 1 ≤ Ltr
  Ctr_pos : 0 < Ctr
  law : ∀ l0 : ℕ, Ltr ≤ l0 →
    ∀ Cd : ℝ, 1 ≤ Cd →
    ∀ (P : MeasureTheory.Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ),
      MeasureTheory.IsProbabilityMeasure P →
      HCPoly.Frozen.IsStationaryLaw P →
      HCPoly.Frozen.IsUnitRangeLaw P →
      HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
      ∀ jStar M : ℤ, IsCoupledWindow d Q K jStar M →
      ∀ Y : CoeffSpace d → ℝ, IsWindowMultiplier P g E Ψ K Cd jStar M Y →
      ∀ mu mu' : Mat d, mu.PosDef → mu'.PosDef →
        gridRatio (roundedGrid jStar mu) (roundedGrid jStar mu') ≤ Khop →
      ∀ rchk u : ℤ, jStar ≤ rchk → rchk ≤ u →
      (∀ r : Mat d,
        r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
        ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
          adaptedCell r j ⊆ centeredCube d M) →
      ((∀ r : Mat d,
          r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
          ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
            HasFiniteAdaptedMean P r j ∧
              Book.Ch02.BlockPosDef (adaptedMean P r j) ∧
              centeredMoment P (Q : ℝ) r j ≠ ⊤) ∧
        (∀ r : Mat d,
          r = roundedGrid jStar mu ∨ r = roundedGrid jStar mu' →
          ∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ u + 2 * (l0 : ℤ) →
            BlockMatLoewnerLE (adaptedMean P r T) (adaptedMean P r j)) ∧
        ∀ etaX : ℝ, 0 ≤ etaX → etaX ≤ 1 / 4 →
          BlockMatLoewnerLE
            (blockScale (1 - etaX) (adaptedMean P (roundedGrid jStar mu)
              (u + 2 * (l0 : ℤ))))
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))) →
          BlockMatLoewnerLE
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))
            (blockScale (1 + etaX) (adaptedMean P (roundedGrid jStar mu)
              (u + 2 * (l0 : ℤ)))) →
          (centeredHistory P (Q : ℝ) rhoMax (roundedGrid jStar mu') jStar
                (u + (l0 : ℤ)) +
              nonlinearHistory P (Q : ℝ) a (roundedGrid jStar mu') jStar
                (u + (l0 : ℤ)) ≤
            ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
                portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu) jStar
                  rchk (u + 2 * (l0 : ℤ)) +
              ENNReal.ofReal (Ctr * etaX) +
              ENNReal.ofReal
                (Ctr * (3 : ℝ) ^ (a * (l0 : ℝ)) *
                  transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                    (u + (l0 : ℤ)))) ∧
            BlockMatLoewnerLE
              (blockScale (1 + etaX)⁻¹ (Book.Ch02.blockIdentity d))
              (bridgeGram (adaptedMean P (roundedGrid jStar mu)
                (u + 2 * (l0 : ℤ)))
                (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ∧
            BlockMatLoewnerLE
              (bridgeGram (adaptedMean P (roundedGrid jStar mu)
                (u + 2 * (l0 : ℤ)))
                (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))))
              (blockScale (1 - etaX)⁻¹ (Book.Ch02.blockIdentity d)) ∧
            BlockMatLoewnerLE
              (blockScale (1 - etaX / (1 - etaX)) (Book.Ch02.blockIdentity d))
              (bridgeGram (adaptedMean P (roundedGrid jStar mu)
                (u + 2 * (l0 : ℤ)))
                (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))) ∧
            BlockMatLoewnerLE
              (bridgeGram (adaptedMean P (roundedGrid jStar mu)
                (u + 2 * (l0 : ℤ)))
                (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))))
              (blockScale (1 + etaX / (1 - etaX)) (Book.Ch02.blockIdentity d)) ∧
            (1 - etaX) ^ 2 * adaptedDetRoot P (roundedGrid jStar mu)
                (u + 2 * (l0 : ℤ)) ≤
              adaptedDetRoot P (roundedGrid jStar mu') (u + (l0 : ℤ)) ∧
            adaptedDetRoot P (roundedGrid jStar mu') (u + (l0 : ℤ)) ≤
              (1 + etaX) ^ 2 * adaptedDetRoot P (roundedGrid jStar mu)
                (u + 2 * (l0 : ℤ)))

/-- The exact portable-history conclusions at the selected constants. -/
structure PortableProviderData (d Q : ℕ) (a rhoMax Crec : ℝ) (h : ℤ)
    (C0 Csvc : ℝ) (AL : ℤ → ℝ) where
  law : ∀ (P : MeasureTheory.Measure (CoeffSpace d)),
    MeasureTheory.IsProbabilityMeasure P →
    HCPoly.Frozen.IsStationaryLaw P → HCPoly.Frozen.IsUnitRangeLaw P →
    ∀ (l : ℤ) (q : Mat d), IsRoundedGrid l q →
    ∀ jStar b TMax : ℤ, l ≤ jStar → jStar ≤ b → b ≤ TMax →
    (∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j) →
    (∀ j : ℤ, jStar ≤ j → j ≤ TMax → Book.Ch02.BlockPosDef (adaptedMean P q j)) →
    (∀ j : ℤ, jStar ≤ j → j ≤ TMax → centeredMoment P (Q : ℝ) q j ≠ ⊤) →
    (∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ TMax →
        BlockMatLoewnerLE (adaptedMean P q T) (adaptedMean P q j)) ∧
      (∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ TMax → 0 ≤ detIncrement P q j T) ∧
      (∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ TMax →
        BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (relMean P q j T)) ∧
      portableProfile P (Q : ℝ) a rhoMax q jStar b b =
        portableHistory P (Q : ℝ) a rhoMax q jStar b ∧
      (∀ T : ℤ, b ≤ T → T ≤ TMax →
        portableHistory P (Q : ℝ) a rhoMax q jStar T ≤
          ENNReal.ofReal C0 * portableProfile P (Q : ℝ) a rhoMax q jStar b T) ∧
      (∀ T : ℤ, b + h ≤ T → T + h ≤ TMax →
        portableProfile P (Q : ℝ) a rhoMax q jStar b (T + h) ≤
          ENNReal.ofReal (lambdaPort d (Q : ℝ) a Crec h *
              Real.exp ((Q : ℝ) * synchCharge P q h T)) *
            portableProfile P (Q : ℝ) a rhoMax q jStar b T +
          ENNReal.ofReal
            (Csvc * (Real.exp ((Q : ℝ) * synchCharge P q h T) - 1))) ∧
      (∀ (T0 : ℤ) (K : ℕ), b + h ≤ T0 → 1 ≤ K → T0 + (K : ℤ) * h ≤ TMax →
        ∑ k ∈ Finset.range K, synchCharge P q h (T0 + k * h) ≤
          (h : ℝ) * detIncrement P q (T0 + 1 - h) (T0 + K * h)) ∧
      (∀ L T : ℤ, 1 ≤ L → b + h ≤ T → T + L ≤ TMax →
        portableProfile P (Q : ℝ) a rhoMax q jStar b T ≤ 1 →
        portableProfile P (Q : ℝ) a rhoMax q jStar b (T + L) ≤
          ENNReal.ofReal (AL L) * portableProfile P (Q : ℝ) a rhoMax q jStar b T +
          ENNReal.ofReal (AL L * (Real.exp ((Q : ℝ) * detIncrement P q T (T + L)) - 1))) ∧
      ∀ L : ℤ, 1 ≤ L → b + L ≤ TMax →
        portableHistory P (Q : ℝ) a rhoMax q jStar b ≤ 1 →
        portableProfile P (Q : ℝ) a rhoMax q jStar b (b + L) ≤
          ENNReal.ofReal (AL L) * portableHistory P (Q : ℝ) a rhoMax q jStar b +
          ENNReal.ofReal (AL L * (Real.exp ((Q : ℝ) * detIncrement P q b (b + L)) - 1))

/-- The exact short-hop conclusion at the selected thresholds and cutoff. -/
structure ShortHopProviderData (d : ℕ) (g chop etaNew etaX Khop Ctr Cd : ℝ)
    (l0 : ℕ) (tauSrc deltaShort etaPre B : ℝ) where
  law : ∀ (P : MeasureTheory.Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ)
    (K : ℝ) (S : CoeffSpace d → ℝ),
    MeasureTheory.IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
    HCPoly.Frozen.IsUnitRangeLaw P → HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
    ∀ jStar M : ℤ, IsCoupledWindow d (initExpQ d g : ℝ) K jStar M →
    ∀ Y : CoeffSpace d → ℝ, IsWindowMultiplier P g E Ψ K Cd jStar M Y →
    (∀ mp mv : Mat d, mp.PosDef → mv.PosDef →
      ∀ nn l : ℤ, jStar ≤ nn - l →
      Ctr * (1 + Real.log (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))) ≤
          (l : ℝ) →
      Ctr * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
          (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
      (∀ r : Mat d, r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
        ∀ j : ℤ, jStar ≤ j → j ≤ nn + l → adaptedCell r j ⊆ centeredCube d M) →
      BlockMatLoewnerLE
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn - l)))
          (blockScale (bridgeErrUpper Ctr Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) nn)) ∧
        BlockMatLoewnerLE
          (blockScale (-bridgeErrLower Ctr Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) (nn + l)))
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn + l))) ∧
        ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
          BlockMatLoewnerLE
            (blockScale (1 - eta) (adaptedMean P (roundedGrid jStar mp) (nn + l)))
            (adaptedMean P (roundedGrid jStar mv) nn) →
          linearDrift P (initExpRhoDr g) (roundedGrid jStar mv) jStar nn ≤
            Ctr * (eta + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
              (3 : ℝ) ^ (-(l : ℝ)) +
              (1 + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)) *
                (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
                linearDrift P (initExpRhoDr g) (roundedGrid jStar mp) jStar (nn + l) +
              bridgeShiftedRemainder Ctr Cd g (initExpRhoDr g) E jStar mp mv nn l)) →
    ∀ (k : ℕ) (mus : ℕ → Mat d) (ss : ℕ → ℤ) (r0 : ℤ),
      (∀ i : ℕ, i ≤ k → (mus i).PosDef) → mus 0 = 1 →
      (∀ i : ℕ, i < k → projDist (mus i) (mus (i + 1)) ≤ chop) →
      (∀ i : ℕ, i < k → gridRatio (roundedGrid jStar (mus i))
        (roundedGrid jStar (mus (i + 1))) ≤ Khop) →
      r0 ≤ ss 0 → (∀ i : ℕ, i < k → ss i + (l0 : ℤ) ≤ ss (i + 1)) →
      B * Real.logb 3 (2 + aspectRatio E) ≤ (r0 : ℝ) - (jStar : ℝ) →
      ∀ u : ℤ, ss k ≤ u → linearDrift P (initExpRhoDr g)
          (roundedGrid jStar (mus k)) jStar u ≤ etaPre →
        adaptedDetRoot P (roundedGrid jStar (mus k)) u ≤
          (1 + deltaShort) * adaptedDetRoot P (roundedGrid jStar (mus k))
            (u + 2 * (l0 : ℤ)) →
      ∀ mu' : Mat d, mu' = projPathStep chop (mus k)
          (canonicalMetric (adaptedMean P (roundedGrid jStar (mus k))
            (u + 2 * (l0 : ℤ)))) →
        (∀ r : Mat d, r = roundedGrid jStar (mus k) ∨ r = roundedGrid jStar mu' →
          ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
            adaptedCell r j ⊆ centeredCube d M) →
        mu'.PosDef ∧ projDist (mus k) mu' ≤ chop ∧
          gridRatio (roundedGrid jStar (mus k)) (roundedGrid jStar mu') ≤ Khop ∧
          BlockMatLoewnerLE
            (blockScale (1 - etaX) (adaptedMean P (roundedGrid jStar (mus k))
              (u + 2 * (l0 : ℤ))))
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ))) ∧
          BlockMatLoewnerLE
            (adaptedMean P (roundedGrid jStar mu') (u + (l0 : ℤ)))
            (blockScale (1 + etaX) (adaptedMean P (roundedGrid jStar (mus k))
              (u + 2 * (l0 : ℤ)))) ∧
          linearDrift P (initExpRhoDr g) (roundedGrid jStar mu') jStar
            (u + (l0 : ℤ)) ≤ etaNew

/-- Decreasing the determinant and drift thresholds preserves the exact
short-hop conclusion. -/
theorem ShortHopProviderData.shrink {d : ℕ}
    {g chop etaNew etaX Khop Ctr Cd : ℝ} {l0 : ℕ}
    {tauSrc delta0 etaPre0 B deltaShort etaPre : ℝ}
    (raw : ShortHopProviderData d g chop etaNew etaX Khop Ctr Cd l0
      tauSrc delta0 etaPre0 B)
    (hd : 2 ≤ d) (hB : 0 < B) (hdelta : deltaShort ≤ delta0)
    (heta : etaPre ≤ etaPre0) :
    ShortHopProviderData d g chop etaNew etaX Khop Ctr Cd l0
      tauSrc deltaShort etaPre B := by
  refine ⟨?_⟩
  intro P E Ψ K S hprob hstat hunit hdag jStar M hwin Y hY hbridge
    k mus ss r0 hmus hmus0 hjump hratio hr0 hstep hentry u hsku hdrift hdet
    mu' hmu' hcont
  have : MeasureTheory.IsProbabilityMeasure P := hprob
  let : NeZero d := ⟨by omega⟩
  have hmuk : (mus k).PosDef := hmus k le_rfl
  have hjr0 : jStar < r0 := ShortHop.lt_entry_scale hdag hB hentry
  have hss0k : ss 0 + (k : ℤ) * (l0 : ℤ) ≤ ss k := ShortHop.scale_recursion hstep
  have hkl0 : (0 : ℤ) ≤ (k : ℤ) * (l0 : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hju : jStar ≤ u := by linarith only [hjr0, hr0, hss0k, hsku, hkl0]
  have hcontOld : ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
      adaptedCell (roundedGrid jStar (mus k)) j ⊆ centeredCube d M :=
    fun j hj hj2 => hcont _ (Or.inl rfl) j hj hj2
  have hEt : (toFullBlockMat (adaptedMean P (roundedGrid jStar (mus k))
      (u + 2 * (l0 : ℤ)))).PosDef :=
    ShortHop.posDef_adaptedMean_of_window hwin hY hmuk (by omega) le_rfl hcontOld
  have hroot : 0 < adaptedDetRoot P (roundedGrid jStar (mus k))
      (u + 2 * (l0 : ℤ)) := ShortHop.detRoot_pos hEt
  have hcoef : 1 + deltaShort ≤ 1 + delta0 := by linarith only [hdelta]
  have hdet0 : adaptedDetRoot P (roundedGrid jStar (mus k)) u ≤
      (1 + delta0) * adaptedDetRoot P (roundedGrid jStar (mus k))
        (u + 2 * (l0 : ℤ)) := by
    exact hdet.trans (mul_le_mul_of_nonneg_right hcoef hroot.le)
  exact raw.law P E Ψ K S hprob hstat hunit hdag jStar M hwin Y hY hbridge
    k mus ss r0 hmus hmus0 hjump hratio hr0 hstep hentry u hsku
    (hdrift.trans heta) hdet0 mu' hmu' hcont

/-- Enlarging the entry cutoff preserves the exact short-hop conclusion. -/
theorem ShortHopProviderData.enlargeCutoff {d : ℕ}
    {g chop etaNew etaX Khop Ctr Cd : ℝ} {l0 : ℕ}
    {tauSrc deltaShort etaPre B B' : ℝ}
    (raw : ShortHopProviderData d g chop etaNew etaX Khop Ctr Cd l0
      tauSrc deltaShort etaPre B)
    (hd : 2 ≤ d) (hBB' : B ≤ B') :
    ShortHopProviderData d g chop etaNew etaX Khop Ctr Cd l0
      tauSrc deltaShort etaPre B' := by
  refine ⟨?_⟩
  intro P E Ψ K S hprob hstat hunit hdag jStar M hwin Y hY hbridge
    k mus ss r0 hmus hmus0 hjump hratio hr0 hstep hentry u hsku hdrift hdet
    mu' hmu' hcont
  let : NeZero d := ⟨by omega⟩
  have hPi : 1 ≤ aspectRatio E := one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hLam : 0 ≤ Real.logb 3 (2 + aspectRatio E) :=
    le_trans zero_le_one (ShortHop.one_le_logb_two_add_aspectRatio hPi)
  have hentry' : B * Real.logb 3 (2 + aspectRatio E) ≤
      (r0 : ℝ) - (jStar : ℝ) :=
    (mul_le_mul_of_nonneg_right hBB' hLam).trans hentry
  exact raw.law P E Ψ K S hprob hstat hunit hdag jStar M hwin Y hY hbridge
    k mus ss r0 hmus hmus0 hjump hratio hr0 hstep hentry' u hsku hdrift hdet
    mu' hmu' hcont

end

end Selection
end HighContrast
end Homogenization
