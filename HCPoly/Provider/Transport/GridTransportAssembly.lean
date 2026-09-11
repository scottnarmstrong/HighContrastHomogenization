/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.GridTransportNonlinear

/-!
# Assembly of random-source grid transport

This file isolates the sole remaining input to the frozen grid-transport
assembly.  Once the centered-history bound supplies its two uniform constants,
the nonlinear-history bound, definedness, bridge estimates, and conclusion
arithmetic assemble without further hypotheses.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- The frozen random-source grid transport follows from a uniform centered
history bound with independent profile and source constants.  The conclusion
of this theorem is the frozen transport statement; its sole additional premise
is the missing centered half in the form needed by
`transport_conclusion_of_histories`. -/
theorem random_source_grid_transport_assembly_of_centered_bound
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Q : ℕ) (hQ : 2 ≤ Q) (hQeven : Even Q)
    (rhoMax : ℝ) (hrhoLo : g < rhoMax) (hrhoHi : rhoMax < 1)
    (a : ℝ) (hadef : a = (Q : ℝ) * (rhoMax - g) - (d : ℝ))
    (halo : 0 < a) (hahi : a < 1 - g)
    (hasum : 0 < ((d : ℝ) + 1) / 2 - g - a / (Q : ℝ))
    (Khop : ℝ) (hKhop : 1 ≤ Khop)
    (hcentered :
      Even Q →
      g < rhoMax →
      rhoMax < 1 →
      0 < ((d : ℝ) + 1) / 2 - g - a / (Q : ℝ) →
      ∃ Ccen CcenS : ℝ, 0 ≤ Ccen ∧ 0 ≤ CcenS ∧
        ∀ l0 : ℕ, 1 ≤ l0 →
        ∀ Cd : ℝ, 1 ≤ Cd →
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P →
          HCPoly.Frozen.IsUnitRangeLaw P →
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
          centeredHistory P (Q : ℝ) rhoMax (roundedGrid jStar mu') jStar
              (u + (l0 : ℤ)) ≤
            ENNReal.ofReal (Ccen * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
                portableProfile P (Q : ℝ) a rhoMax (roundedGrid jStar mu)
                  jStar rchk (u + 2 * (l0 : ℤ)) +
              ENNReal.ofReal (Ccen * etaX) +
              ENNReal.ofReal
                (CcenS * (3 : ℝ) ^ (a * (l0 : ℝ)) *
                  transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
                    (u + (l0 : ℤ)))) :
    ∃ Ltr : ℕ, 1 ≤ Ltr ∧
      ∃ Ctr : ℝ, 0 < Ctr ∧
        ∀ l0 : ℕ, Ltr ≤ l0 →
        ∀ Cd : ℝ, 1 ≤ Cd →
        ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
          (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
          MeasureTheory.IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P →
          HCPoly.Frozen.IsUnitRangeLaw P →
          HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
          ∀ jStar M : ℤ,
            Homogenization.HighContrast.IsCoupledWindow d Q K jStar M →
            ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
              Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar M
                Y →
              ∀ mu mu' : Homogenization.Mat d, mu.PosDef → mu'.PosDef →
                Homogenization.HighContrast.gridRatio
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (Homogenization.HighContrast.roundedGrid jStar mu') ≤ Khop →
                ∀ rchk u : ℤ, jStar ≤ rchk → rchk ≤ u →
                  -- every cell read lies in the window
                  (∀ r : Homogenization.Mat d,
                    r = Homogenization.HighContrast.roundedGrid jStar mu ∨
                      r = Homogenization.HighContrast.roundedGrid jStar mu' →
                    ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
                      Homogenization.HighContrast.adaptedCell r j ⊆
                        Homogenization.HighContrast.centeredCube d M) →
        -- the annealed blocks of both grids are finite, positive definite,
        -- have finite centered moments, and are ordered
        ((∀ r : Homogenization.Mat d,
            r = Homogenization.HighContrast.roundedGrid jStar mu ∨
              r = Homogenization.HighContrast.roundedGrid jStar mu' →
            ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
              Homogenization.HighContrast.HasFiniteAdaptedMean P r j ∧
                Homogenization.Book.Ch02.BlockPosDef
                  (Homogenization.HighContrast.adaptedMean P r j) ∧
                Homogenization.HighContrast.centeredMoment P (Q : ℝ) r j ≠ ⊤) ∧
          (∀ r : Homogenization.Mat d,
            r = Homogenization.HighContrast.roundedGrid jStar mu ∨
              r = Homogenization.HighContrast.roundedGrid jStar mu' →
            ∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ u + 2 * (l0 : ℤ) →
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.adaptedMean P r T)
                (Homogenization.HighContrast.adaptedMean P r j)) ∧
          -- the transported history, the bridge normalization, the bridge
          -- determinant
          ∀ etaX : ℝ, 0 ≤ etaX → etaX ≤ 1 / 4 →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.blockScale (1 - etaX)
                (Homogenization.HighContrast.adaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mu)
                  (u + 2 * (l0 : ℤ))))
              (Homogenization.HighContrast.adaptedMean P
                (Homogenization.HighContrast.roundedGrid jStar mu')
                (u + (l0 : ℤ))) →
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.adaptedMean P
                (Homogenization.HighContrast.roundedGrid jStar mu')
                (u + (l0 : ℤ)))
              (Homogenization.HighContrast.blockScale (1 + etaX)
                (Homogenization.HighContrast.adaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mu)
                  (u + 2 * (l0 : ℤ)))) →
            (Homogenization.HighContrast.centeredHistory P (Q : ℝ) rhoMax
                  (Homogenization.HighContrast.roundedGrid jStar mu') jStar
                  (u + (l0 : ℤ)) +
                Homogenization.HighContrast.nonlinearHistory P (Q : ℝ) a
                  (Homogenization.HighContrast.roundedGrid jStar mu') jStar
                  (u + (l0 : ℤ)) ≤
              ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
                  Homogenization.HighContrast.portableProfile P (Q : ℝ) a rhoMax
                    (Homogenization.HighContrast.roundedGrid jStar mu) jStar rchk
                    (u + 2 * (l0 : ℤ)) +
                ENNReal.ofReal (Ctr * etaX) +
                ENNReal.ofReal
                  (Ctr * (3 : ℝ) ^ (a * (l0 : ℝ)) *
                    Homogenization.HighContrast.transportSrcRemainder Cd g (Q : ℝ)
                      a E jStar mu mu' (u + (l0 : ℤ)))) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.blockScale (1 + etaX)⁻¹
                  (Homogenization.Book.Ch02.blockIdentity d))
                (Homogenization.HighContrast.bridgeGram
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu')
                    (u + (l0 : ℤ)))) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.bridgeGram
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu')
                    (u + (l0 : ℤ))))
                (Homogenization.HighContrast.blockScale (1 - etaX)⁻¹
                  (Homogenization.Book.Ch02.blockIdentity d)) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.blockScale
                  (1 - etaX / (1 - etaX))
                  (Homogenization.Book.Ch02.blockIdentity d))
                (Homogenization.HighContrast.bridgeGram
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu')
                    (u + (l0 : ℤ)))) ∧
              Homogenization.BlockMatLoewnerLE
                (Homogenization.HighContrast.bridgeGram
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu')
                    (u + (l0 : ℤ))))
                (Homogenization.HighContrast.blockScale
                  (1 + etaX / (1 - etaX))
                  (Homogenization.Book.Ch02.blockIdentity d)) ∧
              (1 - etaX) ^ 2 *
                  Homogenization.HighContrast.adaptedDetRoot P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ)) ≤
                Homogenization.HighContrast.adaptedDetRoot P
                  (Homogenization.HighContrast.roundedGrid jStar mu')
                  (u + (l0 : ℤ)) ∧
              Homogenization.HighContrast.adaptedDetRoot P
                  (Homogenization.HighContrast.roundedGrid jStar mu')
                  (u + (l0 : ℤ)) ≤
                (1 + etaX) ^ 2 *
                  Homogenization.HighContrast.adaptedDetRoot P
                    (Homogenization.HighContrast.roundedGrid jStar mu)
                    (u + 2 * (l0 : ℤ))) := by
  obtain ⟨Ccen, CcenS, hCcen, hCcenS, hcentered⟩ :=
    hcentered hQeven hrhoLo hrhoHi hasum
  obtain ⟨Cnl, CnlS, hCnl, hCnlS, hnonlinear⟩ :=
    exists_grid_transport_nonlinear_bound d hd g hg Q hQ rhoMax a hadef halo hahi
      Khop hKhop
  let Ctr : ℝ := Ccen + Cnl + CcenS + CnlS + 1
  have hCtr0 : 0 < Ctr := by
    dsimp only [Ctr]
    linarith only [hCcen, hCcenS, hCnl, hCnlS]
  have hCtr : Ccen + Cnl ≤ Ctr := by
    dsimp only [Ctr]
    linarith only [hCcenS, hCnlS]
  have hCtrS : CcenS + CnlS ≤ Ctr := by
    dsimp only [Ctr]
    linarith only [hCcen, hCnl]
  refine ⟨1, le_rfl, Ctr, hCtr0, ?_⟩
  intro l0 hl0 Cd hCd P E Ψ K S hPprob hPstat hPunit hced jStar M hw Y hY mu mu'
    hmu hmu' hKgrid rchk u hjr hru hcont
  obtain ⟨hdef, hmono, hbridge⟩ :=
    transport_definedness_and_bridge d hd g Q hQ l0 Cd P E Ψ K S hPprob hPstat
      hced jStar M hw Y hY mu mu' hmu hmu' rchk u hjr hru hcont
  refine ⟨hdef, hmono, fun etaX heta0 heta4 hlo hhi => ?_⟩
  obtain ⟨hgram1, hgram2, hgram3, hgram4, hdet1, hdet2⟩ :=
    hbridge etaX heta0 heta4 hlo hhi
  have hcen := hcentered l0 hl0 Cd hCd P E Ψ K S hPprob hPstat hPunit hced
    jStar M hw Y hY mu mu' hmu hmu' hKgrid rchk u hjr hru hcont etaX heta0 heta4
      hlo hhi
  have hnl := hnonlinear l0 hl0 Cd hCd P E Ψ K S hPprob hPstat hced jStar M hw Y
    hY mu mu' hmu hmu' hKgrid rchk u hjr hru hcont etaX heta0 heta4 hlo hhi
  have hR : 0 ≤ transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu'
      (u + (l0 : ℤ)) := by
    have hD1 : (1 : ℝ) ≤ transportSrcCoeff Cd g E jStar mu mu' :=
      one_le_transportSrcCoeff (le_trans zero_le_one hCd) hg.2 E jStar mu mu'
    have hD0 : (0 : ℝ) ≤ transportSrcCoeff Cd g E jStar mu mu' :=
      le_trans zero_le_one hD1
    rw [transportSrcRemainder]
    exact mul_nonneg
      (add_nonneg hD0 (Real.rpow_nonneg hD0 (Q : ℝ)))
      (Real.rpow_nonneg (by norm_num) _)
  have hhistory := transport_conclusion_of_histories heta0 hR hCcen hCnl hCcenS
    hCnlS hCtr hCtrS hcen hnl
  exact ⟨hhistory, hgram1, hgram2, hgram3, hgram4, hdet1, hdet2⟩

end

end Transport
end HighContrast
end Homogenization
