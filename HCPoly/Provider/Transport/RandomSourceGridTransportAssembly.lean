/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.GridTransportAssembly
import HCPoly.Provider.Transport.GridTransportCentered

/-!
# Random-source grid transport assembly

The centered and nonlinear transport bounds assemble the frozen proposition.
The declaration below reproduces the frozen statement byte for byte, modulo
its declaration name.
-/

theorem Homogenization.HighContrast.Transport.random_source_grid_transport_assembly
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (Q : ℕ) (hQ : 2 ≤ Q) (hQeven : Even Q)
    (rhoMax : ℝ) (hrhoLo : g < rhoMax) (hrhoHi : rhoMax < 1)
    (a : ℝ) (hadef : a = (Q : ℝ) * (rhoMax - g) - (d : ℝ))
    (halo : 0 < a) (hahi : a < 1 - g)
    (hasum : 0 < ((d : ℝ) + 1) / 2 - g - a / (Q : ℝ))
    (Khop : ℝ) (hKhop : 1 ≤ Khop) :
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
                    (u + 2 * (l0 : ℤ)))
    := by
  apply Homogenization.HighContrast.Transport.random_source_grid_transport_assembly_of_centered_bound
    d hd g hg Q hQ hQeven rhoMax hrhoLo hrhoHi a hadef halo hahi hasum Khop hKhop
  exact Homogenization.HighContrast.Transport.exists_grid_transport_centered_bound
    d hd g hg Q hQ rhoMax a hadef halo hahi Khop hKhop

