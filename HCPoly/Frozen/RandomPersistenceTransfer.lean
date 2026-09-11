/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.SelectionObjects
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Provider.Persistence.PersistenceTransferAssembly

/-!
# Proposition `p.response.transfer`

Random-source persistence and Euclidean transfer.  Once the terminal annealed
block of a selected adapted grid is balanced, the balance persists at every
later scale of that grid, and two decay gaps — one forward, one reverse —
transfer it to a Euclidean cube, at a total cost logarithmic in the aspect
ratio.

The two gaps are chosen successively and both are deterministic: the forward gap
is read at the terminal scale and the reverse gap at the Euclidean scale the
forward gap produced, and both are read on the deterministic comparison size,
which involves the window multiplier only through its deterministic
normalization constant.  The auxiliary scale the reverse comparison needs is
named but is not returned as an entry scale.

The adapted-to-Euclidean comparison constant enters as data with the two
comparison estimates it names inlined, as the neighbouring constants of the
bridge results do: it is fixed once, valid in both directions and at every
alignment, and a consumer discharges it from the comparison lemma.  The
dimensional constant of the source-control subsection is the same parameter the
window and the source control carry, bound before every constant this statement
produces.

The gap constant is produced before the law.  The exact cost bound is a function
of the structural data alone — the normalization constant, the two comparison
constants, the two tolerances, the radius exponent and the growth exponent — so
once those are fixed the logarithmic bound holds with one constant for every
law, gauge, reference block and aspect ratio.  That is the form the entry
argument cites, and it is why the constant is bound where it is.

The window and its multiplier enter at exactly one place, the terminal
normalization: neither adapted-to-Euclidean comparison, nor the subdivision
monotonicity, nor the persistence conclusion uses them.  This is why the two
gaps may leave the window.

Definedness is neither assumed nor concluded.  The consumer establishes the
finiteness and positive definiteness of the Euclidean block at the entry scale
from the Euclidean mean comparison at that generation, which is available there
because the entry scale is at or above the burn.
-/

theorem HCPoly.Frozen.random_persistence_transfer
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
  exact Homogenization.HighContrast.Persistence.persistence_transfer_assembly
    d hd g hg Cd hCd CAE hCAElo hCAE U hU deltaAd hdeltaAdLo hdeltaAdHi etaPlus
    etaMinus etaIso hetaPlusLo hetaPlusHi hetaMinusLo hetaMinusHi hetaIsoLo
    hetaIsoHi hetaPlusIso hetaMinusIso Arad hArad
