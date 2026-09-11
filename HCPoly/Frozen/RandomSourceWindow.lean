/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.SourceObjects
import HCPoly.Provider.Window.WindowAssembly

/-!
# The source multiplier `e.source.multiplier`

One source multiplier on a bounded window.  Unit range of dependence is **not**
assumed: the hypotheses are the random-source data of 02 — stationarity and the
coarse ellipticity assumption with its gauge and source scale — together with a
coupled window pair.

The strict successor of the last bad triadic scale is an explicit quantity of
the data, valued in `ℝ≥0∞` so that "the bad scales are unbounded" reads as the
value `∞` rather than as a real junk value; the conclusion that it is finite
almost surely is then the statement that it is not `∞`.  Below that scale the
coarse ellipticity discount improves to the window height, pathwise and with no
exceptional event.

The multiplier itself is produced with the properties that the source-control
and initialization results bind: it is at least one, it dominates the coarse
response and its sharp adjoint on every standard aligned cube and on every
adapted cell of every deterministic rounded grid at the burn alignment inside
the window — simultaneously, on one event of full measure — and its excess over
one carries the source gauge's weak-Orlicz tail with the resulting moments.

A threshold for the dimensional constant is produced here, and the conclusion
holds at every admissible value above it.  That constant is fixed once for the
source-control subsection, sufficiently large for the filling and Whitney
estimates of the maximal filling; its admissibility condition belongs to that
filling result, so this statement fixes a threshold rather than a value, and the
results that consume it take the value as a parameter.
-/

theorem HCPoly.Frozen.random_source_window
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) (Q : ℝ) (hQ : 2 ≤ Q) :
    ∃ Cd₀ : ℝ, 1 ≤ Cd₀ ∧
      ∀ Cd : ℝ, Cd₀ ≤ Cd →
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
        (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ,
          Homogenization.HighContrast.IsCoupledWindow d Q K jStar M →
          -- the improved discount below the successor scale, pathwise
          (∀ (a : Homogenization.HighContrast.CoeffSpace d) (m : ℤ),
              Homogenization.HighContrast.successorScale g E (M - jStar) a ≤
                ENNReal.ofReal ((3 : ℝ) ^ m) →
              ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
                Homogenization.HighContrast.standardCellCenter k w ∈
                  Homogenization.HighContrast.centeredCube d m →
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.coarseBlock
                    (Homogenization.HighContrast.standardCell d k w) a)
                  (Homogenization.HighContrast.blockScale
                    ((3 : ℝ) ^
                      (g * max ((m : ℝ) - ((M : ℝ) - (jStar : ℝ)) - (k : ℝ)) 0)) E)) ∧
            -- the tail of the successor scale
            (∀ t : ℝ, 1 ≤ t →
              P.real
                  {a : Homogenization.HighContrast.CoeffSpace d |
                    ENNReal.ofReal
                        (max ((3 : ℝ) ^ M)
                          (t * Homogenization.HighContrast.growthBar K ^ (4 * (d + 1)) *
                            (3 : ℝ) ^ (M - jStar + 1))) <
                      Homogenization.HighContrast.successorScale g E (M - jStar) a} ≤
                (Ψ t)⁻¹) ∧
            -- the successor scale is finite almost surely
            (∀ᵐ a ∂P,
              Homogenization.HighContrast.successorScale g E (M - jStar) a ≠ ⊤) ∧
            -- the common multiplier
            ∃ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
              Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar M
                  Y ∧
                ENNReal.ofReal (∫ a, Y a ∂P) ≤
                  Homogenization.HighContrast.lqNorm P Q Y ∧
                Homogenization.HighContrast.lqNorm P Q Y ≤ 2 ∧
                (0 < g →
                  Homogenization.IndependentSums.IsBigOWith P
                    (Homogenization.HighContrast.poweredGauge Ψ g)
                    (fun a => Y a - 1)
                    (Homogenization.HighContrast.poweredRemainderScale d jStar g
                      K)) ∧
                (g = 0 →
                  (∀ᵐ a ∂P, Y a = 1) ∧
                    (∀ᵐ a ∂P, ∀ (k : ℤ) (w : Fin d → ℤ),
                      Homogenization.BlockMatLoewnerLE
                          (Homogenization.HighContrast.coarseBlock
                            (Homogenization.HighContrast.standardCell d k w) a) E ∧
                        Homogenization.BlockMatLoewnerLE
                          (Homogenization.HighContrast.coarseStarInv
                            (Homogenization.HighContrast.standardCell d k w) a)
                          (Homogenization.blockReflect E)) ∧
                    (∀ᵐ a ∂P, ∀ n : Homogenization.Mat d, n.PosDef →
                      ∀ (r : ℤ) (y : Homogenization.Vec d),
                        Homogenization.BlockMatLoewnerLE
                            (Homogenization.HighContrast.coarseBlock
                              (Homogenization.HighContrast.adaptedCellTranslate
                                (Homogenization.HighContrast.roundedGrid jStar n) r
                                y) a)
                            (Homogenization.HighContrast.blockScale
                              (Homogenization.HighContrast.boundaryConst Cd g n)
                              E) ∧
                          Homogenization.BlockMatLoewnerLE
                            (Homogenization.HighContrast.coarseStarInv
                              (Homogenization.HighContrast.adaptedCellTranslate
                                (Homogenization.HighContrast.roundedGrid jStar n) r
                                y) a)
                            (Homogenization.HighContrast.blockScale
                              (Homogenization.HighContrast.boundaryConst Cd g n)
                              (Homogenization.blockReflect E))))
    := by
  exact Homogenization.HighContrast.Window.random_source_window d hd g hg Q hQ
