/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup
import HCPoly.Setup.Moments
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Provider.Quenched.QuenchedConvergenceDischarge
import HCPoly.Provider.Quenched.SmallContrastCorrectedEndpointAssembly

/-!
# Quenched convergence of the coarse-grained matrices

Quenched convergence of the subadditive quantities with a random source scale,
above the random radius of `ss.random.dirichlet`.

The conclusion is the quenched block decay `e.random.quenched.row`, carried on
one integer-translation-invariant event of full probability, together with the
deterministic limit block that pins the annealed blocks from both sides, the
polynomial length, and the optimal two-part tail of the random scale at the
exponent `d - 2g`.

The weighted row of the conclusion is the quantity `B_m` of
`e.random.quenched.row`, written out in the vocabulary of the setup layer: the
`ρ`-weighted sum over depths of the largest normalized coarse-block excess over
the standard cells of that depth whose centers lie in the outer cube, restricted
to the event that the source has burned at the outer scale.  The weight exponent
is the printed one, `ρ = (1+3g)/4` of `e.random.orders`, carried literally
rather than as an existential.

The coefficient fields are uniformly elliptic almost everywhere, with ellipticity
constants belonging to the field and entering no estimate;
`e.qualitative.ellipticity` follows from this, and every quantitative object
below — `Π`, the gauge and its growth witness, the limit block, the length, the
tail, and every dimensional constant — is independent of them.
-/

/-- **Quenched convergence of the coarse-grained matrices**: quenched
convergence of the subadditive quantities with a random source scale. -/
theorem HCPoly.Frozen.quenched_convergence_random_source
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ cd : ℝ, 0 < cd ∧
      ∀ g : ℝ, g ∈ Set.Ico (0 : ℝ) 1 →
        ∃ C κ cSrc : ℝ, 1 < C ∧ 0 < κ ∧ 0 < cSrc ∧
          ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
            ∃ Cδ : ℝ, 1 ≤ Cδ ∧
              ∀ (P : MeasureTheory.Measure
                    (Homogenization.HighContrast.CoeffSpace d))
                (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
                MeasureTheory.IsProbabilityMeasure P →
                HCPoly.Frozen.IsStationaryLaw P →
                HCPoly.Frozen.IsUnitRangeLaw P →
                HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
                ∃ (Abar : Homogenization.BlockMat d) (Lpoly : ℝ)
                  (X : Homogenization.HighContrast.CoeffSpace d → ℝ),
                  Homogenization.IsSymmetricBlockMat Abar ∧
                  Homogenization.Book.Ch02.BlockPosDef Abar ∧
                  (∀ m : ℕ,
                    Homogenization.BlockMatLoewnerLE Abar
                      (Homogenization.HighContrast.annealedBlock P
                        (Homogenization.HighContrast.centeredCube d (m : ℤ)))) ∧
                  (∀ m : ℕ,
                    Homogenization.BlockMatLoewnerLE
                      (Homogenization.HighContrast.blockSharp
                        (Homogenization.HighContrast.annealedBlock P
                          (Homogenization.HighContrast.centeredCube d (m : ℤ))))
                      Abar) ∧
                  1 ≤ Lpoly ∧
                  Lpoly ≤
                    (2 + Homogenization.HighContrast.aspectRatio E * K) ^ Cδ ∧
                  Measurable X ∧
                  (∀ a, 1 ≤ X a) ∧
                  (∀ t : ℝ, 1 ≤ t →
                    P.real {a | C * Lpoly * t ≤ X a} ≤
                      Real.exp (-cd * t ^ ((d : ℝ) - 2 * g)) +
                        (Ψ (cSrc * t))⁻¹) ∧
                  ∃ Ωend : Set (Homogenization.HighContrast.CoeffSpace d),
                    MeasurableSet Ωend ∧
                    P.real Ωend = 1 ∧
                    (∀ z : Fin d → ℤ,
                      Homogenization.HighContrast.translateCoeff z ⁻¹' Ωend =
                        Ωend) ∧
                    ∀ a ∈ Ωend, ∀ m : ℤ, X a ≤ (3 : ℝ) ^ m →
                      (if S a ≤ (3 : ℝ) ^ m then
                          ∑' n : ℕ, (3 : ℝ) ^ (-((1 + 3 * g) / 4) * (n : ℝ)) *
                            sSup {r : ℝ | ∃ w : Fin d → ℤ,
                              Homogenization.HighContrast.standardCellCenter
                                  (m - (n : ℤ)) w ∈
                                Homogenization.HighContrast.centeredCube d m ∧
                              r =
                                Homogenization.HighContrast.blockExcess
                                  (Homogenization.HighContrast.coarseBlock
                                    (Homogenization.HighContrast.standardCell d
                                      (m - (n : ℤ)) w) a)
                                  Abar}
                        else 0) ≤ δ * ((3 : ℝ) ^ m / X a) ^ (-κ)
    := by
  exact
    Homogenization.HighContrast.Quenched.quenched_convergence_of_contrast_core
      d hd (endpoint_hcore_body_corrected d hd)
