import HCPoly.Entry.Annealed.TwoGridTransport

open Homogenization.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace Homogenization.HighContrast.Provider

open MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The literal two-grid transport type, assembled from the ordinary endpoint. -/
theorem two_grid_transport
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ρ : ℝ, ρ ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K S →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
                ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                  ∀ L : ℕ,
                    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)) ∪
                        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)) ⊆
                      HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                    C * ((L : ℝ) +
                        Real.logb 3 ((2 + aspectRatio E) * (‖m‖ * ‖m⁻¹‖))) ≤
                      (n : ℝ) - (jStar : ℝ) →
                    projectiveDistance m mPlus ≤ 1 →
                    C + Real.logb 3 ρ⁻¹ ≤ (L : ℝ) →
                    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                          (n + 2 * (L : ℤ)) ≤
                      (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (L : ℝ)) * ρ →
                    BlockMatLoewnerLE
                        (blockScale (1 - δ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) →
                    BlockMatLoewnerLE
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                        (blockScale (1 + δ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ)))) →
                    profile P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ))
                          (n + (L : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                          (n + (L : ℤ)) ≤
                      C * (δ + ρ) := by
  obtain ⟨C, hC, Csrc, hCsrc, htransport⟩ := Annealed.two_grid_transport_roundedGrid d hd γ hγ
  refine ⟨C, hC, Csrc, hCsrc, ?_⟩
  intro ρ hρ δ hδ P E Ψ K S hP hstat hunit hdag
  let : IsProbabilityMeasure P := hP
  exact htransport ρ hρ δ hδ P E Ψ K S hstat hunit hdag

end Homogenization.HighContrast.Provider
