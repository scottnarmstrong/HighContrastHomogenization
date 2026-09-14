/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.IdentityClause
import HCPoly.Provider.Initialization.IdentityConstant
import HCPoly.Provider.Initialization.Multiplier
import HCPoly.Provider.Initialization.ReferenceComparison
import HCPoly.Provider.Initialization.Structural
import HCPoly.Provider.Initialization.Transport
import HCPoly.Provider.SourceControl.ReferenceIntermediate

/-!
# The assembly of `p.initial.fixed.grid.scale`

Bounded-window random-source initialization, composed from the initialization
development.  The dimensional constant is exhibited: one positive number above
both explicit consumers, the moment coefficient `2 (2d)^{1/Q}(1 + 2d)` of the
Schatten estimates and the logarithmic coefficient `2d(1 + log 24 / log 3)` of
the identity-grid determinant budget.

The composition is clause by clause.  The reference quantities are the printed
intermediate `1 ≤ Θ ≤ Π`, `𝐄_* ≤ 𝐄` and `κ_𝐄 ≤ 1 + 6(Θ - 1) ≤ 6 Π`, read at the
reference block of the coarse ellipticity assumption.  The multiplier display is
the probability-space norm comparison together with the coupled window's moment
bound.  The boundary constant is at least one because its eccentricity and
geometric-series factors are.  The pathwise domination is the primal and adjoint
fields of the window multiplier itself, read at the alignment scale where the
burn discount is one; it is the only clause carrying an exceptional event.  The
deterministic cell conclusions are definedness and positive definiteness from
the window, the two-sided comparison obtained by averaging the pathwise bound
and applying sharp to it, and the raw and centered Schatten estimates in the
mean normalization.  The transport clause compares the two endpoint means
through the reference block and converts the resulting ratio into the
determinant increment.  The identity grid is the same development with the
boundary factor removed, since its cells are standard aligned triadic cubes.

There are no definitions in this file.
-/

theorem Homogenization.HighContrast.Initialization.random_source_adapted_initialization_assembly
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ CdQ : ℝ, 0 < CdQ ∧
      ∀ Cd : ℝ, 1 ≤ Cd →
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
        (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ,
          Homogenization.HighContrast.IsCoupledWindow d
              ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ) K jStar M →
          ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
            Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar M Y →
        -- the reference quantities
        (1 ≤ Homogenization.HighContrast.refContrast E ∧
            Homogenization.HighContrast.refContrast E ≤
              Homogenization.HighContrast.aspectRatio E ∧
            Homogenization.BlockMatLoewnerLE
              (Homogenization.HighContrast.blockSharp E) E ∧
            Homogenization.HighContrast.kappaRef E ≤
              1 + 6 * (Homogenization.HighContrast.refContrast E - 1) ∧
            1 + 6 * (Homogenization.HighContrast.refContrast E - 1) ≤
              6 * Homogenization.HighContrast.aspectRatio E) ∧
        -- the multiplier bound
        (ENNReal.ofReal (∫ a, Y a ∂P) ≤
            Homogenization.HighContrast.lqNorm P
              ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ) Y ∧
            Homogenization.HighContrast.lqNorm P
                ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ) Y ≤ 2) ∧
        -- the boundary constant is at least one
        (∀ mu : Homogenization.Mat d, mu.PosDef →
            1 ≤ Homogenization.HighContrast.boundaryConst Cd g mu) ∧
        -- the pathwise domination, on the single event of the window
        (∀ᵐ a ∂P, ∀ mu : Homogenization.Mat d, mu.PosDef →
            ∀ (r : ℤ) (w : Fin d → ℤ),
              Homogenization.HighContrast.IsAdmissibleIndex
                (Homogenization.HighContrast.roundedGrid jStar mu) jStar M r w →
              Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedResponse
                    (Homogenization.HighContrast.roundedGrid jStar mu) r w a)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.boundaryConst Cd g mu * Y a) E) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.coarseStarInv
                    (Homogenization.HighContrast.adaptedCellAt
                      (Homogenization.HighContrast.roundedGrid jStar mu) r w) a)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.boundaryConst Cd g mu * Y a)
                    (Homogenization.blockReflect E))) ∧
        -- the deterministic cell conclusions
        (∀ mu : Homogenization.Mat d, mu.PosDef → ∀ (r : ℤ) (w : Fin d → ℤ),
            Homogenization.HighContrast.IsAdmissibleIndex
                (Homogenization.HighContrast.roundedGrid jStar mu) jStar M r w →
              Homogenization.HighContrast.HasFiniteAdaptedMean P
                  (Homogenization.HighContrast.roundedGrid jStar mu) r ∧
                Homogenization.Book.Ch02.BlockPosDef
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.boundaryConst Cd g mu * 2)⁻¹
                    (Homogenization.HighContrast.blockSharp E))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.boundaryConst Cd g mu * 2) E) ∧
                Homogenization.HighContrast.lqSchattenSize P
                    ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ)
                    (Homogenization.HighContrast.adaptedResponse
                      (Homogenization.HighContrast.roundedGrid jStar mu) r w)
                    (Homogenization.HighContrast.adaptedMean P
                      (Homogenization.HighContrast.roundedGrid jStar mu) r) ≤
                  ENNReal.ofReal
                    (CdQ * Homogenization.HighContrast.initGridConst Cd g E mu) ∧
                Homogenization.HighContrast.centeredMoment P
                    ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ)
                    (Homogenization.HighContrast.roundedGrid jStar mu) r ≤
                  ENNReal.ofReal
                    (CdQ * Homogenization.HighContrast.initGridConst Cd g E mu)) ∧
        -- the mean transport and the determinant increment
        (∀ mu : Homogenization.Mat d, mu.PosDef → ∀ r T : ℤ, r ≤ T →
            Homogenization.HighContrast.IsAdmissibleIndex
                (Homogenization.HighContrast.roundedGrid jStar mu) jStar M r 0 →
              Homogenization.HighContrast.IsAdmissibleIndex
                (Homogenization.HighContrast.roundedGrid jStar mu) jStar M T 0 →
              Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) T)
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.initGridConst Cd g E mu)
                    (Homogenization.HighContrast.adaptedMean P
                      (Homogenization.HighContrast.roundedGrid jStar mu) T)) ∧
                0 ≤ Homogenization.HighContrast.detIncrement P
                  (Homogenization.HighContrast.roundedGrid jStar mu) r T ∧
                Homogenization.HighContrast.detIncrement P
                    (Homogenization.HighContrast.roundedGrid jStar mu) r T ≤
                  2 * (d : ℝ) *
                    Real.log
                      (Homogenization.HighContrast.initGridConst Cd g E mu)) ∧
        -- the identity grid
        (Homogenization.HighContrast.roundedGrid jStar (1 : Homogenization.Mat d) =
              (1 : Homogenization.Mat d) ∧
            1 ≤ Homogenization.HighContrast.initIdentityConst E ∧
            Homogenization.HighContrast.initIdentityConst E ≤
              24 * Homogenization.HighContrast.aspectRatio E ∧
            2 * (d : ℝ) *
                Real.log (Homogenization.HighContrast.initIdentityConst E) ≤
              CdQ * Real.log (2 + Homogenization.HighContrast.aspectRatio E) ∧
            ∀ r T : ℤ, jStar ≤ r → r ≤ T → T ≤ M →
              Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.blockScale (2 : ℝ)⁻¹
                    (Homogenization.HighContrast.blockSharp E))
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r)
                  (Homogenization.HighContrast.blockScale 2 E) ∧
                Homogenization.HighContrast.centeredMoment P
                    ((Homogenization.HighContrast.initExpQ d g : ℕ) : ℝ)
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r ≤
                  ENNReal.ofReal
                    (CdQ * Homogenization.HighContrast.initIdentityConst E) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) T)
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r) ∧
                Homogenization.BlockMatLoewnerLE
                  (Homogenization.HighContrast.adaptedMean P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r)
                  (Homogenization.HighContrast.blockScale
                    (Homogenization.HighContrast.initIdentityConst E)
                    (Homogenization.HighContrast.adaptedMean P
                      (Homogenization.HighContrast.roundedGrid jStar
                        (1 : Homogenization.Mat d)) T)) ∧
                0 ≤ Homogenization.HighContrast.detIncrement P
                  (Homogenization.HighContrast.roundedGrid jStar
                    (1 : Homogenization.Mat d)) r T ∧
                Homogenization.HighContrast.detIncrement P
                    (Homogenization.HighContrast.roundedGrid jStar
                      (1 : Homogenization.Mat d)) r T ≤
                  2 * (d : ℝ) *
                    Real.log (Homogenization.HighContrast.initIdentityConst E))
    := by
  have : NeZero d := ⟨by omega⟩
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨CdQ, hCdQ0, hMoment, hLog⟩ :=
    Homogenization.HighContrast.Initialization.exists_initialization_constant d hd g
  refine ⟨CdQ, hCdQ0, ?_⟩
  intro Cd hCd P E Ψ K S hPprob hstat hdag jStar M hw Y hY
  have := hPprob
  have hE : Homogenization.IsSymmetricBlockMat E := hdag.refBlock_isSymm
  have hEpd : Homogenization.Book.Ch02.BlockPosDef E := hdag.refBlock_posDef
  have hsharp : Homogenization.BlockMatLoewnerLE
      (Homogenization.HighContrast.blockSharp E) E :=
    Homogenization.HighContrast.Initialization.blockMatLoewnerLE_blockSharp_reference hdag
  have hIup : Homogenization.HighContrast.initIdentityConst E ≤
      24 * Homogenization.HighContrast.aspectRatio E :=
    Homogenization.HighContrast.Initialization.initIdentityConst_le
      (Homogenization.HighContrast.Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger
        hdag)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the reference quantities
    exact ⟨Homogenization.HighContrast.Initialization.one_le_refContrast_of_coarseEllipticityDagger
        hdag,
      Homogenization.HighContrast.Initialization.refContrast_le_aspectRatio_of_coarseEllipticityDagger
        hdag,
      hsharp,
      Homogenization.HighContrast.Initialization.kappaRef_le_one_add_six_mul_refContrast_sub_one_of_coarseEllipticityDagger
        hdag,
      Homogenization.HighContrast.Initialization.one_add_six_mul_refContrast_sub_one_le_six_mul_aspectRatio_of_coarseEllipticityDagger
        hdag⟩
  · -- the multiplier bound
    exact Homogenization.HighContrast.Initialization.initialization_multiplier_bounds hg hw hY
  · -- the boundary constant is at least one
    exact fun mu hmu =>
      Homogenization.HighContrast.Initialization.one_le_boundaryConst hCd hg hmu
  · -- the pathwise domination, on the single event of the window
    exact Homogenization.HighContrast.Initialization.ae_adaptedResponse_and_coarseStarInv_le hY
  · -- the deterministic cell conclusions
    intro mu hmu r w hindex
    have hindex0 : Homogenization.HighContrast.IsAdmissibleIndex
        (Homogenization.HighContrast.roundedGrid jStar mu) jStar M r 0 :=
      ⟨hindex.1, by
        rw [Homogenization.HighContrast.PortableHistory.adaptedCellAt_zero]
        exact hindex.2.2, hindex.2.2⟩
    have hstruct :=
      Homogenization.HighContrast.Initialization.finite_and_posDef_of_admissible hw hY hmu hindex
    have hmean :=
      Homogenization.HighContrast.Initialization.adaptedMean_reference_comparison hg hE hEpd hCd
        hw hY hmu hindex0
    have hmom :=
      Homogenization.HighContrast.Initialization.adapted_moment_bounds_of_constant hg hE hEpd
        hsharp hCd hw hY hmu hindex hMoment
    exact ⟨hstruct.1, hstruct.2, hmean.1, hmean.2, hmom.1, hmom.2⟩
  · -- the mean transport and the determinant increment
    intro mu hmu r T hrT hr hT
    exact Homogenization.HighContrast.Initialization.adaptedMean_transport_and_detIncrement hstat
      hg hE hEpd hsharp hCd hw hY hmu hrT hr hT
  · -- the identity grid
    exact Homogenization.HighContrast.Initialization.identity_clause_of_initIdentityConst_le hstat
      hg hdag hw hY hIup hMoment hLog
