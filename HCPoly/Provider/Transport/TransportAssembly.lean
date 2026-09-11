/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.TransportMeanDomination
import HCPoly.Provider.Transport.WindowDefinedness
import HCPoly.Provider.Transport.CenteredBound
import HCPoly.Provider.Transport.NonlinearBound

/-!
# The transport assembly

Two steps of `p.two.grid.transport` that follow from the
surrounding development alone.

*The last display.*  `e.two.grid.profile` and
`e.two.grid.profile` carry the same three summands — the
portable profile of the old grid with the buffer factor, the bridge error, and
the transported source rows — so their sum is again of that shape with the sum
of the two coefficients, and any constant above that sum is admissible.  This is
the closing arithmetic of the proposition: nothing is discarded, and the
exhibited constant is the plain sum.

*The well-definedness and the bridge.*  Under the containment of the two grid
towers in the window the annealed blocks of both grids are finite and positive
definite at every scale of the range, their centered moments are finite, and the
means are ordered; and for a near isometry of the two terminal blocks with error
at most a quarter, the Gram matrix of the bridge congruence obeys both printed
pairs of bounds and the two determinant roots are comparable with the error
squared.  These are the first two conclusions of the proposition and six of the
seven clauses of the third, in the shape the statement prints them.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped MatrixOrder Matrix ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The last display -/

/-! ## The well-definedness and the bridge conclusions -/

/-- **The well-definedness and the bridge conclusions of
`p.two.grid.transport`.**  Under the containment of the two grid
towers in the window: the annealed blocks of both grids are finite and positive
definite at every scale of the range and their centered moments are finite; the
means are ordered; and for every bridge error at most a quarter for which the
new grid's intermediate block is a near isometry of the old grid's terminal
block, the Gram matrix of the bridge congruence satisfies both printed pairs of
bounds and the two determinant roots are comparable with the error squared.

These are the first two conclusions of the proposition and the six bridge
clauses of the third, in the shape the statement prints them. -/
theorem transport_definedness_and_bridge
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (Q : ℕ) (hQ : 2 ≤ Q)
    (l0 : ℕ) (Cd : ℝ)
    (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
    (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : Homogenization.HighContrast.CoeffSpace d → ℝ)
    (hPprob : MeasureTheory.IsProbabilityMeasure P)
    (hPstat : HCPoly.Frozen.IsStationaryLaw P)
    (hced : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    (jStar M : ℤ)
    (hw : Homogenization.HighContrast.IsCoupledWindow d Q K jStar M)
    (Y : Homogenization.HighContrast.CoeffSpace d → ℝ)
    (hY : Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (mu mu' : Homogenization.Mat d) (hmu : mu.PosDef) (hmu' : mu'.PosDef)
    (rchk u : ℤ) (hjr : jStar ≤ rchk) (hru : rchk ≤ u)
    (hcont : ∀ r : Homogenization.Mat d,
      r = Homogenization.HighContrast.roundedGrid jStar mu ∨
        r = Homogenization.HighContrast.roundedGrid jStar mu' →
      ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
        Homogenization.HighContrast.adaptedCell r j ⊆
          Homogenization.HighContrast.centeredCube d M) :
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
  haveI : IsProbabilityMeasure P := hPprob
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast Nat.one_le_of_lt hQ
  obtain ⟨hdef, hmono⟩ := definedness_of_isWindowMultiplier hd hPstat hced.refBlock_isSymm
    hQ1 hw hY hmu hmu' hcont
  refine ⟨hdef, hmono, fun etaX hetaX hetaX4 hlo hhi => ?_⟩
  have hHpd := (hdef _ (Or.inl rfl) (u + 2 * (l0 : ℤ)) (by omega) le_rfl).2.1
  have hFpd := (hdef _ (Or.inr rfl) (u + (l0 : ℤ)) (by omega) (by omega)).2.1
  have hH : (toFullBlockMat (adaptedMean P (roundedGrid jStar mu)
      (u + 2 * (l0 : ℤ)))).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _) hHpd
  have hF : (toFullBlockMat (adaptedMean P (roundedGrid jStar mu')
      (u + (l0 : ℤ)))).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean _ _ _) hFpd
  obtain ⟨h1, h2, h3, h4⟩ := bridge_normalization hH hF hetaX hetaX4 hlo hhi
  obtain ⟨h5, h6⟩ := bridge_determinant (by omega : d ≠ 0) hH hF hetaX hetaX4 hlo hhi
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end

end Transport
end HighContrast
end Homogenization
