/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.AdaptedWitness
import HCPoly.Provider.Window.PoweredMultiplierTail
import HCPoly.Provider.Window.Successor
import HCPoly.Provider.Window.WindowMultiplierMoment
import HCPoly.Provider.Window.GlobalZero
import HCPoly.Provider.Window.StoppedScale
import HCPoly.Provider.Transport.WindowMomentBound

/-!
# One source multiplier on a bounded window

The strict successor supplies the pathwise improvement and the common stopped
multiplier.  Its almost-sure finiteness closes the standard and adapted cell
rows, while the retained generation factor in its tail gives the full real
moment range of the multiplier.
-/

namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory

open scoped ENNReal MatrixOrder

noncomputable section

/-- The stopped-scale construction satisfies every clause of the bounded
random-source window lemma. -/
theorem random_source_window
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) (Q : ℝ) (hQ : 2 ≤ Q) :
    ∃ Cd₀ : ℝ, 1 ≤ Cd₀ ∧
      ∀ Cd : ℝ, Cd₀ ≤ Cd →
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
        ∀ jStar M : ℤ, IsCoupledWindow d Q K jStar M →
          (∀ (a : CoeffSpace d) (m : ℤ),
              successorScale g E (M - jStar) a ≤ ENNReal.ofReal ((3 : ℝ) ^ m) →
              ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
                standardCellCenter k w ∈ centeredCube d m →
                BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
                  (blockScale
                    ((3 : ℝ) ^
                      (g * max ((m : ℝ) - ((M : ℝ) - (jStar : ℝ)) - (k : ℝ)) 0)) E)) ∧
            (∀ t : ℝ, 1 ≤ t →
              P.real {a : CoeffSpace d |
                ENNReal.ofReal
                    (max ((3 : ℝ) ^ M)
                      (t * growthBar K ^ (4 * (d + 1)) *
                        (3 : ℝ) ^ (M - jStar + 1))) <
                  successorScale g E (M - jStar) a} ≤
                (Ψ t)⁻¹) ∧
            (∀ᵐ a ∂P, successorScale g E (M - jStar) a ≠ ⊤) ∧
            ∃ Y : CoeffSpace d → ℝ,
              IsWindowMultiplier P g E Ψ K Cd jStar M Y ∧
                ENNReal.ofReal (∫ a, Y a ∂P) ≤ lqNorm P Q Y ∧
                lqNorm P Q Y ≤ 2 ∧
                (0 < g →
                  IndependentSums.IsBigOWith P (poweredGauge Ψ g)
                    (fun a => Y a - 1) (poweredRemainderScale d jStar g K)) ∧
                (g = 0 →
                  (∀ᵐ a ∂P, Y a = 1) ∧
                    (∀ᵐ a ∂P, ∀ (k : ℤ) (w : Fin d → ℤ),
                      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a) E ∧
                        BlockMatLoewnerLE (coarseStarInv (standardCell d k w) a)
                          (blockReflect E)) ∧
                    (∀ᵐ a ∂P, ∀ n : Mat d, n.PosDef → ∀ (r : ℤ) (y : Vec d),
                      BlockMatLoewnerLE
                          (coarseBlock (adaptedCellTranslate
                            (roundedGrid jStar n) r y) a)
                          (blockScale (boundaryConst Cd g n) E) ∧
                        BlockMatLoewnerLE
                          (coarseStarInv (adaptedCellTranslate
                            (roundedGrid jStar n) r y) a)
                          (blockScale (boundaryConst Cd g n) (blockReflect E)))) := by
  refine ⟨max 1 (12 * (d : ℝ) * Real.sqrt d), le_max_left _ _, ?_⟩
  intro Cd hCd P E Ψ K S hP hstat hdag jStar M hwindow
  let : IsProbabilityMeasure P := hP
  let : NeZero d := ⟨by omega⟩
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hQone : (1 : ℝ) ≤ Q := one_le_two.trans hQ
  have hfinite := ae_successorScale_ne_top hstat hdag hQone hwindow
  have hstandard := ae_standard_rows_of_successor_ne_top
    (show 0 < d by omega) hg.1 hdag hfinite
  have hadapted := ae_adapted_rows_of_successor_ne_top
    hd hg hwindow hCd hdag hfinite
  have hY : IsWindowMultiplier P g E Ψ K Cd jStar M
      (windowMultiplier g E jStar M) := by
    refine
      { measurable := measurable_windowMultiplier g E hdag.refBlock_isSymm
          hdag.refBlock_posDef jStar M
        one_le := one_le_windowMultiplier hg.1 E jStar M
        standard_primal := ?_
        standard_adjoint := ?_
        adapted_primal := ?_
        adapted_adjoint := ?_
        orlicz := windowMultiplier_isBigOWith hstat hdag hg hQone hwindow
        lp_moment := windowMultiplier_lp_moment hstat hdag hg hQone hwindow }
    · filter_upwards [hstandard] with a ha
      intro k w hcontained
      exact (ha k w hcontained).1
    · filter_upwards [hstandard] with a ha
      intro k w hcontained
      exact (ha k w hcontained).2
    · filter_upwards [hadapted] with a ha
      intro n hn r y hcontained
      exact (ha n hn r y hcontained).1
    · filter_upwards [hadapted] with a ha
      intro n hn r y hcontained
      exact (ha n hn r y hcontained).2
  refine ⟨?_, ?_, hfinite, windowMultiplier g E jStar M, hY,
    Transport.ofReal_integral_le_lqNorm hY hQone, Transport.lqNorm_le_two hQone hwindow hY,
    ?_, ?_⟩
  · intro a m hsuccessor
    exact improved_discount_of_successorScale_le hdag hsuccessor
  · intro t ht
    exact measureReal_successorScale_tail hstat hdag hQone hwindow ht
  · intro hgpos
    exact windowMultiplier_isBigOWith_powered hstat hdag hgpos hQone hwindow
  · intro hgzero
    subst g
    have hglobal := ae_global_response_rows_zero hd hwindow hCd hdag
    refine ⟨_root_.Filter.Eventually.of_forall (windowMultiplier_eq_one E jStar M), ?_, ?_⟩
    · filter_upwards [hglobal] with a ha
      exact ha.1
    · filter_upwards [hglobal] with a ha
      exact ha.2

end

end Window
end HighContrast
end Homogenization
