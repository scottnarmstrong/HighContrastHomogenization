import HCPoly.Entry.Setup.SchattenNorm
import HCPoly.Entry.PositiveGap

/-!
# Lemma `l.fixed.geometry.positive.gap` — positive gap

`l.fixed.geometry.positive.gap`, the paper's Lemma "Positive gap", transcribed from the printed
display.

Reading of the display, stated here so that no divergence is silent:

* `N ≥ 2` is a **real** exponent: unlike `l.fixed.geometry.matrix.averaging` and
  `p.fixed.geometry.parent.child.recurrence`, this display does not say "even", and the printed
  right-hand side uses `(2d)^{1/N}` and `d^{1-1/N}` only.
* "`F` and `G` … random `2d`-by-`2d` matrices in `L^N(S_N)`" is `MemLqSchatten P N F` and
  `MemLqSchatten P N G` — the carrier of `HCPoly/Entry/Setup/SchattenNorm.lean`:
  measurable for the law, almost surely symmetric, `N`-th Schatten moment `P`-integrable. This is
  the one place the manuscript prints the membership, and it is carried here and nowhere else.
* "positive semidefinite" is the Loewner order against the zero block, and "`F ≤ G`" is the
  Loewner order of the display; both are read **almost surely**, as statements about random
  matrices in a probability space.
* `𝔼[F]` and `𝔼[G]` are the entrywise Bochner expectations, written inline: this is exactly the
  reading the pinned `annealedBlock` (`HCPoly/Entry/Setup/Response.lean`) gives the same symbol for the
  coarse response, and the definition layer names the expectation only there. Nothing else is
  needed to state the display, so no new definition is introduced.
* `|𝔼[G]|` is `blockOpNorm` (Mathlib's L2 operator norm, the print's `|·|` near `e.scale.selection.Q.choice`),
  `tr` is `blockTrace`, and the ambient dimension is the standing `d ≥ 2` of `t.polynomial.entry`.
* The law is an arbitrary probability measure on the coefficient space: the display assumes
  nothing about it, so none of the standing assumptions of the manuscript is carried here.

The proof applies `Homogenization.HighContrast.Provider.fixed_geometry_positive_gap` (`HCPoly/Entry/PositiveGap.lean`).
-/

open Homogenization.HighContrast (CoeffSpace blockSub blockTrace)
namespace Homogenization.HighContrast

open MeasureTheory

/-- **Lemma `l.fixed.geometry.positive.gap`**. Let `N ≥ 2` and let
`F` and `G` be positive semidefinite random `2d`-by-`2d` matrices in `L^N(S_N)` with `F ≤ G`.
Then `‖F − 𝔼[F]‖_{L^N(S_N)} ≤ (1+(2d)^{1/N}) ‖G − 𝔼[G]‖_{L^N(S_N)} + 2(1+d^{1−1/N})
|𝔼[G]|^{1−1/N} (tr(𝔼[G] − 𝔼[F]))^{1/N}`. -/
theorem fixed_geometry_positive_gap
    (d : ℕ) (hd : 2 ≤ d)
    (N : ℝ) (hN : 2 ≤ N)
    (P : Measure (CoeffSpace d)) (hP : IsProbabilityMeasure P)
    (F G : CoeffSpace d → BlockMat d)
    (hF : MemLqSchatten P N F) (hG : MemLqSchatten P N G)
    (hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (F a))
    (hGpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (G a))
    (hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (F a) (G a)) :
    lqSchattenNorm P N
        (fun a => blockSub (F a)
          (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (F b) α β ∂P))) ≤
      (1 + (2 * (d : ℝ)) ^ N⁻¹) *
          lqSchattenNorm P N
            (fun a => blockSub (G a)
              (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (G b) α β ∂P))) +
        2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) *
            blockOpNorm
                (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (G b) α β ∂P)) ^
              (1 - N⁻¹) *
            blockTrace
                (blockSub (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (G b) α β ∂P))
                  (ofFullBlockMat (Matrix.of fun α β => ∫ b, blockMatEntry (F b) α β ∂P))) ^
              N⁻¹ := by exact Homogenization.HighContrast.Provider.fixed_geometry_positive_gap d hd N hN P hP F G hF hG hFpos hGpos hFG

end Homogenization.HighContrast
