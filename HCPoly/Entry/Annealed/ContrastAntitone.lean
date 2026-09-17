import HCPoly.Entry.Analysis.ContrastOrder
import HCPoly.Entry.Annealed.AdaptedIntegrability
import HCPoly.Entry.Annealed.MeanOrder
import HCPoly.Entry.Geometry.EuclideanGrid
import HCPoly.Entry.Geometry.StandardCell
import HCPoly.Entry.Setup.Response

/-!
# Monotonicity of the annealed contrast in the scale

The Euclidean annealed contrast `Θ_m` of `e.Theta.m` is the intrinsic contrast of the
annealed block of the centered cube `□_m`.  Under the standing stationary law the annealed
blocks of the centered cubes decrease in the doubled Loewner order as the scale grows, and
the intrinsic contrast is monotone in that order.  Hence `Θ_m` is nonincreasing in `m` beyond
the rounding scale: a contrast bound at one scale is a contrast bound at every larger scale,
which is the form in which `t.polynomial.entry` is consumed.
-/

open Homogenization.HighContrast (CoeffSpace adaptedMean annealedContrast blockContrast)
namespace Homogenization.HighContrast.Annealed

open MeasureTheory

noncomputable section

/-- Positivity of the flattened doubled matrix is positivity of the doubled quadratic
form. -/
private theorem blockPosDef_of_toFullBlockMat_posDef {d : ℕ} {A : BlockMat d}
    (hA : (toFullBlockMat A).PosDef) : Book.Ch02.BlockPosDef A := by
  intro X hX
  have hvec : toFullBlockVec X ≠ 0 := by
    intro h
    apply hX
    have h' := congrArg ofFullBlockVec h
    rw [ofFullBlockVec_toFullBlockVec] at h'
    simpa using! h'
  have hq := hA.dotProduct_mulVec_pos hvec
  have hstar : star (toFullBlockVec X) = toFullBlockVec X := rfl
  rw [hstar, ← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec] at hq
  exact hq

/-- The Euclidean annealed contrast is the intrinsic contrast of the adapted mean at the
identity metric: the adapted cell of the identity grid is the centered cube. -/
private theorem annealedContrast_eq_blockContrast_adaptedMean {d : ℕ}
    (P : Measure (CoeffSpace d)) (m : ℤ) :
    annealedContrast P m = blockContrast (adaptedMean P (1 : Mat d) m) := by
  rw [annealedContrast, adaptedMean, Geometry.adaptedCell_one,
    ← Geometry.centeredCube_eq_standardCell]

/-- **The annealed contrast is nonincreasing in the scale.**  Under the standing stationary
law, `Θ_k ≤ Θ_j` whenever `j ≤ k` are at least the rounding scale: the annealed block of
`□_k` lies below that of `□_j` in the doubled Loewner order, and the intrinsic contrast
of `e.Theta.m` is monotone in that order. -/
theorem annealedContrast_antitone (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (j k : ℤ)
    (hj : (jStar : ℤ) ≤ j) (hjk : j ≤ k) :
    annealedContrast P k ≤ annealedContrast P j := by
  let : NeZero d := ⟨by omega⟩
  have hle : BlockMatLoewnerLE (adaptedMean P (1 : Mat d) k) (adaptedMean P (1 : Mat d) j) := by
    simpa [Geometry.explicitRoundedGrid_one (d := d) jStar] using
      adaptedMean_antitone d hd P γ E Ψ K S hstat hdag jStar hjStar
        (1 : Mat d) (Geometry.one_posDef d) j k hj hjk
  have hpos : Book.Ch02.BlockPosDef (adaptedMean P (1 : Mat d) k) := by
    have h := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) k
    rw [Geometry.explicitRoundedGrid_one] at h
    exact blockPosDef_of_toFullBlockMat_posDef h
  rw [annealedContrast_eq_blockContrast_adaptedMean, annealedContrast_eq_blockContrast_adaptedMean]
  exact blockContrast_le_of_blockMatLoewnerLE (isSymmetricBlockMat_annealedBlock P _) hpos
    (isSymmetricBlockMat_annealedBlock P _) hle

end

end Homogenization.HighContrast.Annealed
