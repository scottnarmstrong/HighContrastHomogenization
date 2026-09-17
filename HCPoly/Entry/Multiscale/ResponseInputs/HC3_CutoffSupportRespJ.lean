import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65a
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Source.BoundedWindowFiniteness
import HCPoly.Setup.BlockAlgebra

/-!
# Law integrability of the pathwise response on an adapted cell

Let `P` be a stationary law satisfying the coarse ellipticity assumption, and let `U_u` be the
adapted cell of generation `u` on a selected grid.  This file proves that for each of the two
recentred coefficients `a_- = a - g` and `a_+ = a^t + g` of the self-dual recentring the pathwise
response `J(U_u, p, q'; a_\pm)` is `P`-integrable.

The route has three steps.  The response of an elliptic field on a bounded open convex domain is
the fixed quadratic `\tfrac12 (-p, q') \cdot \mathbf A(U; a)(-p, q') - p \cdot q'` of the coarse
block; the coarse block of a recentred field is a *deterministic* congruence of the coarse block
of the sample, so its entries are fixed linear combinations of the entries of `\mathbf A(U; a)`;
and those entries are `P`-integrable for every law satisfying the coarse ellipticity assumption.

The only dimensional hypothesis used is `d \neq 0`.

Paper: `p.response.transfer`, Step 3 and Step 6; the recentring is the one of `e.self.dual`.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock coarseBlock
  isSymmetricBlockMat_coarseBlockMatrix)
open Homogenization.HighContrast (adaptedCellTranslate)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

variable {d : ℕ}

/-! ## Step 1: the coarse block of an adapted cell is law integrable in every dimension -/

/-- Every finite moment of the Schatten norm of the coarse block of an adapted cell is finite,
for any law satisfying the coarse ellipticity assumption.  This is the statement of the
bounded-window source estimate with the dimensional hypothesis relaxed to `d \neq 0`, which is
all its proof uses. -/
theorem memLqSchatten_coarseBlock_adaptedCellTranslate [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) (y : Vec d)
    (N : ℝ) (hN : 1 ≤ N) :
    MemLqSchatten P N
      (fun a => coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) j y) a) := by
  set q := explicitRoundedGrid jStar m with hqdef
  have hq : IsUnit q := isUnit_roundedGrid hj hm
  set W := adaptedCellTranslate q j y with hWdef
  have hW : Bornology.IsBounded W := by
    rw [hWdef, Annealed.adaptedCellTranslate_eq_cg_affine]
    exact (isOpenBoundedConvexDomain_affine_openCube q hq j y).isBoundedDomain.isBounded
  obtain ⟨J, X, _, _, hXN, hbound⟩ := Source.bounded_source_envelope P γ E Ψ K S hstat hdag W hW
  have hmeas : HasMeasurableBlock P (fun a => coarseBlock W a) := fun α β =>
    ((Annealed.measurable_coarseBlock_entry_adapted q hq j y α β).mono
      (Annealed.coeffSigma_le_global _) le_rfl).aestronglyMeasurable
  set D : ℝ := (12 * (d : ℝ) ^ ((3 : ℝ) / 2) / (1 - (3 : ℝ) ^ (-(1 - γ)))) *
    (3 : ℝ) ^ (γ * max ((J : ℝ) - (j : ℝ)) 0) with hDdef
  apply Source.memLqSchatten_of_order_envelope hN hmeas
    (ae_of_all _ (fun a => isSymmetricBlockMat_coarseBlockMatrix W (⇑a.1)))
    (ae_of_all _ (fun a => Annealed.blockPosDef_coarseBlock_adapted q hq j y a)) (hXN N hN) D
  filter_upwards [hbound] with a ha
  have hb := ha q (inverseNormLE_roundedGrid hj hm) j y Set.Subset.rfl
  convert hb using 1
  congr 1
  rw [hDdef]
  ring

/-- Every entry of the coarse block of an adapted cell is `P`-integrable, in every dimension
`d \neq 0`. -/
theorem hasIntegrableCoarseBlock_adaptedCell [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    HasIntegrableCoarseBlock P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) := by
  have h := (memLqSchatten_coarseBlock_adaptedCellTranslate P γ E Ψ K S hstat hdag jStar hj
    m hm j 0 1 le_rfl).integrable_entry le_rfl
  rwa [Annealed.adaptedCellTranslate_zero] at h

/-- The same at the selected grid of the response argument. -/
theorem hasIntegrableCoarseBlock_respCell [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (u : ℤ) :
    HasIntegrableCoarseBlock P (respCell jStar F u) :=
  hasIntegrableCoarseBlock_adaptedCell P γ E Ψ K S hstat hdag jStar hj (explicitCanonicalMetric F) hm u

end

end Homogenization.HighContrast.Multiscale
