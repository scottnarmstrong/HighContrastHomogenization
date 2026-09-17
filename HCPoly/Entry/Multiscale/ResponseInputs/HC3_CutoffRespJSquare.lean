import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRespJIntegrable
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffRespJPlus
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportRespJ
import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Entry.Analysis.SchattenIntegrability
import HCPoly.Setup.BlockAlgebra
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Square integrability of the recentred pathwise response

On an adapted cell the pathwise response `J(U_u; a_-(a))` of the recentred coefficient is the
fixed quadratic form `AK.HC (2.15)` of the coarse block `𝐀(U_u; a_-(a))`, and that coarse block is
a deterministic congruence `Gᵀ 𝐀(U_u; a) G` of the coarse block of the sample.  Hence the response
is an affine function of the entries of `𝐀(U_u; a)`, and the square of the response is a finite
combination of products of pairs of those entries.

This file records the two consequences used by the cutoff rows:

* each entry of `𝐀(U_u; ·)` is square integrable as soon as the coarse block lies in every
  Schatten moment `L^N(S_N)`, because the operator norm — and so each entry — is dominated by the
  Schatten norm;
* consequently the square of the pathwise response is `P`-integrable for both recentrings
  `a_- = a - g` and `a_+ = aᵗ + g`, with the Schatten-moment hypothesis discharged from the
  stationary law and the coarse ellipticity assumption.

Paper: `AK.HC (2.15)`, and the bounded-window source estimate for the Schatten moments.
-/

open Homogenization.HighContrast (CoeffSpace blockVecDot_blockMatVecMul_eq_sum coarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

variable {d : ℕ}

/-! ## Entrywise square integrability of the coarse block -/

/-- Each entry of the coarse block is square integrable for the law as soon as the coarse block
lies in every Schatten moment.  The entry is dominated by the operator norm, which the Schatten
norm dominates, so an `L²(S₂)` membership transfers to the entry. -/
private theorem memLp_two_blockMatEntry_of_memLqSchatten
    (P : Measure (CoeffSpace d)) (V : Set (Vec d))
    (hmem : ∀ N : ℝ, 1 ≤ N → MemLqSchatten P N (fun a => coarseBlock V a))
    (α β : BlockCoord d) :
    MemLp (fun a => blockMatEntry (coarseBlock V a) α β) 2 P := by
  have hH := hmem 2 (by norm_num)
  have hsn : MemLp (fun a => absSchattenNorm 2 (coarseBlock V a)) 2 P := by
    simpa only [ENNReal.ofReal_ofNat] using hH.memLp_absSchattenNorm (by norm_num)
  refine MemLp.of_le hsn (hH.measurable α β) ?_
  filter_upwards [hH.symmetric] with a ha
  have hHerm : (toFullBlockMat (coarseBlock V a)).IsHermitian :=
    (Analysis.toFullBlockMat_isHermitian_iff (coarseBlock V a)).2 ha
  have hnn : 0 ≤ absSchattenNorm 2 (coarseBlock V a) :=
    Analysis.absSchattenNorm_nonneg hHerm (by norm_num)
  calc
    ‖blockMatEntry (coarseBlock V a) α β‖
        = |blockMatEntry (coarseBlock V a) α β| := Real.norm_eq_abs _
    _ ≤ blockOpNorm (coarseBlock V a) :=
        MemLqSchatten.abs_blockMatEntry_le_blockOpNorm _ α β
    _ ≤ absSchattenNorm 2 (coarseBlock V a) :=
        Analysis.blockOpNorm_le_absSchattenNorm hHerm (by norm_num)
    _ = ‖absSchattenNorm 2 (coarseBlock V a)‖ := (Real.norm_of_nonneg hnn).symm

/-! ## Square integrability of the pathwise response -/

/-- Square integrability of the pathwise response when its coarse block is a constant congruence
of the sample coarse block.  The response is the block quadratic `AK.HC (2.15)` of the recentred
block, so it is an affine function of the entries of the coarse block; being a finite combination
of square integrable entries it is square integrable, and its square is integrable. -/
private theorem integrable_respJ_sq_of_blockCongr {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (G : BlockMat d) (V : Set (Vec d)) (qq : Mat d) (u : ℤ) (b : CoeffSpace d → CoeffField d)
    (p q' : Vec d)
    (hpath : ∀ a : CoeffSpace d, respJ qq u p q' (b a)
      = (1 / 2 : ℝ) * blockVecDot (-p, q')
          (blockMatVecMul (coarseBlockMatrix V (b a)) (-p, q')) - vecDot p q')
    (hcongr : ∀ a : CoeffSpace d,
      coarseBlockMatrix V (b a) = blockCongr G (coarseBlock V a))
    (hmem : ∀ N : ℝ, 1 ≤ N → MemLqSchatten P N (fun a => coarseBlock V a)) :
    Integrable (fun a => respJ qq u p q' (b a) ^ 2) P := by
  let X : BlockVec d := (-p, q')
  let Y : BlockVec d := blockMatVecMul G X
  let Q : CoeffSpace d → ℝ := fun a =>
    ∑ κ : BlockCoord d, ∑ β : BlockCoord d,
      toFullBlockVec Y κ *
        (blockMatEntry (coarseBlock V a) κ β * toFullBlockVec Y β)
  have hQ : MemLp Q 2 P := by
    dsimp only [Q]
    refine memLp_finsetSum _ (fun κ _ => ?_)
    refine memLp_finsetSum _ (fun β _ => ?_)
    exact ((memLp_two_blockMatEntry_of_memLqSchatten P V hmem κ β).const_mul
      (toFullBlockVec Y κ * toFullBlockVec Y β)).ae_eq
      (Filter.Eventually.of_forall fun a => by ring)
  have hpoint : ∀ a : CoeffSpace d,
      respJ qq u p q' (b a) = (1 / 2 : ℝ) * Q a - vecDot p q' := by
    intro a
    rw [hpath a, hcongr a, blockVecDot_blockCongr, blockVecDot_blockMatVecMul_eq_sum]
  have hres : MemLp (fun a => respJ qq u p q' (b a)) 2 P :=
    ((hQ.const_mul (1 / 2 : ℝ)).sub (memLp_const (vecDot p q'))).ae_eq
      (Filter.Eventually.of_forall fun a => (hpoint a).symm)
  exact hres.integrable_sq

/-- **Square integrability of the recentred pathwise response.**  For the recentred coefficient
`a_- = a - g` of the self-dual splitting, whose coarse block is the fixed shear congruence
`Gᵀ 𝐀(U_u; a) G`, the square of the pathwise response is `P`-integrable as soon as the coarse
block of the sample lies in every Schatten moment.  The response is the block quadratic
`AK.HC (2.15)` of that congruence, hence an affine function of the entries of `𝐀(U_u; ·)`; each
entry is square integrable because it is dominated by the operator norm, which the Schatten norm
dominates. -/
theorem integrable_respJ_sq_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (u : ℤ)
    (hq : IsUnit (respGrid jStar F))
    (hmem : ∀ N : ℝ, 1 ≤ N → MemLqSchatten P N (fun a => coarseBlock (respCell jStar F u) a))
    (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffMinus F a) ^ 2) P :=
  integrable_respJ_sq_of_blockCongr P (respG F) (respCell jStar F u) (respGrid jStar F) u
    (respCoeffMinus F) p q'
    (fun a => respJ_respCoeffMinus_eq (respGrid jStar F) hq u F a p q')
    (fun a => coarseBlockMatrix_respCoeffMinus_eq_blockCongr (respGrid jStar F) hq u F a)
    hmem

/-- **Square integrability of the adjoint recentred pathwise response.**  For the adjoint recentred
coefficient `a_+ = aᵗ + g`, whose coarse block is the fixed congruence `(G·D)ᵀ 𝐀(U_u; a) (G·D)`,
the square of the pathwise response is `P`-integrable as soon as the coarse block of the sample
lies in every Schatten moment.  The proof is the adjoint twin of
`integrable_respJ_sq_respCoeffMinus`. -/
theorem integrable_respJ_sq_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d) (u : ℤ)
    (hq : IsUnit (respGrid jStar F))
    (hmem : ∀ N : ℝ, 1 ≤ N → MemLqSchatten P N (fun a => coarseBlock (respCell jStar F u) a))
    (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffPlus F a) ^ 2) P :=
  integrable_respJ_sq_of_blockCongr P
    (ofFullBlockMat (toFullBlockMat (respG F) * toFullBlockMat (blockD d)))
    (respCell jStar F u) (respGrid jStar F) u (respCoeffPlus F) p q'
    (fun a => respJ_respCoeffPlus_eq (respGrid jStar F) hq u F a p q')
    (fun a => coarseBlockMatrix_respCoeffPlus_eq_blockCongr (respGrid jStar F) hq u F a)
    hmem

/-! ## Discharging the Schatten-moment hypothesis -/

/-- **Square integrability of the recentred pathwise response from the law hypotheses.**  For a
stationary law satisfying the coarse ellipticity assumption, the coarse block of the response cell
lies in every Schatten moment `L^N(S_N)` by the bounded-window source estimate, so
`integrable_respJ_sq_respCoeffMinus` applies and the square of the recentred pathwise response is
`P`-integrable. -/
theorem integrable_respJ_sq_respCoeffMinus_of_dagger {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (u : ℤ) (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffMinus F a) ^ 2) P := by
  have hq : IsUnit (respGrid jStar F) := isUnit_roundedGrid hj hm
  have hmem : ∀ N : ℝ, 1 ≤ N →
      MemLqSchatten P N (fun a => coarseBlock (respCell jStar F u) a) := by
    intro N hN
    have h := memLqSchatten_coarseBlock_adaptedCellTranslate P γ E Ψ K S hstat hdag
      jStar hj (explicitCanonicalMetric F) hm u 0 N hN
    simpa only [respCell, respGrid, adaptedCellTranslate_zero] using h
  exact integrable_respJ_sq_respCoeffMinus P jStar F u hq hmem p q'

/-- **Square integrability of the adjoint recentred pathwise response from the law hypotheses.**
The adjoint twin of `integrable_respJ_sq_respCoeffMinus_of_dagger`: the coarse block of the response
cell lies in every Schatten moment, and `integrable_respJ_sq_respCoeffPlus` applies. -/
theorem integrable_respJ_sq_respCoeffPlus_of_dagger {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (u : ℤ) (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (respCoeffPlus F a) ^ 2) P := by
  have hq : IsUnit (respGrid jStar F) := isUnit_roundedGrid hj hm
  have hmem : ∀ N : ℝ, 1 ≤ N →
      MemLqSchatten P N (fun a => coarseBlock (respCell jStar F u) a) := by
    intro N hN
    have h := memLqSchatten_coarseBlock_adaptedCellTranslate P γ E Ψ K S hstat hdag
      jStar hj (explicitCanonicalMetric F) hm u 0 N hN
    simpa only [respCell, respGrid, adaptedCellTranslate_zero] using h
  exact integrable_respJ_sq_respCoeffPlus P jStar F u hq hmem p q'

end

end Homogenization.HighContrast.Multiscale
