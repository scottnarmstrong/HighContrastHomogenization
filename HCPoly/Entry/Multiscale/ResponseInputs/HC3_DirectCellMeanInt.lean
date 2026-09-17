import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCellEnt
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCellQuad
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectOscNonneg
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsB3aSub
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCellPair
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCanonAvg
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakSubcellCoeffOn

/-!
# Sample integrability of the two optimizer cell means on an aligned subcell

The cell half of the cutoff-mean row of `p.response.transfer` pairs the deterministic dual variable
with the difference of two doubled optimizer cell means on each aligned subcell of the terminal
cell: the mean of the TERMINAL optimizer and the mean of the SUBCELL maximizer.  Both are needed
coordinatewise in `L^1` of the law.

The subcell maximizer mean is the block response mean of the pathwise coarse block, hence affine
in the entries of that block and integrable by `HasIntegrableCoarseBlock`.  The terminal optimizer
mean is not a functional of the block, but its difference from the subcell mean is controlled
coordinatewise by the Fenchel probe of AK Lemma A.1 read at a single basis direction: the probe
`Y = (0, δ_i)` bounds the `i`-th gradient coordinate by the square root of the `i`-th diagonal
entry of the lower-right sub-block times the square root of twice the subcell deficit, and the
probe `Y = (δ_i, 0)` bounds the `i`-th flux coordinate by the upper-left analogue.  Both envelopes
are integrable, and the terminal mean is measurable in the sample through the canonical selection,
so the terminal mean is integrable as well.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The gradient slot of the block response mean is affine in the entries of the block. -/
private theorem integrable_blockResponseMean_fst {d : ℕ} {α : Type*} [MeasurableSpace α]
    {P : Measure α} [IsFiniteMeasure P] (A : α → BlockMat d) (x : BlockVec d)
    (hA : ∀ κ l : BlockCoord d, Integrable (fun a => blockMatEntry (A a) κ l) P) (i : Fin d) :
    Integrable (fun a => (blockResponseMean (A a) x).1 i) P := by
  have hEq : (fun a => (blockResponseMean (A a) x).1 i)
      = fun a => x.1 i + ((∑ j : Fin d, blockMatEntry (A a) (Sum.inr i) (Sum.inl j) * x.1 j)
          + ∑ j : Fin d, blockMatEntry (A a) (Sum.inr i) (Sum.inr j) * x.2 j) := by
    funext a
    have h1 : (blockResponseMean (A a) x).1 i = x.1 i + (blockMatVecMul (A a) x).2 i := by
      simp only [blockResponseMean, Prod.fst_add, Pi.add_apply, blockMatVecMul_blockSwap_fst]
    rw [h1]
    simp only [blockMatVecMul, Pi.add_apply, matVecMul, blockMatEntry]
  rw [hEq]
  refine (integrable_const _).add (Integrable.add ?_ ?_)
  · exact integrable_finsetSum _ fun j _ => (hA (Sum.inr i) (Sum.inl j)).mul_const _
  · exact integrable_finsetSum _ fun j _ => (hA (Sum.inr i) (Sum.inr j)).mul_const _

/-- The flux slot of the block response mean is affine in the entries of the block. -/
private theorem integrable_blockResponseMean_snd {d : ℕ} {α : Type*} [MeasurableSpace α]
    {P : Measure α} [IsFiniteMeasure P] (A : α → BlockMat d) (x : BlockVec d)
    (hA : ∀ κ l : BlockCoord d, Integrable (fun a => blockMatEntry (A a) κ l) P) (i : Fin d) :
    Integrable (fun a => (blockResponseMean (A a) x).2 i) P := by
  have hEq : (fun a => (blockResponseMean (A a) x).2 i)
      = fun a => x.2 i + ((∑ j : Fin d, blockMatEntry (A a) (Sum.inl i) (Sum.inl j) * x.1 j)
          + ∑ j : Fin d, blockMatEntry (A a) (Sum.inl i) (Sum.inr j) * x.2 j) := by
    funext a
    have h1 : (blockResponseMean (A a) x).2 i = x.2 i + (blockMatVecMul (A a) x).1 i := by
      simp only [blockResponseMean, Prod.snd_add, Pi.add_apply, blockMatVecMul_blockSwap_snd]
    rw [h1]
    simp only [blockMatVecMul, Pi.add_apply, matVecMul, blockMatEntry]
  rw [hEq]
  refine (integrable_const _).add (Integrable.add ?_ ?_)
  · exact integrable_finsetSum _ fun j _ => (hA (Sum.inl i) (Sum.inl j)).mul_const _
  · exact integrable_finsetSum _ fun j _ => (hA (Sum.inl i) (Sum.inr j)).mul_const _

/-- **The subcell maximizer cell mean is integrable, minus sign.**  On an aligned adapted cell the
doubled optimizer cell mean of a response maximizer for the recentred coefficient `a_- = a - g` is
the block response mean of the pathwise coarse block at the load `(-p, r)`, hence affine in the
entries of that block; `HasIntegrableCoarseBlock` on the cell makes every coordinate
`P`-integrable. -/
theorem integrable_cellAverage_subcellOptimizer_respCoeffMinus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ) (p r : Vec d)
    (v : (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffMinus F a) (adaptedCellAtCenter (respGrid jStar F) j w))
    (hv : ∀ a, IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) j w) p r
      (respCoeffMinus F a) (v a))
    (hblk : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
        (optimizerField (respCoeffMinus F a) (v a))).1 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
        (optimizerField (respCoeffMinus F a) (v a))).2 i) P) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hent := integrable_blockMatEntry_respCoeffMinus_adaptedCellAtCenter hq j w F hblk
  have hid : ∀ a : CoeffSpace d,
      cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
          (optimizerField (respCoeffMinus F a) (v a))
        = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
            (respCoeffMinus F a)) (-p, r) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCoeffMinusAt (respGrid jStar F) hq j w F a
    exact cellAverage_optimizerField_adaptedCellAtCenter_eq_blockResponseMean hq j w hEll hae p r
      (v a) (hv a)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · refine (integrable_blockResponseMean_fst
      (fun a => coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)) (-p, r) hent i).congr ?_
    filter_upwards with a
    rw [hid a]
  · refine (integrable_blockResponseMean_snd
      (fun a => coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffMinus F a)) (-p, r) hent i).congr ?_
    filter_upwards with a
    rw [hid a]

/-- **The subcell maximizer cell mean is integrable, plus sign.**  The adjoint twin of
`integrable_cellAverage_subcellOptimizer_respCoeffMinus`, for `a_+ = aᵀ + g`. -/
theorem integrable_cellAverage_subcellOptimizer_respCoeffPlus {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (F : BlockMat d) (hm : (explicitCanonicalMetric F).PosDef) (j : ℤ) (w : Fin d → ℤ) (p r : Vec d)
    (v : (a : CoeffSpace d) →
      AHarmonicFunction (respCoeffPlus F a) (adaptedCellAtCenter (respGrid jStar F) j w))
    (hv : ∀ a, IsResponseMaximizer (adaptedCellAtCenter (respGrid jStar F) j w) p r
      (respCoeffPlus F a) (v a))
    (hblk : HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) j w)) :
    (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
        (optimizerField (respCoeffPlus F a) (v a))).1 i) P)
      ∧ (∀ i : Fin d, Integrable (fun a => (cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
        (optimizerField (respCoeffPlus F a) (v a))).2 i) P) := by
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid hjStar hm
  have hent := integrable_blockMatEntry_respCoeffPlus_adaptedCellAtCenter hq j w F hblk
  have hid : ∀ a : CoeffSpace d,
      cellAverage (adaptedCellAtCenter (respGrid jStar F) j w)
          (optimizerField (respCoeffPlus F a) (v a))
        = blockResponseMean (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
            (respCoeffPlus F a)) (-p, r) := by
    intro a
    obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
      exists_elliptic_representative_respCoeffPlusAt (respGrid jStar F) hq j w F a
    exact cellAverage_optimizerField_adaptedCellAtCenter_eq_blockResponseMean hq j w hEll hae p r
      (v a) (hv a)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · refine (integrable_blockResponseMean_fst
      (fun a => coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)) (-p, r) hent i).congr ?_
    filter_upwards with a
    rw [hid a]
  · refine (integrable_blockResponseMean_snd
      (fun a => coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) j w)
        (respCoeffPlus F a)) (-p, r) hent i).congr ?_
    filter_upwards with a
    rw [hid a]

end

end Homogenization.HighContrast.Multiscale
