import HCPoly.Entry.CG.Proofs.ResponseCountableExhaustion
import HCPoly.Entry.CG.Proofs.ResponseSummable
import HCPoly.Entry.CG.Proofs.ResponseFiniteDefect
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Countable subadditivity of the scalar CG response

The proof uses the scalar finite-defect inequality on each finite subtype
subfamily, then lets the finite set tend to the whole countable subtype.  The response
series converges by the summability statement, and the signed finite-defect
term vanishes because the uncovered volume ratio tends to zero.  No response or
coarse matrix is formed on the non-open remainder.
-/

namespace Homogenization.HighContrast.CG

open MeasureTheory Filter
open scoped BigOperators

private theorem pairwiseDisjoint_subtype_finset {d : ℕ} {ι : Type*} {s : Set ι}
    {U : ι → Set (Vec d)} (hdisj : s.PairwiseDisjoint U) (F : Finset s) :
    (F : Set s).PairwiseDisjoint fun i : s => U i.1 := by
  intro i _hi j _hj hij
  exact hdisj i.2 j.2 (fun h => hij (Subtype.ext h))

/-- Countable subadditivity of the scalar response, proved from the integrated
summability and finite-defect statements. -/
theorem responseJ_subadditive_countable_of_isEllipticFieldOn_provider {d : ℕ}
    {ι : Type*} {s : Set ι} (hs : s.Countable) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWopen : IsOpen W) (hWvol : (volume W).toReal ≠ 0)
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (hnull : volume (W \ ⋃ i ∈ s, U i) = 0)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a) (p q : Vec d) :
    ResponseJ W p q a ≤
      ∑' i : s, (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a := by
  classical
  let term : s → ℝ :=
    fun i => (volume (U i.1)).toReal / (volume W).toReal * ResponseJ (U i.1) p q a
  let defect : Finset s → ℝ :=
    fun F =>
      (volume (W \ ⋃ i ∈ F, U i.1)).toReal / (volume W).toReal *
        (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q))
  have htermSummable : Summable term := by
    dsimp [term]
    exact summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn_provider
      hs hopen hsub hdisj hEll p q
  have htermLimit :
      Tendsto (fun F : Finset s => ∑ i ∈ F, term i) atTop
        (nhds (∑' i : s, term i)) := by
    simpa [HasSum] using htermSummable.hasSum
  have hmeas : ∀ i ∈ s, MeasurableSet (U i) :=
    fun i hi => (hopen i hi).measurableSet
  have hremLimit :
      Tendsto
        (fun F : Finset s =>
          (volume (W \ ⋃ i ∈ F, U i.1)).toReal / (volume W).toReal)
        atTop (nhds 0) :=
    tendsto_remainder_volumeRatio_zero hs hWvol hmeas hsub hdisj hnull
  have hdefectLimit : Tendsto defect atTop (nhds 0) := by
    have hmul :=
      hremLimit.mul
        (tendsto_const_nhds :
          Tendsto
            (fun _F : Finset s =>
              lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q))
            atTop
            (nhds (lam⁻¹ * (Lam ^ 2 * vecNormSq p + vecNormSq q))))
    simpa [defect] using hmul
  have hfinite :
      ∀ F : Finset s, ResponseJ W p q a ≤ ∑ i ∈ F, term i + defect F := by
    intro F
    have hopenF : ∀ i ∈ F, IsOpen (U i.1) := fun i _hi => hopen i.1 i.2
    have hsubF : ∀ i ∈ F, U i.1 ⊆ W := fun i _hi => hsub i.1 i.2
    have hdisjF : (F : Set s).PairwiseDisjoint fun i : s => U i.1 :=
      pairwiseDisjoint_subtype_finset hdisj F
    have h :=
      responseJ_le_sum_volumeRatio_mul_responseJ_add_defect_of_isEllipticFieldOn_provider
        (F := F) (W := W) (U := fun i : s => U i.1)
        hWopen hWvol hopenF hsubF hdisjF hEll p q
    simpa [term, defect] using h
  have hrightLimit :
      Tendsto (fun F : Finset s => ∑ i ∈ F, term i + defect F) atTop
        (nhds ((∑' i : s, term i) + 0)) :=
    htermLimit.add hdefectLimit
  have hle :
      ResponseJ W p q a ≤ (∑' i : s, term i) + 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hrightLimit
      (Eventually.of_forall hfinite)
  simpa [term] using hle

end Homogenization.HighContrast.CG
