/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Recurrence.MeanOrder
import HCPoly.Provider.Recurrence.AlignedSubdivision
import HCPoly.Provider.Recurrence.CellMuMeasurability
import HCPoly.Provider.Recurrence.AdaptedCellPositivity

/-!
# Upward integrability of the adapted response

The persistence step of `p.response.transfer` reads the adapted
means `E_u^q` at every scale `u` above the entry scale `t`, and both halves of
the persistence of the adapted block above the response scale are statements
about those means as expectations.  The finiteness guard is available only at
`t`, where the window multiplier supplies it; at a coarser scale the adapted cell
leaves the window and no multiplier bound is available.

The reference argument supplies the missing guard from the subdivision itself.
The aligned subdivision of the coarse block writes the coarse response of the
parent cell `⋄_u^q` below the average of the responses over its `3^{d(u-t)}`
scale-`t` children, and each child is an integer translate of the cell at the
origin, so stationarity makes every child response as integrable as the one at
the origin.  A finite average of integrable responses dominates the parent, and
the domination is entrywise once the quadratic form is read on the basis vectors
and on their pairwise sums: a doubled block whose
diagonal is nonnegative and whose two-vector form is caught between zero and that
of the average has all its entries bounded by twice the average entry scale.

Positive definiteness of the coarser mean is then the pathwise positivity of the
response integrated, which needs the finiteness guard and nothing else.

Nothing here uses the window, the multiplier, or the law beyond stationarity, so
the guard propagates upward from a single scale for as long as the grid is
rounded.
-/

namespace Homogenization
namespace HighContrast
namespace Persistence

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The pathwise entrywise domination -/

/-- **The entries of the parent response are bounded by the children's entry
scale.**  This is `e.fixed.geometry.parent.child` over the aligned
subdivision, read on the basis vectors `e_α` and on the sums `e_α + e_β`, which
are the vectors that control the entries of a symmetric block: the diagonal
comparison bounds `A_{γγ}` by the averaged diagonal, and the two-vector
comparison bounds the off-diagonal entry once the diagonal is known to be
nonnegative. -/
theorem abs_blockMatEntry_coarseBlock_adaptedCell_le_average [NeZero d] {q : Mat d}
    (hq : q.PosDef) {t u : ℤ} (htu : t ≤ u) {Z : Finset (Fin d → ℤ)}
    (hZ : (↑Z : Set (Fin d → ℤ)) =
      {w : Fin d → ℤ | adaptedCellCenter q t w ∈ adaptedCell q u})
    (a : CoeffSpace d) (α β : BlockCoord d) :
    |blockMatEntry (coarseBlock (adaptedCell q u) a) α β| ≤
      2 * ((Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z, blockEntrySum (coarseBlock (adaptedCellAt q t w) a)) := by
  have hc0 : (0 : ℝ) ≤ (Z.card : ℝ)⁻¹ := by positivity
  have hB0 : (0 : ℝ) ≤ (Z.card : ℝ)⁻¹ *
      ∑ w ∈ Z, blockEntrySum (coarseBlock (adaptedCellAt q t w) a) :=
    mul_nonneg hc0 (Finset.sum_nonneg fun w _ => blockEntrySum_nonneg _)
  -- the averaged entry scale dominates every averaged entry
  have hB : ∀ γ δ : BlockCoord d,
      (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, blockMatEntry (coarseBlock (adaptedCellAt q t w) a) γ δ ≤
        (Z.card : ℝ)⁻¹ *
          ∑ w ∈ Z, blockEntrySum (coarseBlock (adaptedCellAt q t w) a) := by
    intro γ δ
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) hc0
    exact le_trans (le_abs_self _) (abs_blockMatEntry_le_blockEntrySum _ γ δ)
  -- the diagonal comparison, on the basis vectors
  have hdiag : ∀ γ : BlockCoord d,
      blockMatEntry (coarseBlock (adaptedCell q u) a) γ γ ≤
        (Z.card : ℝ)⁻¹ *
          ∑ w ∈ Z, blockMatEntry (coarseBlock (adaptedCellAt q t w) a) γ γ := by
    intro γ
    have h := Recurrence.coarseBlock_adaptedCell_le_average hq htu hZ a (blockBasis γ)
    simp only [blockBasis_pairing] at h
    rw [← Finset.mul_sum] at h
    linarith only [h]
  -- the two-vector comparison, on the sums of basis vectors
  have hpair :
      blockMatEntry (coarseBlock (adaptedCell q u) a) α α +
          blockMatEntry (coarseBlock (adaptedCell q u) a) α β +
          blockMatEntry (coarseBlock (adaptedCell q u) a) β α +
          blockMatEntry (coarseBlock (adaptedCell q u) a) β β ≤
        (Z.card : ℝ)⁻¹ *
            ∑ w ∈ Z, blockMatEntry (coarseBlock (adaptedCellAt q t w) a) α α +
          ((Z.card : ℝ)⁻¹ *
            ∑ w ∈ Z, blockMatEntry (coarseBlock (adaptedCellAt q t w) a) α β +
          ((Z.card : ℝ)⁻¹ *
            ∑ w ∈ Z, blockMatEntry (coarseBlock (adaptedCellAt q t w) a) β α +
          (Z.card : ℝ)⁻¹ *
            ∑ w ∈ Z, blockMatEntry (coarseBlock (adaptedCellAt q t w) a) β β)) := by
    have h := Recurrence.coarseBlock_adaptedCell_le_average hq htu hZ a
      (blockBasis α + blockBasis β)
    simp only [blockBasis_sum_pairing] at h
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, mul_add, mul_add, mul_add] at h
    linarith only [h]
  -- the symmetry of the response and the nonnegativity of its diagonal
  have hsymm : blockMatEntry (coarseBlock (adaptedCell q u) a) β α =
      blockMatEntry (coarseBlock (adaptedCell q u) a) α β :=
    isSymmetricBlockMat_coarseBlock (adaptedCell q u) a β α
  have hd0 : ∀ γ : BlockCoord d,
      0 ≤ blockMatEntry (coarseBlock (adaptedCell q u) a) γ γ :=
    zero_le_blockMatEntry_coarseBlock_diag (adaptedCell q u) a
  have hsum0 : 0 ≤ blockMatEntry (coarseBlock (adaptedCell q u) a) α α +
      blockMatEntry (coarseBlock (adaptedCell q u) a) α β +
      blockMatEntry (coarseBlock (adaptedCell q u) a) β α +
      blockMatEntry (coarseBlock (adaptedCell q u) a) β β := by
    have h := zero_le_blockVecDot_coarseBlock_blockBasis_add (adaptedCell q u) a α β
    rwa [blockBasis_sum_pairing] at h
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith only [hsum0, hdiag α, hdiag β, hB α α, hB β β, hB0, hsymm]
  · linarith only [hpair, hd0 α, hd0 β, hB α α, hB α β, hB β α, hB β β, hsymm]

/-! ## The finiteness guard propagates to every coarser scale -/

/-- **The adapted mean is an expectation at every scale above a scale where it
is one.**  This is the integrability step of the persistence argument of
`p.response.transfer`: the coarse response over `⋄_u^q` is
dominated by the average of the responses over its aligned scale-`t` children,
each of which is an integer translate of the cell at the origin and so, by
stationarity, as integrable as the response at `t`. -/
theorem hasFiniteAdaptedMean_of_le [NeZero d] {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q)
    {t : ℤ} (hlt : l ≤ t) (hfin : HasFiniteAdaptedMean P q t) {u : ℤ} (htu : t ≤ u) :
    HasFiniteAdaptedMean P q u := by
  intro α β
  obtain ⟨Z, hZ, -, -, -, -, -⟩ := Recurrence.aligned_subdivision hq hlt htu
  have hchild : ∀ w : Fin d → ℤ, ∀ γ δ : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlock (adaptedCellAt q t w) a) γ δ) P :=
    fun w γ δ => Recurrence.hasIntegrableCoarseBlock_adaptedCellAt hP hq hlt hfin w γ δ
  have hscale : ∀ w : Fin d → ℤ,
      Integrable (fun a => blockEntrySum (coarseBlock (adaptedCellAt q t w) a)) P := by
    intro w
    simp only [blockEntrySum]
    exact integrable_finsetSum _ fun γ _ =>
      integrable_finsetSum _ fun δ _ => (hchild w γ δ).abs
  have hdom : Integrable (fun a => 2 * ((Z.card : ℝ)⁻¹ *
      ∑ w ∈ Z, blockEntrySum (coarseBlock (adaptedCellAt q t w) a))) P :=
    ((integrable_finsetSum Z fun w _ => hscale w).const_mul _).const_mul _
  refine Integrable.mono' hdom
    (Recurrence.hasMeasurableCoarseBlock_adaptedCell_of_isRoundedGrid P hq u α β)
    (_root_.Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs]
  exact abs_blockMatEntry_coarseBlock_adaptedCell_le_average
    (Recurrence.posDef_of_isRoundedGrid hq) htu hZ a α β

end

end Persistence
end HighContrast
end Homogenization
