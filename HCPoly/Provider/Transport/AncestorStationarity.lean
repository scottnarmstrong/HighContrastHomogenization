/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationSup

/-!
# The stationarity comparison on an ancestor cell

The inherited half of the grid transport does not restart the history: every
selected source of a scale at or below the checkpoint is grouped by the aligned
scale-`b` cell that contains it, and the whole history that group carries is
read off the single statistic

`X_B = sup_{j_* ≤ r ≤ b} 3^{-ρ_max(b-r)} max_{y ∈ 3^r 𝕃_q ∩ B, y + ⋄_r^q ⊆ B}
        |(E_b^q)^{-1/2}(𝐀(y + ⋄_r^q) - E_r^q)(E_b^q)^{-1/2}|`

attached to the ancestor `B`.  This file proves the sentence the printed proof
spends on it, `E[X_B^Q] ≤ 𝓗_q^cen(b)`.

The mechanism is the one the fixed-grid majorization already uses.  An aligned
scale-`b` cell is an *integer* translate of the cell at the origin — that is the
alignment clause of the rounded grid — and the aligned scale-`r` cells inside it
are, index for index, the aligned scale-`r` cells inside `⋄_b^q` moved by the
same translation: the residual index of `w` is `w - 3^{b-r} v_B`, and the two
centers differ by the center of the ancestor.  Since the translation is integral
it does not move the law, so the whole statistic transports, and the transported
supremum is the integrand of `e.scale.selection.fluctuation.history` at the
checkpoint.

Nothing is discarded except the containment constraint: the printed index set of
`X_B` is `{y ∈ 3^r 𝕃_q ∩ B : y + ⋄_r^q ⊆ B}`, which is exactly the set of
aligned cells contained in `B` because a cell contains its own center.  The
comparison is proved first for the larger index set — the centers in `B`, with
no containment demanded — and the printed statistic is the corollary.  Both
forms are recorded because the grouping step of the transport produces the
containment form while the majorization consumes the membership form.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix ENNReal

noncomputable section

section Ancestor

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar : ℤ}

/-! ## The residual index inside an ancestor -/

/-- **The center of an aligned cell splits along its ancestor.**  For scales
`r ≤ b` the scale-`r` center at the index `w` is the center of the aligned
scale-`b` cell at `v_B` translated by the scale-`r` center at the residual index
`w - 3^{b-r}v_B`.  This is the index bookkeeping of the grouping by ancestors. -/
theorem adaptedCellCenter_sub_ancestor (q : Mat d) {r b : ℤ} (hrb : r ≤ b)
    (w vB : Fin d → ℤ) :
    adaptedCellCenter q r w =
      adaptedCellCenter q b vB +
        adaptedCellCenter q r fun i => w i - (3 : ℤ) ^ (b - r).toNat * vB i := by
  refine PortableHistory.adaptedCellCenter_split q hrb fun i => ?_
  show w i = w i - (3 : ℤ) ^ (b - r).toNat * vB i + (3 : ℤ) ^ (b - r).toNat * vB i
  ring

/-- **The residual center sits in the cell at the origin.**  If the scale-`r`
center at `w` lies in the aligned scale-`b` cell at `v_B`, then the residual
center lies in `⋄_b^q`: the ancestor and the cell at the origin differ by the
translation the split records. -/
theorem adaptedCellCenter_residual_mem {q : Mat d} {r b : ℤ} (hrb : r ≤ b)
    {w vB : Fin d → ℤ} (hw : adaptedCellCenter q r w ∈ adaptedCellAt q b vB) :
    (adaptedCellCenter q r fun i => w i - (3 : ℤ) ^ (b - r).toNat * vB i) ∈
      adaptedCell q b := by
  rw [Recurrence.adaptedCellAt_eq_translateSet, mem_translateSet_iff_sub_mem,
    adaptedCellCenter_sub_ancestor q hrb w vB] at hw
  simpa using hw

/-- **An aligned adapted cell contains its own center.**  This is what makes the
printed index set of `X_B` — the aligned cells contained in the ancestor — a
subset of the aligned cells whose centers lie in the ancestor. -/
theorem adaptedCellCenter_mem_self (q : Mat d) (r : ℤ) (w : Fin d → ℤ) :
    adaptedCellCenter q r w ∈ adaptedCellAt q r w := by
  rw [Recurrence.adaptedCellAt_eq_image, Recurrence.adaptedCellCenter_eq]
  exact Set.mem_image_of_mem _ (Recurrence.standardCellCenter_mem_standardCell r w)

/-! ## The comparison -/

/-- **`E[X_B^Q] ≤ 𝓗_q^cen(b)` for the membership form of the ancestor
statistic.**  The centered maximum over all the aligned cells of the scales
`[j_*, b]` whose centers lie in an aligned scale-`b` cell, weighted by
`3^{-ρ_max(b-r)}` and measured at the checkpoint normalization `E_b^q`, has
`Q`-th moment at most the centered history at the checkpoint.

The only input is stationarity of the coefficient law: the ancestor is an
integer translate of `⋄_b^q`, the aligned cells inside it are the same integer
translate of the aligned cells inside `⋄_b^q`, and an integer translation does
not move a lower integral. -/
theorem ancestor_moment_le_centeredHistory {Q rhoMax : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) {b : ℤ} (hlb : l ≤ b)
    (hpdb : Book.Ch02.BlockPosDef (adaptedMean P q b)) (vB : Fin d → ℤ) :
    ∫⁻ x, (⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b) (w : Fin d → ℤ)
        (_ : adaptedCellCenter q r w ∈ adaptedCellAt q b vB),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
        blockSize (blockSub (adaptedResponse q r w x) (adaptedMean P q r))
          (adaptedMean P q b))) ^ Q ∂P ≤
      centeredHistory P Q rhoMax q jStar b := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  obtain ⟨v, hv⟩ := Recurrence.exists_intVec_adaptedCellCenter hq hlb vB
  set F : CoeffSpace d → ℝ≥0∞ := fun x =>
    ⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b) (w : Fin d → ℤ)
        (_ : adaptedCellCenter q r w ∈ adaptedCell q b),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
        blockSize (blockSub (adaptedResponse q r w x) (adaptedMean P q r))
          (adaptedMean P q b)) with hFdef
  have hFmeas : AEMeasurable F P := by
    rw [hFdef]
    exact PortableHistory.aemeasurable_adaptedSup hqPD (Recurrence.isSymmetricBlockMat_adaptedMean P q b) hpdb
      (fun r => (3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ)))) jStar b (adaptedCell q b)
  have hFQ : AEMeasurable (fun z => F z ^ Q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hFmeas
  have hpt : ∀ x : CoeffSpace d,
      (⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q r w ∈ adaptedCellAt q b vB),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
          blockSize (blockSub (adaptedResponse q r w x) (adaptedMean P q r))
            (adaptedMean P q b))) ≤ F (translateCoeff v x) := by
    intro x
    refine iSup_le fun r => iSup_le fun hr1 => iSup_le fun hr2 => iSup_le fun w =>
      iSup_le fun hw => ?_
    rw [PortableHistory.adaptedResponse_split q (adaptedCellCenter_sub_ancestor q hr2 w vB) hv x, hFdef]
    exact le_iSup_of_le r (le_iSup_of_le hr1 (le_iSup_of_le hr2
      (le_iSup_of_le _ (le_iSup_of_le (adaptedCellCenter_residual_mem hr2 hw) le_rfl))))
  have hkey : ∫⁻ x, F (translateCoeff v x) ^ Q ∂P = centeredHistory P Q rhoMax q jStar b :=
    PortableHistory.lintegral_comp_translateCoeff hP hFQ v
  exact le_trans (lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hQ) (le_of_eq hkey)

/-- **`E[X_B^Q] ≤ 𝓗_q^cen(b)`**, the printed sentence of the inherited rows: the
statistic `X_B` of an aligned scale-`b` ancestor, whose maximum runs over the
aligned cells of the scales `[j_*, b]` *contained* in the ancestor, has `Q`-th
moment at most the centered history at the checkpoint.

The containment index set is the printed one, `y ∈ 3^r 𝕃_q ∩ B` together with
`y + ⋄_r^q ⊆ B`: a cell contains its center, so the second condition implies the
first and the two describe the same family. -/
theorem ancestor_stationarity_le {Q rhoMax : ℝ} (hQ : 0 ≤ Q)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) {b : ℤ} (hlb : l ≤ b)
    (hpdb : Book.Ch02.BlockPosDef (adaptedMean P q b)) (vB : Fin d → ℤ) :
    ∫⁻ x, (⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b) (w : Fin d → ℤ)
        (_ : adaptedCellAt q r w ⊆ adaptedCellAt q b vB),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
        blockSize (blockSub (adaptedResponse q r w x) (adaptedMean P q r))
          (adaptedMean P q b))) ^ Q ∂P ≤
      centeredHistory P Q rhoMax q jStar b := by
  refine le_trans (lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hQ)
    (ancestor_moment_le_centeredHistory (jStar := jStar) hQ hP hq hlb hpdb vB)
  exact iSup_le fun r => iSup_le fun hr1 => iSup_le fun hr2 => iSup_le fun w =>
    iSup_le fun hsub => le_iSup_of_le r (le_iSup_of_le hr1 (le_iSup_of_le hr2
      (le_iSup_of_le w (le_iSup_of_le (hsub (adaptedCellCenter_mem_self q r w)) le_rfl))))

end Ancestor

end

end Transport
end HighContrast
end Homogenization
