/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationHigh

/-!
# The centered half of the majorization

The centered history at the terminal scale splits at the checkpoint: the scales
at or below `b` are majorized by the centered history at `b` after the terminal
renormalization, and the scales above `b` are the second row of the profile
`e.scale.selection.complete.profile`.  Adding the two halves proves the centered
half of `e.fixed.geometry.profile.majorization`,

`𝓗_q^cen(T) ≤ 3^{-a(T-b)}(1 + 𝔥_Q(P_{b,T}^q)) 𝓗_q^cen(b)`
`             + Σ_{j=b+1}^T 3^{-a(T-j)} e^{QΔ_{j,T}^q} (v_j^q)^Q`.

The splitting itself is max-to-sum on two terms: a supremum over a union of two
ranges of scales is the maximum of the two suprema, and the `Q`-th power of a
maximum of two nonnegative quantities is at most the sum of their `Q`-th powers.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped MatrixOrder Matrix.Norms.L2Operator Matrix ENNReal

noncomputable section

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- **The centered half of `e.fixed.geometry.profile.majorization`.** -/
theorem centered_majorization [NeZero d] [IsProbabilityMeasure P] {Q a rhoMax : ℝ}
    (hQ : 0 < Q) (hadm : a ≤ Q * rhoMax - (d : ℝ))
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ TMax → HasFiniteAdaptedMean P q r)
    {b T : ℤ} (hjb : jStar ≤ b) (hbT : b ≤ T) (hT : T ≤ TMax) :
    centeredHistory P Q rhoMax q jStar T ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b T))) * centeredHistory P Q rhoMax q jStar b +
        ∑ j ∈ Finset.Icc (b + 1) T,
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (j : ℝ))) *
            Real.exp (Q * detIncrement P q j T)) * centeredMoment P Q q j ^ Q := by
  classical
  have hqPD : q.PosDef := Recurrence.posDef_of_isRoundedGrid hq
  have hpdT : Book.Ch02.BlockPosDef (adaptedMean P q T) :=
    (blockPosDef_iff_posDef (Recurrence.isSymmetricBlockMat_adaptedMean P q T)).mpr
      (Recurrence.posDef_toFullBlockMat_adaptedMean hq T (hfin T (le_trans hjb hbT) hT))
  have hlow : AEMeasurable (fun x : CoeffSpace d =>
      (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q T))) ^ Q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (aemeasurable_adaptedSup hqPD (Recurrence.isSymmetricBlockMat_adaptedMean P q T) hpdT
        (fun r => (3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (r : ℝ)))) jStar b (adaptedCell q T))
  have hsplit : centeredHistory P Q rhoMax q jStar T ≤
      (∫⁻ x, (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q T))) ^ Q ∂P) +
      ∫⁻ x, (⨆ (j : ℤ) (_ : b + 1 ≤ j) (_ : j ≤ T) (w : Fin d → ℤ)
          (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
        ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
          blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
            (adaptedMean P q T))) ^ Q ∂P := by
    rw [centeredHistory, ← lintegral_add_left' hlow]
    refine lintegral_mono fun x => ?_
    set A : ℝ≥0∞ := ⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
        (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q T)) with hA
    set B : ℝ≥0∞ := ⨆ (j : ℤ) (_ : b + 1 ≤ j) (_ : j ≤ T) (w : Fin d → ℤ)
        (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q T)) with hB
    have hmax : (⨆ (j : ℤ) (_ : jStar ≤ j) (_ : j ≤ T) (w : Fin d → ℤ)
        (_ : adaptedCellCenter q j w ∈ adaptedCell q T),
      ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((T : ℝ) - (j : ℝ))) *
        blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q T))) ≤ max A B := by
      refine iSup_le fun j => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun w =>
        iSup_le fun hw => ?_
      rcases le_or_gt j b with hjb' | hjb'
      · refine le_trans ?_ (le_max_left A B)
        rw [hA]
        exact le_iSup_of_le j (le_iSup_of_le h1 (le_iSup_of_le hjb'
          (le_iSup_of_le w (le_iSup_of_le hw le_rfl))))
      · refine le_trans ?_ (le_max_right A B)
        rw [hB]
        exact le_iSup_of_le j (le_iSup_of_le (by omega) (le_iSup_of_le h2
          (le_iSup_of_le w (le_iSup_of_le hw le_rfl))))
    refine le_trans (ENNReal.rpow_le_rpow hmax hQ.le) ?_
    rcases le_total A B with h | h
    · rw [max_eq_right h]
      exact le_add_self
    · rw [max_eq_left h]
      exact le_self_add
  exact hsplit.trans (add_le_add
    (centered_low_le hQ hadm hP hq hlj hfin hjb hbT hT)
    (centered_high_le hQ hadm hP hq hlj hfin hjb hbT hT))

end Window

end

end PortableHistory
end HighContrast
end Homogenization
