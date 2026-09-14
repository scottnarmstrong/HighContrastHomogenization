/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.FiniteFamilyPositiveGap
import HCPoly.Provider.PortableHistory.CheckpointMoment

/-!
# The finite target family underlying the centered history

The target indices in the centered history form a finite sigma family.  This
packages that family without introducing a new carrier and compares the
block-size history directly with the finite Schatten supremum consumed by the
collective positive-gap estimate.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The centered history is bounded by the weighted finite Schatten supremum
over precisely the target cells contained in its terminal adapted cell. -/
theorem exists_finite_target_family_centeredHistory_le
    {P : Measure (CoeffSpace d)} {Q rhoMax : ℝ} {q : Mat d} (hq : q.PosDef)
    {jStar n : ℤ} (hjn : jStar ≤ n) (hQ : 0 < Q)
    (hFnpos : Book.Ch02.BlockPosDef (adaptedMean P q n)) :
    ∃ (Z : ℤ → Finset (Fin d → ℤ))
        (hs : ((Finset.Icc jStar n).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))).Nonempty),
      (∀ j ∈ Finset.Icc jStar n,
        (↑(Z j) : Set (Fin d → ℤ)) =
            {w | adaptedCellCenter q j w ∈ adaptedCell q n} ∧
          (Z j).card = 3 ^ (d * (n - j).toNat)) ∧
      (∀ i ∈ ((Finset.Icc jStar n).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))),
        adaptedCellAt q i.1 i.2 ⊆ adaptedCell q n) ∧
      (∀ i ∈ ((Finset.Icc jStar n).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))),
        0 < (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ)))) ∧
      centeredHistory P Q rhoMax q jStar n ≤
        ∫⁻ x, ENNReal.ofReal
          (((Finset.Icc jStar n).sigma Z).sup' hs fun i =>
            (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
              schattenSize Q
                (blockSub (adaptedResponse q i.1 i.2 x)
                  (adaptedMean P q i.1))
                (adaptedMean P q n)) ^ Q ∂P := by
  classical
  have hex : ∀ j : ℤ, ∃ Zj : Finset (Fin d → ℤ),
      j ∈ Finset.Icc jStar n →
        (↑Zj : Set (Fin d → ℤ)) =
            {w | adaptedCellCenter q j w ∈ adaptedCell q n} ∧
          Zj.card = 3 ^ (d * (n - j).toNat) := by
    intro j
    by_cases hj : j ∈ Finset.Icc jStar n
    · obtain ⟨Zj, hZj, hcard⟩ :=
        Recurrence.exists_finset_adaptedCellCenter_mem hq (Finset.mem_Icc.mp hj).2
      exact ⟨Zj, fun _ => ⟨hZj, hcard⟩⟩
    · exact ⟨∅, fun hj' => (hj hj').elim⟩
  choose Z hZ using hex
  have hn : n ∈ Finset.Icc jStar n := Finset.mem_Icc.mpr ⟨hjn, le_rfl⟩
  have hzero : (0 : Fin d → ℤ) ∈ Z n := by
    have hzeroSet : (0 : Fin d → ℤ) ∈ (↑(Z n) : Set (Fin d → ℤ)) := by
      rw [(hZ n hn).1, Set.mem_ofPred_eq,
        Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq (le_refl n)]
      intro i
      simp
    exact hzeroSet
  have hs : ((Finset.Icc jStar n).sigma Z :
      Finset ((_ : ℤ) × (Fin d → ℤ))).Nonempty :=
    Finset.sigma_nonempty.mpr ⟨n, hn, ⟨0, hzero⟩⟩
  refine ⟨Z, hs, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact hZ j hj
  · intro i hi
    have hi' := Finset.mem_sigma.mp hi
    have hcenter : adaptedCellCenter q i.1 i.2 ∈ adaptedCell q n := by
      have hwSet : i.2 ∈ (↑(Z i.1) : Set (Fin d → ℤ)) := hi'.2
      rw [(hZ i.1 hi'.1).1, Set.mem_ofPred_eq] at hwSet
      exact hwSet
    exact Recurrence.adaptedCellAt_subset_adaptedCell hq
      (Finset.mem_Icc.mp hi'.1).2 hcenter
  · intro i hi
    exact Real.rpow_pos_of_pos (by norm_num) _
  · rw [centeredHistory]
    refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hQ.le
    refine iSup_le fun j => iSup_le fun hjStar => iSup_le fun hjn' =>
      iSup_le fun w => iSup_le fun hw => ?_
    have hj : j ∈ Finset.Icc jStar n := Finset.mem_Icc.mpr ⟨hjStar, hjn'⟩
    have hwZ : w ∈ Z j := by
      have hwSet : w ∈ (↑(Z j) : Set (Fin d → ℤ)) := by
        rw [(hZ j hj).1, Set.mem_ofPred_eq]
        exact hw
      exact hwSet
    have hi : (⟨j, w⟩ : ((_ : ℤ) × (Fin d → ℤ))) ∈
        ((Finset.Icc jStar n).sigma Z :
          Finset ((_ : ℤ) × (Fin d → ℤ))) :=
      Finset.mem_sigma.mpr ⟨hj, hwZ⟩
    have hsize : blockSize
          (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q n) ≤
        schattenSize Q
          (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
          (adaptedMean P q n) :=
      PortableHistory.blockSize_le_schattenSize
        (isSymmetricBlockMat_blockSub
          (Recurrence.isSymmetricBlockMat_adaptedResponse q j w x)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q j))
        (Recurrence.isSymmetricBlockMat_adaptedMean P q n) hFnpos hQ
    have hweight :
        -rhoMax * ((n : ℝ) - (j : ℝ)) =
          rhoMax * ((j : ℝ) - (n : ℝ)) := by
      ring
    rw [hweight]
    refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hsize ?_).trans ?_)
    · exact Real.rpow_nonneg (by norm_num) _
    · exact Finset.le_sup'
        (fun i : ((_ : ℤ) × (Fin d → ℤ)) =>
          (3 : ℝ) ^ (rhoMax * ((i.1 : ℝ) - (n : ℝ))) *
            schattenSize Q
              (blockSub (adaptedResponse q i.1 i.2 x)
                (adaptedMean P q i.1))
              (adaptedMean P q n)) hi

end

end Transport
end HighContrast
end Homogenization
