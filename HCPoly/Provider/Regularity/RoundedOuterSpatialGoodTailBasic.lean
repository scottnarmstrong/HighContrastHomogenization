/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.RoundedOuterSpatialGoodTail

/-!
# Basic operations on rounded outer spatial good tails

The rounded physical weak errors are nonnegative.  Consequently their finite
rows and all-later tails support the same restriction and monotonicity operations
used by the finite regularity iteration, without changing the common starting
scale or its geometry witness.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The physical weak error on a base-rounded outer cell is nonnegative. -/
theorem baseRoundedSpatialWeakError_nonneg [NeZero d]
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s : ℝ) (k : ℤ) :
    0 ≤ baseRoundedSpatialWeakError a abar hS s k := by
  unfold baseRoundedSpatialWeakError
  exact Real.sqrt_nonneg _

/-- The finite rounded physical weak-error row between two integer scales. -/
def BaseRoundedSpatialGoodTailOnInterval [NeZero d]
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s delta : ℝ) (n m : ℤ) : Prop :=
  (∑ k ∈ Finset.Icc n m,
    baseRoundedSpatialWeakError a abar hS s k) ≤ delta

/-- Increasing the tolerance preserves a finite rounded good-tail row. -/
theorem BaseRoundedSpatialGoodTailOnInterval.mono [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta delta' : ℝ} {n m : ℤ}
    (h : BaseRoundedSpatialGoodTailOnInterval a abar hS s delta n m)
    (hdelta : delta ≤ delta') :
    BaseRoundedSpatialGoodTailOnInterval a abar hS s delta' n m :=
  h.trans hdelta

/-- An all-later rounded good tail supplies every admissible finite row. -/
theorem BaseRoundedSpatialGoodTail.interval [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta : ℝ} {n m : ℤ}
    (h : BaseRoundedSpatialGoodTail a abar hS s delta n)
    (hnm : n ≤ m) :
    BaseRoundedSpatialGoodTailOnInterval a abar hS s delta n m :=
  h m hnm

/-- Increasing the tolerance preserves an all-later rounded good tail. -/
theorem BaseRoundedSpatialGoodTail.mono [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta delta' : ℝ} {n : ℤ}
    (h : BaseRoundedSpatialGoodTail a abar hS s delta n)
    (hdelta : delta ≤ delta') :
    BaseRoundedSpatialGoodTail a abar hS s delta' n := by
  intro m hnm
  exact (h.interval hnm).mono hdelta

/-- Discarding initial scales preserves a finite rounded good-tail row. -/
theorem BaseRoundedSpatialGoodTailOnInterval.mono_start [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta : ℝ} {n n' m : ℤ}
    (h : BaseRoundedSpatialGoodTailOnInterval a abar hS s delta n m)
    (hnn' : n ≤ n') :
    BaseRoundedSpatialGoodTailOnInterval a abar hS s delta n' m := by
  apply le_trans _ h
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc hnn' le_rfl) ?_
  intro k _ _
  exact baseRoundedSpatialWeakError_nonneg a abar hS s k

/-- Discarding initial scales preserves an all-later rounded good tail. -/
theorem BaseRoundedSpatialGoodTail.mono_start [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta : ℝ} {n n' : ℤ}
    (h : BaseRoundedSpatialGoodTail a abar hS s delta n)
    (hnn' : n ≤ n') :
    BaseRoundedSpatialGoodTail a abar hS s delta n' := by
  intro m hn'm
  exact (h.interval (hnn'.trans hn'm)).mono_start hnn'

/-- Every physical weak error in a rounded good tail is bounded by its
tolerance. -/
theorem BaseRoundedSpatialGoodTail.weakError_le [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta : ℝ} {n k : ℤ}
    (h : BaseRoundedSpatialGoodTail a abar hS s delta n)
    (hnk : n ≤ k) :
    baseRoundedSpatialWeakError a abar hS s k ≤ delta := by
  have hkMem : k ∈ Finset.Icc n k := Finset.mem_Icc.mpr ⟨hnk, le_rfl⟩
  have hkSum :
      baseRoundedSpatialWeakError a abar hS s k ≤
        ∑ j ∈ Finset.Icc n k,
          baseRoundedSpatialWeakError a abar hS s j := by
    exact Finset.single_le_sum
      (fun j _ ↦ baseRoundedSpatialWeakError_nonneg a abar hS s j) hkMem
  exact hkSum.trans (h.interval hnk)

end

end Transport
end HighContrast
end Homogenization
