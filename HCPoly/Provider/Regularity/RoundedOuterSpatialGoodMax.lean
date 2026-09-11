/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.RoundedOuterSpatialGoodTailBasic

/-!
# Rounded outer spatial good maxima

The finite rounded Lipschitz recurrence consumes pointwise smallness on a
scale interval.  This module extracts that event from the literal physical
summable row, preserving its geometry witness, tolerance, and common starting
scale exactly.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

noncomputable section

variable {d : ℕ}

/-- Every base-rounded spatial weak error on `[n,m]` is at most `delta`. -/
def BaseRoundedSpatialGoodMaxOnInterval [NeZero d]
    (a : CoeffSpace d) (abar : Mat d)
    (hS : (symmPart abar).PosDef) (s delta : ℝ) (n m : ℤ) : Prop :=
  ∀ k ∈ Finset.Icc n m,
    baseRoundedSpatialWeakError a abar hS s k ≤ delta

/-- Extract the pointwise physical weak-error bound from a rounded good-max
row. -/
theorem BaseRoundedSpatialGoodMaxOnInterval.weakError_le [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta : ℝ} {n m k : ℤ}
    (h : BaseRoundedSpatialGoodMaxOnInterval a abar hS s delta n m)
    (hk : k ∈ Finset.Icc n m) :
    baseRoundedSpatialWeakError a abar hS s k ≤ delta :=
  h k hk

/-- Increasing the tolerance preserves a rounded good-max row. -/
theorem BaseRoundedSpatialGoodMaxOnInterval.mono [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta delta' : ℝ} {n m : ℤ}
    (h : BaseRoundedSpatialGoodMaxOnInterval a abar hS s delta n m)
    (hdelta : delta ≤ delta') :
    BaseRoundedSpatialGoodMaxOnInterval a abar hS s delta' n m := by
  intro k hk
  exact (h.weakError_le hk).trans hdelta

/-- A finite rounded summable row controls the pointwise maximum row at the
same tolerance. -/
theorem BaseRoundedSpatialGoodTailOnInterval.toGoodMax [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta : ℝ} {n m : ℤ}
    (h : BaseRoundedSpatialGoodTailOnInterval a abar hS s delta n m) :
    BaseRoundedSpatialGoodMaxOnInterval a abar hS s delta n m := by
  intro k hk
  have hsingle :
      baseRoundedSpatialWeakError a abar hS s k ≤
        ∑ j ∈ Finset.Icc n m,
          baseRoundedSpatialWeakError a abar hS s j := by
    exact Finset.single_le_sum
      (fun j _ ↦ baseRoundedSpatialWeakError_nonneg a abar hS s j) hk
  exact hsingle.trans h

/-- An all-later rounded summable tail controls every admissible finite
good-max row. -/
theorem BaseRoundedSpatialGoodTail.goodMaxOnInterval [NeZero d]
    {a : CoeffSpace d} {abar : Mat d}
    {hS : (symmPart abar).PosDef} {s delta : ℝ} {n m : ℤ}
    (h : BaseRoundedSpatialGoodTail a abar hS s delta n)
    (hnm : n ≤ m) :
    BaseRoundedSpatialGoodMaxOnInterval a abar hS s delta n m :=
  (h.interval hnm).toGoodMax

end

end Transport

noncomputable section

variable {d : ℕ}

end

end HighContrast
end Homogenization
