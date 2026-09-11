/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Transport

/-!
# The mean order and the profile at its own checkpoint

Two opening clauses of `p.fixed.geometry.one.grid.propagation` are settled here.

*The mean order.*  "The aligned subdivision, subadditivity, and stationarity
give `E_{j+1}^q ≤ E_j^q`, and hence the asserted mean order and positivity of
the determinant increments."  On the bounded window this is the fixed-grid mean
order at the two scales, together with the two consequences the proposition
lists: `Δ_{j,T}^q ≥ 0` and `I ≤ P_{j,T}^q`.

*The profile at its own checkpoint.*  `𝒫_q(b;b) = 𝓗_q(b)`: the two sums of
`e.scale.selection.complete.profile` are empty at `T = b`, the geometric weight is
`3^0 = 1`, and the relative mean `P_{b,b}^q` has vanishing trace gap — it lies
above the identity, and its trace gap is at most `e^{Δ_{b,b}} - 1 = 0` — so the
inherited row carries the factor `1 + 𝔥_Q(P_{b,b}^q) = 1`.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

section Window

variable {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-! ## The mean order on the bounded window -/

/-- **The mean order of `p.fixed.geometry.one.grid.propagation`**, in the structural dialect of
the doubled block. -/
theorem blockMatLoewnerLE_adaptedMean_window [NeZero d]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    BlockMatLoewnerLE (adaptedMean P q T) (adaptedMean P q j) :=
  Recurrence.adaptedMean_le hP hq (le_trans hlj hj) hjT (hfin j hj (le_trans hjT hT))
    (hfin T (le_trans hj hjT) hT)

/-- **`Δ_{j,T}^q ≥ 0` on the bounded window.** -/
theorem detIncrement_nonneg_window [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    0 ≤ detIncrement P q j T :=
  Recurrence.detIncrement_nonneg hP hq (le_trans hlj hj) hjT (hfin j hj (le_trans hjT hT))
    (hfin T (le_trans hj hjT) hT)

/-- **`I ≤ P_{j,T}^q` on the bounded window**, in the structural dialect of the
doubled block. -/
theorem blockMatLoewnerLE_blockIdentity_relMean_window [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {j T : ℤ} (hj : jStar ≤ j) (hjT : j ≤ T) (hT : T ≤ TMax) :
    BlockMatLoewnerLE (Book.Ch02.blockIdentity d) (relMean P q j T) :=
  Recurrence.blockMatLoewnerLE_blockIdentity_relMean hP hq (le_trans hlj hj) hjT
    (hfin j hj (le_trans hjT hT)) (hfin T (le_trans hj hjT) hT)

/-! ## The profile at its own checkpoint -/

/-- The relative mean at a single scale has vanishing trace gap. -/
theorem trace_relMean_self [NeZero d] [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b : ℤ} (hb : jStar ≤ b) (hbT : b ≤ TMax) :
    Matrix.trace (toFullBlockMat (relMean P q b b) - 1) = 0 := by
  obtain ⟨-, -, -, -, htr⟩ := Recurrence.determinant_transport_adaptedMean hP hq
    (le_trans hlj hb) (le_refl b) (hfin b hb hbT) (hfin b hb hbT)
  rw [blockTrace_sub_two_mul, detIncrement_self, Real.exp_zero] at htr
  have hnn := trace_relMean_sub_one_nonneg hP hq hlj hfin hb (le_refl b) hbT
  linarith only [htr, hnn]

/-- **The gain of the relative mean at a single scale vanishes.** -/
theorem frakH_relMean_self [NeZero d] [IsProbabilityMeasure P] (Q : ℝ)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b : ℤ} (hb : jStar ≤ b) (hbT : b ≤ TMax) :
    frakH Q (relMean P q b b) = 0 := by
  rw [frakH_eq_rpow, trace_relMean_self hP hq hlj hfin hb hbT, add_zero, Real.one_rpow,
    sub_self]

/-- **`𝒫_q(b;b) = 𝓗_q(b)`.**  The profile at its own checkpoint is the complete
history it carries. -/
theorem portableProfile_self [NeZero d] [IsProbabilityMeasure P] (Q a rhoMax : ℝ)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    {b : ℤ} (hb : jStar ≤ b) (hbT : b ≤ TMax) :
    portableProfile P Q a rhoMax q jStar b b = portableHistory P Q a rhoMax q jStar b := by
  have hcen : Finset.Icc (b + 1) b = (∅ : Finset ℤ) := by
    rw [Finset.Icc_eq_empty]
    omega
  have hnl : Finset.Ico b b = (∅ : Finset ℤ) := Finset.Ico_self b
  have hzero : (-a * ((b : ℝ) - (b : ℝ))) = 0 := by ring
  rw [portableProfile, hcen, hnl, Finset.sum_empty, Finset.sum_empty, hzero,
    Real.rpow_zero, frakH_relMean_self Q hP hq hlj hfin hb hbT]
  norm_num

end Window

end

end PortableHistory
end HighContrast
end Homogenization
