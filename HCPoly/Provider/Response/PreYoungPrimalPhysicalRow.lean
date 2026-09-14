/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.PreYoungPrimalPhysicalProjectionLimit

/-!
# The physical primal cutoff row

The physical projection limit is rewritten as the literal cutoff-oscillation
row appearing in the decomposition of the primal cutoff mean.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Annealed integration of the physical primal pairing equals the coordinate
cutoff-oscillation row on the terminal parent partition. -/
theorem integral_primal_physical_oscillation_eq_cutoff_row
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    (∫ a, primal_physical_oscillation hq s t g hg p r Qcen a ∂P) =
      avsum (alignedIndex q s t) (fun z ↦
        ∑ i, Qcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
          (adaptedPreYoungCutoff q hq t x -
            volumeAverage (adaptedCellAt q s z)
              (adaptedPreYoungCutoff q hq t)) *
            toFullBlockVec
              (diagonalWeakState hq t (a.subSkew g hg) p r x)
              (Sum.inl i)) ∂P) := by
  let Z := alignedIndex q s t
  let coord : (Fin d → ℤ) → Fin d → CoeffSpace d → ℝ := fun z i a ↦
    volumeAverage (adaptedCellAt q s z) (fun x ↦
      (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s z)
          (adaptedPreYoungCutoff q hq t)) *
        toFullBlockVec
          (diagonalWeakState hq t (a.subSkew g hg) p r x)
          (Sum.inl i))
  let parent : (Fin d → ℤ) → CoeffSpace d → ℝ := fun z a ↦
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦
      adaptedPreYoungCutoff q hq t (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let F : Vec d → BlockVec d :=
      diagonalWeakState hq t (a.subSkew g hg) p r
    let G : Vec d → ℝ := fun y ↦ vecDot Qcen (F (matVecMul q y)).1
    cubeBesovPairing R f G
  have hread :=
    (integrable_primal_adaptedFiveTermSplit_readouts
      hq hm0 hst g hg p r hweak).2
  have hcoord : ∀ z ∈ Z, ∀ i, Integrable (coord z i) P := by
    intro z hz i
    simpa only [coord, toFullBlockVec] using hread z hz (Sum.inl i)
  have hparentEq : ∀ z ∈ Z, parent z =
      fun a ↦ ∑ i, Qcen i * coord z i a := by
    intro z hz
    funext a
    simpa only [parent, coord, toFullBlockVec] using
      primal_physical_parent_pairing_eq_coordinate_sum
        hq hst hz g hg a p r Qcen
  have hparent : ∀ z ∈ Z, Integrable (parent z) P := by
    intro z hz
    rw [hparentEq z hz]
    exact integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i hi ↦
      (hcoord z hz i).const_mul (Qcen i)
  change (∫ a, avsum Z (fun z ↦ parent z a) ∂P) = _
  rw [integral_avsum_eq_avsum_integral Z parent hparent]
  unfold avsum
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  change (∫ a, parent z a ∂P) = _
  rw [hparentEq z hz]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
  · intro i hi
    exact (hcoord z hz i).const_mul (Qcen i)

/-- The literal primal gradient-slot cutoff oscillation is controlled by the
all-earlier hatted row. -/
theorem of_real_abs_primal_cutoff_oscillation_row_le
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {gamma : ℝ} {E : BlockMat d} {Psi : ℝ → ℝ} {K Cd : ℝ}
    {jStar M : ℤ} {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P gamma E Psi K Cd jStar M Y)
    {m0 q : Mat d} (hm0 : m0.PosDef) (hqeq : q = roundedGrid jStar m0)
    (hgrid : IsRoundedGrid jStar q)
    {s t : ℤ} (hjs : jStar ≤ s) (hst : s ≤ t)
    (hbelow : ∀ k : ℤ, k < jStar → ∀ v : ℤ,
      v = s ∨ v = t → ∀ z ∈ containedCenters q k v,
        adaptedCellTranslate q k z ⊆ centeredCube d M)
    (hblocks : ∀ k : ℤ, jStar ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    ENNReal.ofReal
        |avsum (alignedIndex q s t) (fun z ↦
          ∑ i, Qcen i * ∫ a, volumeAverage (adaptedCellAt q s z) (fun x ↦
            (adaptedPreYoungCutoff q (Recurrence.posDef_of_isRoundedGrid hgrid) t x -
              volumeAverage (adaptedCellAt q s z)
                (adaptedPreYoungCutoff q
                  (Recurrence.posDef_of_isRoundedGrid hgrid) t)) *
              toFullBlockVec
                (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) t
                  (a.subSkew g hg) p r x)
                (Sum.inl i)) ∂P)| ≤
      ENNReal.ofReal
          (preYoungRowCoefficient d *
            (3 : ℝ) ^ (-((t : ℝ) - (s : ℝ))) *
              Real.sqrt (∫ a, responseJ
                (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t)
                ((a.subSkew g hg).coeffOn
                  (adaptedDomain (Recurrence.posDef_of_isRoundedGrid hgrid) t))
                p r ∂P)) *
        profilePrimalHattedEarlierRow P q g s Pcen Qcen ^ (1 / 2 : ℝ) := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  have hphysical := of_real_abs_integral_primal_physical_oscillation_le_row
    hstat hY hm0 hqeq hgrid hjs hst hbelow hblocks
      g hg p r Pcen Qcen hweak
  have heq := integral_primal_physical_oscillation_eq_cutoff_row
    (P := P) hq hm0 hst g hg p r Qcen hweak
  rw [heq] at hphysical
  simpa only [hq] using hphysical

end

end Homogenization.HighContrast.Response
