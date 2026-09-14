/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.PreYoungPrimalFluxProjectedRowBound
import HCPoly.Provider.Response.PreYoungPrimalPhysicalProjectionLimit

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory _root_.Filter
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-!
# The physical primal flux projection limit

Finite projected primal flux pairings converge to the physical cutoff
oscillation. Their common annealed row bound passes to the limit by Fatou's
lemma.
-/

/-- Finite-depth projected primal flux pairings converge pointwise to the
physical pairing. -/
theorem tendsto_primal_flux_projected_oscillation
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (a : CoeffSpace d)
    (p r Pcen : Vec d) :
    Tendsto
      (fun n ↦ primal_flux_projected_oscillation
        hq s t g hg p r Pcen (n + 1) a)
      atTop (nhds (primal_flux_physical_oscillation
        hq s t g hg p r Pcen a)) := by
  let Z := alignedIndex q s t
  apply tendsto_avsum Z _ _
  intro z hz
  let R : TriadicCube d := translateCube z (originCube d s)
  let phi : Vec d → ℝ := fun y ↦
    adaptedPreYoungCutoff q hq t (matVecMul q y)
  let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
  let F : Vec d → BlockVec d :=
    diagonalWeakState hq t (a.subSkew g hg) p r
  let G : Vec d → ℝ := fun y ↦ vecDot Pcen (F (matVecMul q y)).2
  have hGInt : IntegrableOn G (cubeSet R) volume := by
    simpa only [G, F, R] using
      integrableOn_vecDot_diagonalWeakState_flux_pullback
        hq hst hz (a.subSkew g hg) p r Pcen
  have hphiCont : Continuous phi :=
    (adaptedPreYoungCutoff_smooth hq t).continuous.comp
      (continuous_matVecMul q)
  have hphiInt : IntegrableOn phi (cubeSet R) volume :=
    (hphiCont.continuousOn.integrableOn_compact
      (isBounded_cubeSet R).isCompact_closure).mono_set subset_closure
  have hfInt : IntegrableOn f (cubeSet R) volume :=
    hphiInt.sub (integrableOn_const (volume_cubeSet_lt_top R).ne)
  have hphiAvg0 : 0 ≤ cubeAverage R phi :=
    le_cubeAverage_of_le R hphiInt
      (fun y ↦ adaptedPreYoungCutoff_nonneg hq t _)
  have hphiAvg2 : cubeAverage R phi ≤ 2 :=
    cubeAverage_le_of_le R hphiInt
      (fun y ↦ adaptedPreYoungCutoff_le_two hq t _)
  have hfBound : ∀ y ∈ cubeSet R, |f y| ≤ 2 := by
    intro y hy
    dsimp only [f, phi]
    rw [abs_le]
    constructor <;>
      linarith only [adaptedPreYoungCutoff_nonneg hq t (matVecMul q y),
        adaptedPreYoungCutoff_le_two hq t (matVecMul q y),
        hphiAvg0, hphiAvg2]
  simpa only [primal_flux_projected_oscillation,
    primal_flux_physical_oscillation, Z, R, phi, f, F, G] using
      projected_primal_pairing_tendsto_physical
        R f G 2 hGInt hfInt (by norm_num) hfBound

/-- The physical primal flux pairing on one parent cell is its coordinate
expansion. -/
theorem primal_flux_physical_parent_pairing_eq_coordinate_sum
    [NeZero d] {q : Mat d} (hq : q.PosDef) {s t : ℤ} (hst : s ≤ t)
    {z : Fin d → ℤ} (hz : z ∈ alignedIndex q s t)
    (g : Mat d) (hg : IsSkewMat g) (a : CoeffSpace d)
    (p r Pcen : Vec d) :
    let U := adaptedCellAt q s z
    let cut := adaptedPreYoungCutoff q hq t
    let X := diagonalWeakState hq t (a.subSkew g hg) p r
    let R : TriadicCube d := translateCube z (originCube d s)
    let phi : Vec d → ℝ := fun y ↦ cut (matVecMul q y)
    let f : Vec d → ℝ := fun y ↦ phi y - cubeAverage R phi
    let G : Vec d → ℝ := fun y ↦ vecDot Pcen (X (matVecMul q y)).2
    cubeBesovPairing R f G =
      ∑ i, Pcen i * volumeAverage U (fun x ↦
        (cut x - volumeAverage U cut) * (X x).2 i) := by
  dsimp only
  let U := adaptedCellAt q s z
  let cut := adaptedPreYoungCutoff q hq t
  let X := diagonalWeakState hq t (a.subSkew g hg) p r
  let eta : Vec d → ℝ := fun x ↦ cut x - volumeAverage U cut
  have hcoordInt : ∀ i, IntegrableOn (fun x ↦ eta x * (X x).2 i) U volume := by
    intro i
    have hX := integrableOn_diagonalWeakState_snd_component_of_aligned
      hq hst hz (a.subSkew g hg) p r i
    have hetaMeas : AEStronglyMeasurable eta (volume.restrict U) :=
      ((adaptedPreYoungCutoff_smooth hq t).continuous.sub
        continuous_const).aestronglyMeasurable
    have hetaBound : ∀ᵐ x ∂volume.restrict U, ‖eta x‖ ≤
        2 + |volumeAverage U cut| :=
      _root_.Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;>
          linarith only [adaptedPreYoungCutoff_nonneg hq t x,
            adaptedPreYoungCutoff_le_two hq t x,
            neg_abs_le (volumeAverage U cut),
            le_abs_self (volumeAverage U cut)]
    simpa only [mul_comm] using! hX.bdd_mul hetaMeas hetaBound
  have hvec : volumeAverage U (fun x ↦ eta x * vecDot Pcen (X x).2) =
      ∑ i, Pcen i * volumeAverage U (fun x ↦ eta x * (X x).2 i) := by
    calc
      volumeAverage U (fun x ↦ eta x * vecDot Pcen (X x).2) =
          volumeAverage U (fun x ↦
            vecDot Pcen (fun i ↦ eta x * (X x).2 i)) := by
        apply congrArg (volumeAverage U)
        funext x
        simp only [vecDot, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        simpa only [vecDot] using
          volumeAverage_vecDot_left (U := U) Pcen
            (fun x i ↦ eta x * (X x).2 i) hcoordInt
  rw [← hvec]
  symm
  simpa only [U, cut, X, eta] using
    primal_flux_cutoff_oscillation_eq_unprojected_pairing
      hq s t z X Pcen

/-- A finite primal weak quantity makes the physical flux cutoff oscillation
integrable. -/
theorem integrable_primal_flux_physical_oscillation_of_weak
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) (hm0 : m0.PosDef)
    {s t : ℤ} (hst : s ≤ t)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen : Vec d)
    (hweak : profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    Integrable (primal_flux_physical_oscillation
      hq s t g hg p r Pcen) P := by
  let Z := alignedIndex q s t
  let coord : (Fin d → ℤ) → Fin d → CoeffSpace d → ℝ := fun z i a ↦
    volumeAverage (adaptedCellAt q s z) (fun x ↦
      (adaptedPreYoungCutoff q hq t x -
        volumeAverage (adaptedCellAt q s z)
          (adaptedPreYoungCutoff q hq t)) *
        (diagonalWeakState hq t (a.subSkew g hg) p r x).2 i)
  have hread :=
    (integrable_primal_adaptedFiveTermSplit_readouts
      hq hm0 hst g hg p r hweak).2
  have hparent : ∀ z ∈ Z, Integrable (fun a ↦
      ∑ i, Pcen i * coord z i a) P := by
    intro z hz
    exact integrable_finsetSum (Finset.univ : Finset (Fin d)) fun i hi ↦
      (by simpa only [coord, toFullBlockVec] using
        (hread z hz (Sum.inr i)).const_mul (Pcen i))
  have heq : primal_flux_physical_oscillation hq s t g hg p r Pcen =
      fun a ↦ avsum Z (fun z ↦ ∑ i, Pcen i * coord z i a) := by
    funext a
    unfold primal_flux_physical_oscillation
    unfold avsum
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    simpa only [coord, Z] using
      primal_flux_physical_parent_pairing_eq_coordinate_sum
        hq hst hz g hg a p r Pcen
  rw [heq]
  unfold avsum
  exact (integrable_finsetSum Z hparent).const_mul _

/-- The physical primal flux cutoff oscillation is controlled by the earlier
profile row. -/
theorem of_real_abs_integral_primal_flux_physical_oscillation_le_row
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
    ENNReal.ofReal |∫ a, primal_flux_physical_oscillation
        (Recurrence.posDef_of_isRoundedGrid hgrid) s t g hg p r Pcen a ∂P| ≤
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
  apply ofReal_abs_integral_le_of_tendsto_of_uniform_bound
    (F := fun n ↦ primal_flux_projected_oscillation
      hq s t g hg p r Pcen (n + 1))
    (f := primal_flux_physical_oscillation hq s t g hg p r Pcen)
  · intro n
    exact (aestrongly_measurable_primal_flux_projected_oscillation
      (P := P) hq hst g hg p r Pcen (n + 1)).aemeasurable
  · exact integrable_primal_flux_physical_oscillation_of_weak
      hq hm0 hst g hg p r Pcen hweak
  · exact _root_.Filter.Eventually.of_forall fun a ↦
      tendsto_primal_flux_projected_oscillation
        hq hst g hg a p r Pcen
  · intro n
    simpa only [hq] using
      lintegral_primal_flux_projected_oscillation_le_row
        hstat hY hm0 hqeq hgrid hjs hst hbelow hblocks
          g hg p r Pcen Qcen hweak (n + 1)

end

end Homogenization.HighContrast.Response
