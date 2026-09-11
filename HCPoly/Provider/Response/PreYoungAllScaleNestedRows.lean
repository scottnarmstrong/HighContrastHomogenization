/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.PreYoungAllScaleNestedStationarity
import HCPoly.Provider.Response.PreYoungWindowCellFiniteness

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The primal nested row pairing remains valid at every fine scale.  Above
the starting scale it uses stationary finite means; below that scale it uses
the source-window enclosure and the parent-aligned stationarity relation. -/
theorem nestedAnnealedCellPairings_primal_le_of_window_telescope
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] [NeZero d]
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
    {k : ℤ} (hks : k ≤ s)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k s)
    (g : Mat d) (hg : IsSkewMat g) (p r Pcen Qcen : Vec d) :
    avsum (alignedIndex q s t) (fun z ↦
        (1 / 2 : ℝ) * ∫ a, |vecDot Qcen
          (blockCellAverage
            (adaptedCellAt q k (nestedLabel k s z w))
            (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (a.subSkew g hg) p r)).1| ∂P) ≤
        profileRowCellEnergy P (Recurrence.posDef_of_isRoundedGrid hgrid) k s t w
            (fun a ↦ a.subSkew g hg) p r *
          profileSchurLoadFlux
            (profileHattedBlock g
              (annealedBlock P (adaptedCellAt q k w))) Qcen ∧
      avsum (alignedIndex q s t) (fun z ↦
        (1 / 2 : ℝ) * ∫ a, |vecDot Pcen
          (blockCellAverage
            (adaptedCellAt q k (nestedLabel k s z w))
            (diagonalWeakState (Recurrence.posDef_of_isRoundedGrid hgrid) t
              (a.subSkew g hg) p r)).2| ∂P) ≤
        profileRowCellEnergy P (Recurrence.posDef_of_isRoundedGrid hgrid) k s t w
            (fun a ↦ a.subSkew g hg) p r *
          profileSchurLoadGradient
            (profileHattedBlock g
              (annealedBlock P (adaptedCellAt q k w))) Pcen := by
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let Z := alignedIndex q s t
  let energy : (Fin d → ℤ) → ℝ := fun z ↦
    profileAnnealedCellEnergySq P hq k t
      (nestedLabel k s z w) (fun a ↦ a.subSkew g hg) p r
  let loadFlux : (Fin d → ℤ) → ℝ := fun z ↦
    profileSchurLoadFlux
      (profileHattedBlock g
        (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Qcen
  let loadGradient : (Fin d → ℤ) → ℝ := fun z ↦
    profileSchurLoadGradient
      (profileHattedBlock g
        (annealedBlock P (adaptedCellAt q k (nestedLabel k s z w)))) Pcen
  let pairFlux : (Fin d → ℤ) → ℝ := fun z ↦
    (1 / 2 : ℝ) * ∫ a, |vecDot Qcen
      (blockCellAverage (adaptedCellAt q k (nestedLabel k s z w))
        (diagonalWeakState hq t (a.subSkew g hg) p r)).1| ∂P
  let pairGradient : (Fin d → ℤ) → ℝ := fun z ↦
    (1 / 2 : ℝ) * ∫ a, |vecDot Pcen
      (blockCellAverage (adaptedCellAt q k (nestedLabel k s z w))
        (diagonalWeakState hq t (a.subSkew g hg) p r)).2| ∂P
  have hintRef : HasIntegrableCoarseBlock P (adaptedCellAt q k w) :=
    hasIntegrableCoarseBlock_adaptedCellAt_of_window_telescope
      hstat hY hm0 hqeq hgrid hbelow hblocks hks hst (Or.inl rfl) hw
  have hmeasRef : HasMeasurableCoarseBlock P (adaptedCellAt q k w) :=
    fun i j ↦ (hintRef i j).aestronglyMeasurable
  have hmem : ∀ z ∈ Z,
      nestedLabel k s z w ∈ alignedIndex q k t := by
    intro z hz
    exact nestedLabel_mem_alignedIndex hq hks hst hw hz
  have henergy : ∀ z ∈ Z, 0 ≤ energy z := by
    intro z hz
    exact profileAnnealedCellEnergySq_nonneg P hq k t
      (nestedLabel k s z w) (fun a ↦ a.subSkew g hg) p r
  have hpathFlux : ∀ z ∈ Z, loadFlux z =
      profileSchurLoadFlux
        (profileHattedBlock g
          (annealedBlock P (adaptedCellAt q k w))) Qcen := by
    intro z hz
    exact profileSchurLoadFlux_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hjs z w hmeasRef g Qcen
  have hpathGradient : ∀ z ∈ Z, loadGradient z =
      profileSchurLoadGradient
        (profileHattedBlock g
          (annealedBlock P (adaptedCellAt q k w))) Pcen := by
    intro z hz
    exact profileSchurLoadGradient_nestedLabel_eq_of_parent_aligned
      hstat hgrid hks hjs z w hmeasRef g Pcen
  have hintt : HasFiniteAdaptedMean P q t :=
    (hblocks t (hjs.trans hst) le_rfl).1
  have hcell : ∀ z ∈ Z,
      pairFlux z ≤ Real.sqrt (energy z) * loadFlux z ∧
      pairGradient z ≤ Real.sqrt (energy z) * loadGradient z := by
    intro z hz
    have hintNested : HasIntegrableCoarseBlock P
        (adaptedCellAt q k (nestedLabel k s z w)) :=
      hasIntegrableCoarseBlock_adaptedCellAt_of_window_telescope
        hstat hY hm0 hqeq hgrid hbelow hblocks (hks.trans hst) le_rfl
          (Or.inr rfl) (hmem z hz)
    exact half_integral_cellPairings_primal_le_of_integrable_energy
      hq (hks.trans hst) (hmem z hz) g hg p r Pcen Qcen hintNested
      (integrable_cellQuarterEnergy_subSkew_of_finiteAdaptedMean
        hq (hks.trans hst) (hmem z hz) hintt g hg p r)
  constructor
  · simpa only [hq, Z, pairFlux, energy, loadFlux,
      profileRowCellEnergy] using
      avsum_cellPair_le_sqrt_avsum_energy_mul_load
        (alignedIndex_nonempty hq hst) pairFlux energy loadFlux
        (profileSchurLoadFlux
          (profileHattedBlock g
            (annealedBlock P (adaptedCellAt q k w))) Qcen)
        henergy (profileSchurLoadFlux_nonneg _ _) hpathFlux
        (fun z hz ↦ (hcell z hz).1)
  · simpa only [hq, Z, pairGradient, energy, loadGradient,
      profileRowCellEnergy] using
      avsum_cellPair_le_sqrt_avsum_energy_mul_load
        (alignedIndex_nonempty hq hst) pairGradient energy loadGradient
        (profileSchurLoadGradient
          (profileHattedBlock g
            (annealedBlock P (adaptedCellAt q k w))) Pcen)
        henergy (profileSchurLoadGradient_nonneg _ _) hpathGradient
        (fun z hz ↦ (hcell z hz).2)

end

end Homogenization.HighContrast.Response
