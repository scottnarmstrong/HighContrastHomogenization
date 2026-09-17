import HCPoly.Entry.Multiscale.ResponseInputs.MaximizerSelection
import Homogenization.Book.Ch04.Internal.AEESliceAssembly.CarrierMinimizerFamily

/-!
# Galerkin selection on a response cell

This is the general-open-cell part of the measurable response-maximizer chain.  It is re-derived
on the current `RegCoeffField` carrier from CG's Chapter-4 Hilbert realization and this
library's public countable-energy presentation.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {d : ℕ}

/-- The doubled operator system on a general positive-volume response cell. -/
def responseCellMuSystem {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    AEEMuOperatorSystemData U a.1 :=
  (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toAEEMuOperatorSystemData
    (AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn a.2 hvol)

/-- The Hilbert realization of `responseCellMuSystem`. -/
def responseCellMuHilbert {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    MuHilbertRealization U a.1 :=
  (responseCellMuSystem hvol a).toMuHilbertRealization

/-- A fixed affine Galerkin competitor. -/
def responseCellMuCandidate {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) : HilbertBlockL2 U :=
  blockVecToHilbertBlockL2Const (U := U) P0 +
    (canonicalMuCorrectionGeneratorEmbedding U Y : HilbertBlockL2 U)

/-- The carrier slice datum at a parameter. -/
def responseSliceOf {Om : Type*} [MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun) (w : Om) :
    {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
  ⟨(A w).toFun, hSlice w⟩

theorem constantField_responseCellMuHilbert
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    (responseCellMuHilbert hvol a).constantField = blockVecToHilbertBlockL2Const (U := U) :=
  rfl

theorem correctionSpace_responseCellMuHilbert
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) :
    (responseCellMuHilbert hvol a).correctionSpace =
      MuCorrectionSpaceData.ofSubmoduleClosures U :=
  rfl

theorem responseCellMuCandidate_sub_constant_mem
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    responseCellMuCandidate P0 Y - (responseCellMuHilbert hvol a).constantField P0 ∈
      (responseCellMuHilbert hvol a).correctionSpace.correctionSpace := by
  rw [correctionSpace_responseCellMuHilbert, constantField_responseCellMuHilbert,
    responseCellMuCandidate, add_sub_cancel_left]
  exact (canonicalMuCorrectionGeneratorEmbedding U Y).2

theorem quadraticEnergy_responseCellMuCandidate
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    quadraticEnergy (responseCellMuHilbert hvol a).energyBilin
        (responseCellMuCandidate P0 Y) =
      blockEnergyAverage U a.1 (canonicalMuGeneratorAffineField (U := U) P0 Y) := by
  have hsplit := canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 Y
  rw [responseCellMuCandidate, ← hsplit]
  simpa [responseCellMuHilbert, responseCellMuSystem,
    AEEMuOperatorSystemData.toMuHilbertRealization,
    MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
    (responseCellMuSystem hvol a).toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
      (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y)

/-- On a general response cell, `Mu` is the energy of the Hilbert minimizer. -/
theorem responseMu_eq_quadraticEnergy_minimizer
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d) :
    Mu U P0 a.1 = quadraticEnergy (responseCellMuHilbert hvol a).energyBilin
      ((responseCellMuHilbert hvol a).minimizerMap P0) := by
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq _
  let H := responseCellMuHilbert hvol a
  let gen : ℕ → H.correctionSpace.correctionSpace.toSubmodule := fun n =>
    canonicalMuCorrectionGeneratorEmbedding U (ξ n)
  have hgen : DenseRange gen := by
    have hc := DenseRange.comp
      (denseRange_canonicalMuCorrectionGeneratorEmbedding U)
      (TopologicalSpace.denseRange_denseSeq
        (canonicalMuBlockCorrectionGeneratorSubmodule U))
      (continuous_canonicalMuCorrectionGeneratorEmbedding U)
    simpa [gen, ξ, H, responseCellMuHilbert, responseCellMuSystem,
      PotentialSolenoidalL2Data.toAEEMuOperatorSystemData,
      MuCorrectionSpaceData.ofSubmoduleClosures,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
      Function.comp_def] using! hc
  have hcandidate : H.muCandidate P0 = ⨅ n : ℕ,
      quadraticEnergy H.energyBilin (responseCellMuCandidate P0 (ξ n)) := by
    rw [H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen, sInf_range]
    apply iInf_congr
    intro n
    simp [H, gen, responseCellMuCandidate, responseCellMuHilbert, responseCellMuSystem,
      PotentialSolenoidalL2Data.toAEEMuOperatorSystemData,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator]
  have hmu := Annealed.mu_eq_iInf_energy_for_responseSelection hvol k a P0
  have henergy : ∀ n : ℕ,
      quadraticEnergy H.energyBilin (responseCellMuCandidate P0 (ξ n)) =
        blockEnergyAverage U a.1
          (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
    intro n
    exact quadraticEnergy_responseCellMuCandidate hvol a P0 (ξ n)
  have hMuCandidate : Mu U P0 a.1 = H.muCandidate P0 := by
    calc
      Mu U P0 a.1 = ⨅ n : ℕ, blockEnergyAverage U a.1
          (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by simpa [ξ] using hmu
      _ = ⨅ n : ℕ, quadraticEnergy H.energyBilin
          (responseCellMuCandidate P0 (ξ n)) := (iInf_congr henergy).symm
      _ = H.muCandidate P0 := hcandidate.symm
  simpa [H, MuHilbertRealization.muCandidate, MuHilbertProblem.muCandidate,
    MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
    parameterAffineMinimizerMap] using! hMuCandidate

/-- Near-minimal fixed Galerkin competitors converge pointwise to the response-cell minimizer. -/
theorem tendsto_responseCellMuCandidate_selected
    {Om : Type*} [MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : 0 < (volume U).toReal) {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (P0 : BlockVec d) (ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U)
    (index : ℕ → Om → ℕ)
    (hindex : ∀ (m : ℕ) (w : Om),
      blockEnergyAverage U (A w).toFun
          (canonicalMuGeneratorAffineField (U := U) P0 (ξ (index m w))) ≤
        Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1))
    (w : Om) :
    Tendsto (fun m : ℕ ↦ responseCellMuCandidate P0 (ξ (index m w))) atTop
      (𝓝 ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0)) := by
  let a := responseSliceOf hSlice w
  let H := responseCellMuHilbert hvol a
  have hmem : ∀ m : ℕ,
      responseCellMuCandidate P0 (ξ (index m w)) - H.constantField P0 ∈
        H.correctionSpace.correctionSpace := fun m ↦
    responseCellMuCandidate_sub_constant_mem hvol a P0 (ξ (index m w))
  have heps : Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear : ∀ m : ℕ,
      quadraticEnergy H.energyBilin (responseCellMuCandidate P0 (ξ (index m w))) ≤
        quadraticEnergy H.energyBilin (affineMinimizerMap H.correctionSpace.correctionSpace
          H.energyBilin H.energyCoercive (H.constantField P0)) + 1 / ((m : ℝ) + 1) := by
    intro m
    have hmin := responseMu_eq_quadraticEnergy_minimizer hvol a P0
    calc
      quadraticEnergy H.energyBilin (responseCellMuCandidate P0 (ξ (index m w))) =
          blockEnergyAverage U (A w).toFun
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ (index m w))) := by
        simpa [H, a, responseSliceOf] using
          quadraticEnergy_responseCellMuCandidate hvol a P0 (ξ (index m w))
      _ ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := hindex m w
      _ = quadraticEnergy H.energyBilin
          (affineMinimizerMap H.correctionSpace.correctionSpace H.energyBilin
            H.energyCoercive (H.constantField P0)) + 1 / ((m : ℝ) + 1) := by
        simpa [H, a, responseSliceOf, MuHilbertRealization.minimizerMap,
          MuHilbertProblem.minimizerMap, parameterAffineMinimizerMap] using!
          congrArg (fun r : ℝ ↦ r + 1 / ((m : ℝ) + 1)) hmin
  change Tendsto (fun m : ℕ ↦ responseCellMuCandidate P0 (ξ (index m w))) atTop
    (𝓝 (H.minimizerMap P0))
  rw [show H.minimizerMap P0 = affineMinimizerMap H.correctionSpace.correctionSpace
      H.energyBilin H.energyCoercive (H.constantField P0) by rfl]
  exact tendsto_of_quadraticEnergy_le_min_add_eps H.correctionSpace.correctionSpace
    H.energyCoercive H.energySymm (H.constantField P0) hmem heps hnear

/-- The doubled `Mu` minimizer on a general positive-volume open cell is strongly measurable in
any regular-field parameter whose supported smooth entry tests are measurable on one quantitative
ellipticity slice. -/
theorem stronglyMeasurable_responseCellMuMinimizer
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (P0 : BlockVec d) :
    StronglyMeasurable fun w : Om ↦
      (responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0 := by
  classical
  have hF := measurable_toHilbertMatrixL2_carrier (A := A) (hSlice := hSlice)
    hUopen.measurableSet hEntry hUopen hUfin
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq _
  let energy : Om → ℕ → ℝ := fun w n ↦
    blockEnergyAverage U (A w).toFun
      (canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
  have henergyMeas : ∀ n : ℕ, Measurable fun w ↦ energy w n := by
    intro n
    exact measurable_blockEnergyAverage_carrier hF
      (canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
      (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))
  have hMuEq : (fun w ↦ Mu U P0 (A w).toFun) = fun w ↦ ⨅ n : ℕ, energy w n := by
    funext w
    simpa [energy, ξ] using!
      Annealed.mu_eq_iInf_energy_for_responseSelection hvol k
        (responseSliceOf hSlice w) P0
  have hMuMeas : Measurable fun w ↦ Mu U P0 (A w).toFun := by
    rw [hMuEq]
    exact Measurable.iInf henergyMeas
  have hexists : ∀ m : ℕ, ∀ w : Om,
      ∃ n : ℕ, energy w n ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := by
    intro m w
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hlt : (⨅ n : ℕ, energy w n) <
        (⨅ n : ℕ, energy w n) + 1 / ((m : ℝ) + 1) :=
      lt_add_of_le_of_pos le_rfl hpos
    rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
    refine ⟨n, le_of_lt ?_⟩
    rw [congrFun hMuEq w]
    exact hn
  let index : ℕ → Om → ℕ := fun m w ↦ Nat.find (hexists m w)
  have hgood : ∀ m n : ℕ,
      MeasurableSet {w : Om | energy w n ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1)} := by
    intro m n
    exact measurableSet_le (henergyMeas n) (hMuMeas.add measurable_const)
  have hindex : ∀ m : ℕ, Measurable (index m) := fun m ↦ by
    simpa [index] using measurable_find (hexists m) (hgood m)
  have happrox : ∀ m : ℕ, StronglyMeasurable fun w : Om ↦
      responseCellMuCandidate P0 (ξ (index m w)) := by
    intro m
    have hdisc : StronglyMeasurable fun n : ℕ ↦ responseCellMuCandidate P0 (ξ n) :=
      StronglyMeasurable.of_discrete
    simpa [Function.comp_def] using hdisc.comp_measurable (hindex m)
  refine stronglyMeasurable_of_tendsto atTop happrox ?_
  rw [tendsto_pi_nhds]
  intro w
  let a := responseSliceOf hSlice w
  let H := responseCellMuHilbert hvol a
  have hmem : ∀ m : ℕ,
      responseCellMuCandidate P0 (ξ (index m w)) - H.constantField P0 ∈
        H.correctionSpace.correctionSpace := fun m ↦
    responseCellMuCandidate_sub_constant_mem hvol a P0 (ξ (index m w))
  have heps : Tendsto (fun m : ℕ ↦ 1 / ((m : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hnear : ∀ m : ℕ,
      quadraticEnergy H.energyBilin (responseCellMuCandidate P0 (ξ (index m w))) ≤
        quadraticEnergy H.energyBilin (affineMinimizerMap H.correctionSpace.correctionSpace
          H.energyBilin H.energyCoercive (H.constantField P0)) + 1 / ((m : ℝ) + 1) := by
    intro m
    have hg := Nat.find_spec (hexists m w)
    have hqe := quadraticEnergy_responseCellMuCandidate hvol a P0 (ξ (index m w))
    have hmin := responseMu_eq_quadraticEnergy_minimizer hvol a P0
    calc
      quadraticEnergy H.energyBilin (responseCellMuCandidate P0 (ξ (index m w))) =
          energy w (index m w) := by simpa [H, a, energy]
      _ ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := hg
      _ = quadraticEnergy H.energyBilin
          (affineMinimizerMap H.correctionSpace.correctionSpace H.energyBilin
            H.energyCoercive (H.constantField P0)) + 1 / ((m : ℝ) + 1) := by
        simpa [H, a, responseSliceOf, MuHilbertRealization.minimizerMap,
          MuHilbertProblem.minimizerMap, parameterAffineMinimizerMap] using!
          congrArg (fun r : ℝ ↦ r + 1 / ((m : ℝ) + 1)) hmin
  change Tendsto (fun m : ℕ ↦ responseCellMuCandidate P0 (ξ (index m w))) atTop
    (𝓝 (H.minimizerMap P0))
  rw [show H.minimizerMap P0 = affineMinimizerMap H.correctionSpace.correctionSpace
      H.energyBilin H.energyCoercive (H.constantField P0) by rfl]
  exact tendsto_of_quadraticEnergy_le_min_add_eps H.correctionSpace.correctionSpace
    H.energyCoercive H.energySymm (H.constantField P0) hmem heps hnear

/-- Every fixed Hilbert-space coordinate of the general-cell minimizer is measurable. -/
theorem measurable_inner_responseCellMuMinimizer
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (P0 : BlockVec d) (y : HilbertBlockL2 U) :
    Measurable fun w : Om ↦ inner ℝ y
      ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
  have hstrong := stronglyMeasurable_responseCellMuMinimizer
    hUopen hUfin hvol hSlice hEntry P0
  have hcomp : StronglyMeasurable fun w : Om ↦ inner ℝ y
      ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
    simpa [Function.comp_def, innerSL_apply_apply] using
      (innerSL ℝ y).continuous.comp_stronglyMeasurable hstrong
  exact hcomp.measurable

/-- Continuous sample-dependent readouts transfer from fixed Galerkin competitors to the
response-cell minimizer. -/
theorem measurable_readout_responseCellMuMinimizer
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (P0 : BlockVec d) {R : Om → HilbertBlockL2 U → ℝ}
    (hRcont : ∀ w : Om, Continuous (R w))
    (hRmeas : ∀ Y : canonicalMuBlockCorrectionGeneratorSubmodule U,
      Measurable fun w : Om ↦ R w (responseCellMuCandidate P0 Y)) :
    Measurable fun w : Om ↦
      R w ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
  classical
  have hF := measurable_toHilbertMatrixL2_carrier (A := A) (hSlice := hSlice)
    hUopen.measurableSet hEntry hUopen hUfin
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq _
  let energy : Om → ℕ → ℝ := fun w n ↦ blockEnergyAverage U (A w).toFun
    (canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
  have henergyMeas : ∀ n : ℕ, Measurable fun w ↦ energy w n := by
    intro n
    exact measurable_blockEnergyAverage_carrier hF
      (canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
      (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))
  have hMuEq : (fun w ↦ Mu U P0 (A w).toFun) = fun w ↦ ⨅ n : ℕ, energy w n := by
    funext w
    simpa [energy, ξ] using!
      Annealed.mu_eq_iInf_energy_for_responseSelection hvol k
        (responseSliceOf hSlice w) P0
  have hMuMeas : Measurable fun w ↦ Mu U P0 (A w).toFun := by
    rw [hMuEq]
    exact Measurable.iInf henergyMeas
  have hexists : ∀ m : ℕ, ∀ w : Om,
      ∃ n : ℕ, energy w n ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1) := by
    intro m w
    have hlt : (⨅ n : ℕ, energy w n) <
        (⨅ n : ℕ, energy w n) + 1 / ((m : ℝ) + 1) := by
      exact lt_add_of_le_of_pos le_rfl (by positivity)
    rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
    refine ⟨n, le_of_lt ?_⟩
    rw [congrFun hMuEq w]
    exact hn
  have hgood : ∀ m n : ℕ,
      MeasurableSet {w : Om | energy w n ≤ Mu U P0 (A w).toFun + 1 / ((m : ℝ) + 1)} := by
    intro m n
    exact measurableSet_le (henergyMeas n) (hMuMeas.add measurable_const)
  let index : ℕ → Om → ℕ := fun m w ↦ Nat.find (hexists m w)
  have hselected : ∀ m : ℕ, Measurable fun w : Om ↦
      R w (responseCellMuCandidate P0 (ξ (index m w))) := by
    intro m
    exact Measurable.find
      (f := fun n w ↦ R w (responseCellMuCandidate P0 (ξ n)))
      (fun n ↦ hRmeas (ξ n)) (hgood m) (hexists m)
  refine measurable_of_tendsto_metrizable hselected ?_
  rw [tendsto_pi_nhds]
  intro w
  exact (hRcont w).tendsto _ |>.comp
    (tendsto_responseCellMuCandidate_selected hvol hSlice P0 ξ index
      (fun m w ↦ Nat.find_spec (hexists m w)) w)

/-- A fixed pair of block states has measurable coefficient-weighted pairing on the slice. -/
theorem measurable_blockPairingAverage_responseCell
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (X Y : BlockState d) (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval) :
    Measurable fun w : Om ↦ blockPairingAverage U (A w).toFun X Y := by
  have hF := measurable_toHilbertMatrixL2_carrier (A := A) (hSlice := hSlice)
    hUopen.measurableSet hEntry hUopen hUfin
  exact measurable_blockPairingAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := fun w ↦ (A w).toFun) (X := X) (Y := Y)
    (fun w α β ↦
      (hSlice w).integrableOn_pairingWeightedFullBlockCoeffEntry_of_memBlockL2 hX hY α β)
    (fun α β ↦ measurable_integrableWeightedFullBlockCoeffEntry_carrier hF
      (integrable_blockPairingEntryWeight_of_memBlockL2 hX hY α β) α β)

/-- The energy pairing against a fixed state, evaluated at a Galerkin competitor, is the
corresponding block pairing average. -/
theorem energyBilin_responseCellMuCandidate_eq_blockPairingAverage
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ}
    (hvol : 0 < (volume U).toReal)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}) (P0 : BlockVec d)
    {Y : BlockState d} (hY : MemBlockL2 U Y.eval)
    (Z : canonicalMuBlockCorrectionGeneratorSubmodule U) :
    (responseCellMuHilbert hvol a).energyBilin
        (toHilbertBlockL2OfBlockField (U := U) hY) (responseCellMuCandidate P0 Z) =
      blockPairingAverage U a.1 (canonicalMuGeneratorAffineField (U := U) P0 Z) Y := by
  rw [responseCellMuCandidate,
    ← canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 Z]
  simpa [responseCellMuHilbert, responseCellMuSystem,
    AEEMuOperatorSystemData.toMuHilbertRealization,
    MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
    (responseCellMuSystem hvol a).toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
      (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Z) hY

/-- The coefficient-dependent doubled energy pairing of the minimizer against a fixed block state
is measurable. -/
theorem measurable_energyBilin_responseCellMuMinimizer
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Set (Vec d)} {k : ℕ}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfin : volume U ≠ ⊤) (hvol : 0 < (volume U).toReal)
    {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice U k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (P0 : BlockVec d) {Y : BlockState d} (hY : MemBlockL2 U Y.eval) :
    Measurable fun w : Om ↦
      (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
        (toHilbertBlockL2OfBlockField (U := U) hY)
        ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
  refine measurable_readout_responseCellMuMinimizer hUopen hUfin hvol hSlice hEntry P0
    (R := fun w z ↦ (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
      (toHilbertBlockL2OfBlockField (U := U) hY) z)
    (fun w ↦ ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
      (toHilbertBlockL2OfBlockField (U := U) hY)).continuous) ?_
  intro Z
  have heq : (fun w : Om ↦
      (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
        (toHilbertBlockL2OfBlockField (U := U) hY) (responseCellMuCandidate P0 Z)) =
      fun w ↦ blockPairingAverage U (A w).toFun
        (canonicalMuGeneratorAffineField (U := U) P0 Z) Y := by
    funext w
    exact energyBilin_responseCellMuCandidate_eq_blockPairingAverage
      hvol (responseSliceOf hSlice w) P0 hY Z
  rw [heq]
  exact measurable_blockPairingAverage_responseCell hUopen hUfin hSlice hEntry _ Y
    (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Z) hY

end

end Homogenization.HighContrast.Multiscale
