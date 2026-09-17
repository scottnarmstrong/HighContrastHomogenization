import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffQuadConnect
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffWeightedQuadMeas
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra

/-!
# Measurability of the cutoff-weighted quadratic readout of the canonical optimizer

The cutoff pairing of the response estimate `e.response.cutoff.estimate` expands, in the notation of
AK.HC Lemma A.1, (A.4), into one quadratic term and three linear terms.  The quadratic term is the
cutoff-weighted volume average of the Euclidean pairing of the two slots of the canonical optimizer
state,

`a ↦ ⨍_{adaptedCell} φ · ⟨Z(a).1, Z(a).2⟩`.

The canonical optimizer state is not the Chapter-2 doubled minimizer: the almost-everywhere
extraction identity reads `Z(a).α = X(a).α + (B_a X(a)).α.swap`.  The cutoff-weighted pairing of `Z`
is therefore the cutoff-weighted block energy of the minimizer together with twice the plain pairing
of the minimizer.  Reading the canonical state directly as the minimizer loses the weighted energy,
so the quadratic readout is *not* the manifestly continuous functional `z ↦ ⨍ φ ⟨z₁, z₂⟩`.

This file proves the measurability of the quadratic readout in the coefficient sample for the two
recentred response coefficient families of `e.response.cutoff.estimate`, with no hypothesis beyond
the cutoff class.  The proof runs the Galerkin selection machine on the response cell with the
continuous readout

`z ↦ ⨍ ⟨z, B_a z⟩ + 2 · ⨍ φ ⟨z₁, z₂⟩`,

whose first summand is the doubled energy bilinear form of the slice evaluated on `z` and its
pointwise `φ`-multiple (continuous by `continuous_weightedEnergy_add_cutoffQuadReadout`), and whose
second summand is the continuous `cutoffQuadReadout`.  The almost-everywhere extraction identity of
`HC3_CutoffWeightedQuadMeas` identifies this readout on the minimizer with the canonical quadratic
readout.  The two statements are exactly the `hquadMinus`/`hquadPlus` hypotheses under which
`aestronglyMeasurable_abs_pairing_of_maximizer` closes the measurability of the cutoff pairing.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A block state whose two slots are multiplied pointwise by a scalar field.  This is the
algebraic packaging of the `φ`-weighted block field used by the weighted energy term of the cutoff
quadratic readout. -/
private def blockStateSmulField (φ : Vec d → ℝ) (X : BlockState d) : BlockState d where
  potential := fun x => φ x • X.potential x
  flux := fun x => φ x • X.flux x

/-- The pointwise scalar multiple of a block state evaluates to the scalar multiple of its
evaluation. -/
@[simp] private theorem blockStateSmulField_eval (φ : Vec d → ℝ) (X : BlockState d) (x : Vec d) :
    (blockStateSmulField φ X).eval x = φ x • X.eval x := rfl

/-- A block state whose two slots are multiplied by an essentially bounded scalar field is square
integrable.  This is the pointwise-multiplication input for the weighted energy term of the cutoff
quadratic readout. -/
private theorem memBlockL2_blockStateSmulField {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2)
    {X : BlockState d} (hX : MemBlockL2 U X.eval) :
    MemBlockL2 U (blockStateSmulField φ X).eval := by
  have heq : (blockStateSmulField φ X).eval = fun x => φ x • X.eval x := by
    funext x
    rw [blockStateSmulField_eval]
  rw [heq]
  refine MemLp.of_le_mul (c := 2) hX (hφm.smul hX.aestronglyMeasurable) ?_
  filter_upwards [hφb] with x hx
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- The promotion of an algebraic doubled vector into the Euclidean Hilbert carrier intertwines
scalar multiplication. -/
private theorem ofBlockVec_smul (c : ℝ) (v : BlockVec d) :
    HilbertBlockVec.ofBlockVec (c • v) = c • HilbertBlockVec.ofBlockVec v := by
  rw [← HilbertBlockVec.continuousLinearEquivBlockVec_symm_apply, map_smul,
    HilbertBlockVec.continuousLinearEquivBlockVec_symm_apply]

/-- Pointwise multiplication of a block field by an essentially bounded scalar field coincides, on
the ambient doubled `L²` space, with pointwise multiplication of its Hilbert promotion. -/
private theorem weightedBlockSMulL_toHilbertBlockL2OfBlockField {U : Set (Vec d)}
    {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn U))
    (hφb : ∀ᵐ x ∂volumeMeasureOn U, ‖φ x‖ ≤ 2)
    {X : BlockState d} (hX : MemBlockL2 U X.eval) :
    weightedBlockSMulL hφm hφb (toHilbertBlockL2OfBlockField (U := U) hX) =
      toHilbertBlockL2OfBlockField (U := U) (memBlockL2_blockStateSmulField hφm hφb hX) := by
  apply Lp.ext
  filter_upwards [coeFn_weightedBlockSMulL hφm hφb (toHilbertBlockL2OfBlockField (U := U) hX),
    coeFn_toHilbertBlockL2OfBlockField (U := U) hX,
    coeFn_toHilbertBlockL2OfBlockField (U := U)
      (memBlockL2_blockStateSmulField hφm hφb hX)]
    with x h1 h2 h3
  rw [h1, h2, h3]
  simp only [hilbertifyBlockField]
  rw [blockStateSmulField_eval, ofBlockVec_smul]

/-- On one quantitative ellipticity slice, the cutoff-weighted quadratic readout of the canonical
optimizer state is measurable in the sample.  The canonical state is recovered from the doubled
minimizer of the slice through the almost-everywhere extraction identity, and the resulting readout
is continuous on the minimizer because the doubled energy form is a continuous bilinear form. -/
private theorem measurable_cutoffQuad_canonical_of_fixedSlice
    {Om : Type*} [MeasurableSpace Om] {U : Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))] {k : ℕ}
    (hUopen : IsOpen (U : Set (Vec d))) (hUfin : volume (U : Set (Vec d)) ≠ ⊤)
    (hvol : 0 < (volume (U : Set (Vec d))).toReal) {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Vec d)) →
        Measurable fun w : Om ↦ entryTestR i j φ (A w))
    (aU : Om → Book.Ch02.CoeffOn U) (haU : ∀ w : Om, (aU w).toCoeffField = (A w).toFun)
    (p r : Vec d) {φ : Vec d → ℝ}
    (hφm : AEStronglyMeasurable φ (volumeMeasureOn (U : Set (Vec d))))
    (hφb : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)), ‖φ x‖ ≤ 2) :
    Measurable fun w : Om ↦ volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * vecDot
      (canonicalOptimizerBlockState U (aU w) p r x).1
      (canonicalOptimizerBlockState U (aU w) p r x).2) := by
  classical
  let P0 : BlockVec d := (-p, r)
  let R : Om → HilbertBlockL2 (U : Set (Vec d)) → ℝ := fun w z ↦
    (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
        (weightedBlockSMulL hφm hφb z) z +
      2 * cutoffQuadReadout (U : Set (Vec d)) φ z
  have hRcont : ∀ w : Om, Continuous (R w) := fun w ↦
    continuous_weightedEnergy_add_cutoffQuadReadout (U := (U : Set (Vec d))) hvol
      (responseSliceOf hSlice w) hφm hφb
  have hRmeas : ∀ Y : canonicalMuBlockCorrectionGeneratorSubmodule (U : Set (Vec d)),
      Measurable fun w : Om ↦
        R w (responseCellMuCandidate (U := (U : Set (Vec d))) P0 Y) := by
    intro Y
    let Xc : BlockState d :=
      canonicalMuGeneratorAffineField (U := (U : Set (Vec d))) P0 Y
    have hXc : MemBlockL2 (U : Set (Vec d)) Xc.eval :=
      canonicalMuGeneratorAffineField_memBlockL2 (U := (U : Set (Vec d))) P0 Y
    have hφXc : MemBlockL2 (U : Set (Vec d)) (blockStateSmulField φ Xc).eval :=
      memBlockL2_blockStateSmulField hφm hφb hXc
    have hcand : toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXc =
        responseCellMuCandidate (U := (U : Set (Vec d))) P0 Y :=
      canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := (U : Set (Vec d))) P0 Y
    have hsmul := weightedBlockSMulL_toHilbertBlockL2OfBlockField hφm hφb hXc
    have hE : ∀ w : Om,
        (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hφXc)
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXc) =
        blockPairingAverage (U : Set (Vec d)) (A w).toFun Xc (blockStateSmulField φ Xc) := by
      intro w
      simpa [responseCellMuHilbert, responseCellMuSystem, responseSliceOf,
        AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        (responseCellMuSystem hvol (responseSliceOf hSlice w)).toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
          hXc hφXc
    have henergy : Measurable fun w : Om ↦
        (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hφXc)
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXc) := by
      rw [show (fun w : Om ↦
          (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hφXc)
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXc)) =
            fun w : Om ↦
              blockPairingAverage (U : Set (Vec d)) (A w).toFun Xc (blockStateSmulField φ Xc)
          from funext hE]
      exact measurable_blockPairingAverage_responseCell hUopen hUfin hSlice hEntry
        Xc (blockStateSmulField φ Xc) hXc hφXc
    have hconst : Measurable fun _ : Om ↦
        (2 : ℝ) * cutoffQuadReadout (U : Set (Vec d)) φ
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXc) := measurable_const
    have hgoal : (fun w : Om ↦
          R w (responseCellMuCandidate (U := (U : Set (Vec d))) P0 Y)) =
        fun w : Om ↦
          (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
              (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hφXc)
              (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXc) +
            2 * cutoffQuadReadout (U : Set (Vec d)) φ
              (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXc) := by
      funext w
      simp only [R]
      rw [← hcand, hsmul]
    rw [hgoal]
    exact henergy.add hconst
  have hfun : (fun w : Om ↦ volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * vecDot
        (canonicalOptimizerBlockState U (aU w) p r x).1
        (canonicalOptimizerBlockState U (aU w) p r x).2)) =
      fun w : Om ↦ R w
        ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
    funext w
    have hkw : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (aU w).toCoeffField := by
      rw [haU w]
      exact hSlice w
    obtain ⟨X, hX⟩ := (Book.Ch02.doubledMuTheory U (aU w)).minimizer_exists P0
    let Xb : BlockState d := { potential := X.potential, flux := X.flux }
    have hXb : IsBlockMuAdmissible (U : Set (Vec d)) P0 Xb :=
      isBlockMuAdmissible_of_bookDoubledMuAdmissible hX.1
    have hXbMem : MemBlockL2 (U : Set (Vec d)) Xb.eval := hXb.memBlockL2_eval
    have hEqSlice : (⟨(aU w).toCoeffField, hkw⟩ :
        {b : CoeffField d // AEEQuantitativeEllipticSlice (U : Set (Vec d)) k b}) =
        responseSliceOf hSlice w := Subtype.ext (haU w)
    have hMin : toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXbMem =
        (responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0 := by
      have h := toHilbertBlockL2_eq_responseMinimizer_of_isDoubledMuMinimizer
        hvol hkw P0 hX hXb
      rw [hEqSlice] at h
      simpa using h
    have hEll : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
        IsEllipticMatrix ((k + 1 : ℝ)⁻¹) (k + 1 : ℝ) ((aU w).toCoeffField x) := by
      filter_upwards [hkw.2.2] with x hx
      exact hx
    have hxy := ae_vecDot_canonicalOptimizerBlockState_eq_blockVecDot (U := U)
      (aU := aU w) hEll p r hX
    have hZ : (fun x ↦ φ x * vecDot
          (canonicalOptimizerBlockState U (aU w) p r x).1
          (canonicalOptimizerBlockState U (aU w) p r x).2)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        (fun x ↦ φ x * blockVecDot (Xb.eval x)
            (blockMatVecMul (blockCoeffField (aU w).toCoeffField x) (Xb.eval x)))
          + (fun x ↦ 2 * (φ x * vecDot (Xb.eval x).1 (Xb.eval x).2)) := by
      filter_upwards [hxy] with x hx
      rw [hx]
      simp only [Pi.add_apply, Xb, BlockState.eval, Book.Ch02.DoubledField.eval]
      ring
    have hIntB : IntegrableOn (fun x ↦ φ x * blockVecDot (Xb.eval x)
        (blockMatVecMul (blockCoeffField (aU w).toCoeffField x) (Xb.eval x)))
        (U : Set (Vec d)) :=
      (integrableOn_blockPairingIntegrand_of_responseSlice (X := Xb) (Y := Xb)
        hkw hXbMem hXbMem).bdd_mul hφm hφb
    have hIntC : IntegrableOn
        (fun x ↦ 2 * (φ x * vecDot (Xb.eval x).1 (Xb.eval x).2))
        (U : Set (Vec d)) := by
      have h' : IntegrableOn (fun x ↦ φ x * vecDot (Xb.eval x).1 (Xb.eval x).2)
          (U : Set (Vec d)) :=
        (integrableOn_vecDot_of_memVectorL2
          (memVectorL2_fst_of_memBlockL2 hXbMem)
          (memVectorL2_snd_of_memBlockL2 hXbMem)).bdd_mul hφm hφb
      exact h'.const_mul 2
    have hsplit : volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * vecDot
          (canonicalOptimizerBlockState U (aU w) p r x).1
          (canonicalOptimizerBlockState U (aU w) p r x).2) =
        volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * blockVecDot (Xb.eval x)
            (blockMatVecMul (blockCoeffField (aU w).toCoeffField x) (Xb.eval x))) +
          volumeAverage (U : Set (Vec d))
            (fun x ↦ 2 * (φ x * vecDot (Xb.eval x).1 (Xb.eval x).2)) := by
      have hcongr : volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * vecDot
            (canonicalOptimizerBlockState U (aU w) p r x).1
            (canonicalOptimizerBlockState U (aU w) p r x).2) =
          volumeAverage (U : Set (Vec d))
            ((fun x ↦ φ x * blockVecDot (Xb.eval x)
                (blockMatVecMul (blockCoeffField (aU w).toCoeffField x) (Xb.eval x))) +
              (fun x ↦ 2 * (φ x * vecDot (Xb.eval x).1 (Xb.eval x).2))) := by
        unfold volumeAverage
        rw [integral_congr_ae hZ]
      rw [hcongr, volumeAverage_add hIntB hIntC]
    have hcross : volumeAverage (U : Set (Vec d))
          (fun x ↦ 2 * (φ x * vecDot (Xb.eval x).1 (Xb.eval x).2)) =
        2 * cutoffQuadReadout (U : Set (Vec d)) φ
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXbMem) := by
      rw [cutoffQuadReadout_toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) Xb hXbMem]
      have hsm : (fun x ↦ 2 * (φ x * vecDot (Xb.eval x).1 (Xb.eval x).2)) =
          (2 : ℝ) • (fun x ↦ φ x * vecDot (Xb.potential x) (Xb.flux x)) := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul, BlockState.eval]
      rw [hsm, volumeAverage_smul]
    have hba : blockPairingAverage (U : Set (Vec d)) (aU w).toCoeffField
          Xb (blockStateSmulField φ Xb) =
        volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * blockVecDot (Xb.eval x)
            (blockMatVecMul (blockCoeffField (aU w).toCoeffField x) (Xb.eval x))) := by
      unfold blockPairingAverage
      refine congrArg (volumeAverage (U : Set (Vec d))) ?_
      funext x
      simp only [blockPairingIntegrand, blockStateSmulField_eval, blockMatVecMul_smul,
        blockVecDot_smul_right]
    have hφXb : MemBlockL2 (U : Set (Vec d)) (blockStateSmulField φ Xb).eval :=
      memBlockL2_blockStateSmulField hφm hφb hXbMem
    have henergy : volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * blockVecDot (Xb.eval x)
            (blockMatVecMul (blockCoeffField (aU w).toCoeffField x) (Xb.eval x))) =
        (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
          (weightedBlockSMulL hφm hφb
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXbMem))
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXbMem) := by
      have hsmulB := weightedBlockSMulL_toHilbertBlockL2OfBlockField hφm hφb hXbMem
      have hmain : (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hφXb)
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXbMem) =
          volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * blockVecDot (Xb.eval x)
              (blockMatVecMul (blockCoeffField (aU w).toCoeffField x) (Xb.eval x))) := by
        rw [← hba]
        simpa [responseCellMuHilbert, responseCellMuSystem, responseSliceOf, haU w,
          AEEMuOperatorSystemData.toMuHilbertRealization,
          MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
          (responseCellMuSystem hvol (responseSliceOf hSlice w)).toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
            hXbMem hφXb
      rw [← hmain, hsmulB]
    calc
      volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * vecDot
            (canonicalOptimizerBlockState U (aU w) p r x).1
            (canonicalOptimizerBlockState U (aU w) p r x).2)
          = volumeAverage (U : Set (Vec d)) (fun x ↦ φ x * blockVecDot (Xb.eval x)
                (blockMatVecMul (blockCoeffField (aU w).toCoeffField x) (Xb.eval x))) +
              volumeAverage (U : Set (Vec d))
                (fun x ↦ 2 * (φ x * vecDot (Xb.eval x).1 (Xb.eval x).2)) := hsplit
      _ = (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
              (weightedBlockSMulL hφm hφb
                (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXbMem))
              (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXbMem) +
            2 * cutoffQuadReadout (U : Set (Vec d)) φ
              (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hXbMem) := by
            rw [henergy, hcross]
      _ = (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
              (weightedBlockSMulL hφm hφb
                ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0))
              ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) +
            2 * cutoffQuadReadout (U : Set (Vec d)) φ
              ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
            rw [hMin]
      _ = R w ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap P0) := by
            simp only [R]
  rw [hfun]
  exact measurable_readout_responseCellMuMinimizer hUopen hUfin hvol hSlice hEntry
    P0 hRcont hRmeas

/-- The cutoff-weighted quadratic readout of the canonical minus optimizer state of
`e.response.cutoff.estimate` is measurable in the coefficient sample, with no hypothesis beyond the
cutoff class.  This is the `hquadMinus` hypothesis of the family reduction of the cutoff pairing
(AK.HC Lemma A.1, (A.4)). -/
theorem measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffMinus_full [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x).1
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x).2) := by
  classical
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal :=
    adaptedCell_volume_toReal_pos q hq t
  have hφm : AEStronglyMeasurable φ (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hφ.contDiff.continuous.measurable.aestronglyMeasurable
  have hφb : ∀ᵐ x ∂volumeMeasureOn (HighContrast.adaptedCell q t), ‖φ x‖ ≤ 2 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  let A : CoeffSpace d → RegCoeffField d := fun a => selectionRespCoeffMinusReg F a
  let slice : ℕ → Set (CoeffSpace d) := fun k =>
    {a | AEEQuantitativeEllipticSlice (HighContrast.adaptedCell q t) k (A a).toFun}
  have hsliceMeas : ∀ k, MeasurableSet (slice k) := by
    intro k
    apply Annealed.measurableSet_aeeSlice_of_entryTest_response A hU.isOpen
    intro i j φ hφ'
    exact measurable_entryTest_selectionRespCoeffMinusReg F i j hφ'.contDiff hφ'.hasCompactSupport
  have hcoverU : ⋃ k, slice k = Set.univ := by
    ext a
    constructor
    · intro _
      exact Set.mem_univ a
    · intro _
      obtain ⟨k, hk⟩ := exists_responseSlice_selectionRespCoeffMinusReg q hq t F a
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
  let f : (k : ℕ) → slice k → ℝ := fun _ w => volumeAverage (HighContrast.adaptedCell q t)
    (fun x => φ x * vecDot
      (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F w.1) p r x).1
      (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F w.1) p r x).2)
  have hfmeas : ∀ k, Measurable (f k) := by
    intro k
    exact measurable_cutoffQuad_canonical_of_fixedSlice (Om := slice k)
      (U := adaptedDomain q hq t) hU.isOpen hU.volume_lt_top.ne hvol
      (A := fun w : slice k => selectionRespCoeffMinusReg F w.1)
      (fun w => w.2)
      (fun i j φ hcont hcpt _hs =>
        (measurable_entryTest_selectionRespCoeffMinusReg F i j hcont hcpt).comp
          measurable_subtype_coe)
      (fun w : slice k => canonicalRespCoeffMinusOn q hq t F w.1)
      (fun w => by
        rw [canonicalRespCoeffMinusOn_toFun, selectionRespCoeffMinusReg_toFun])
      p r hφm hφb
  have hagree : ∀ (i j : ℕ) (a : CoeffSpace d) (hi : a ∈ slice i) (hj : a ∈ slice j),
      f i ⟨a, hi⟩ = f j ⟨a, hj⟩ := fun _ _ _ _ _ => rfl
  have heq : (fun a : CoeffSpace d => volumeAverage (HighContrast.adaptedCell q t)
        (fun x => φ x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain q hq t)
            (canonicalRespCoeffMinusOn q hq t F a) p r x).1
          (canonicalOptimizerBlockState (adaptedDomain q hq t)
            (canonicalRespCoeffMinusOn q hq t F a) p r x).2)) =
      Set.liftCover slice f hagree hcoverU := by
    funext a
    have ha : a ∈ ⋃ k, slice k := by
      rw [hcoverU]
      exact Set.mem_univ a
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
    rw [Set.liftCover_of_mem (S := slice) (f := f) (hf := hagree) (hS := hcoverU)
      (i := k) hk]
  rw [heq]
  exact measurable_liftCover slice hsliceMeas f hfmeas hagree hcoverU

/-- The cutoff-weighted quadratic readout of the canonical plus optimizer state of
`e.response.cutoff.estimate` is measurable in the coefficient sample, with no hypothesis beyond the
cutoff class.  This is the `hquadPlus` hypothesis of the family reduction of the cutoff pairing
(AK.HC Lemma A.1, (A.4)). -/
theorem measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffPlus_full [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff q t φ) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => φ x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x).1
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x).2) := by
  classical
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal :=
    adaptedCell_volume_toReal_pos q hq t
  have hφm : AEStronglyMeasurable φ (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hφ.contDiff.continuous.measurable.aestronglyMeasurable
  have hφb : ∀ᵐ x ∂volumeMeasureOn (HighContrast.adaptedCell q t), ‖φ x‖ ≤ 2 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg x)]
    exact hφ.le_two x
  let A : CoeffSpace d → RegCoeffField d := fun a => selectionRespCoeffPlusReg F a
  let slice : ℕ → Set (CoeffSpace d) := fun k =>
    {a | AEEQuantitativeEllipticSlice (HighContrast.adaptedCell q t) k (A a).toFun}
  have hsliceMeas : ∀ k, MeasurableSet (slice k) := by
    intro k
    apply Annealed.measurableSet_aeeSlice_of_entryTest_response A hU.isOpen
    intro i j φ hφ'
    exact measurable_entryTest_selectionRespCoeffPlusReg F i j hφ'.contDiff hφ'.hasCompactSupport
  have hcoverU : ⋃ k, slice k = Set.univ := by
    ext a
    constructor
    · intro _
      exact Set.mem_univ a
    · intro _
      obtain ⟨k, hk⟩ := exists_responseSlice_selectionRespCoeffPlusReg q hq t F a
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
  let f : (k : ℕ) → slice k → ℝ := fun _ w => volumeAverage (HighContrast.adaptedCell q t)
    (fun x => φ x * vecDot
      (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F w.1) p r x).1
      (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F w.1) p r x).2)
  have hfmeas : ∀ k, Measurable (f k) := by
    intro k
    exact measurable_cutoffQuad_canonical_of_fixedSlice (Om := slice k)
      (U := adaptedDomain q hq t) hU.isOpen hU.volume_lt_top.ne hvol
      (A := fun w : slice k => selectionRespCoeffPlusReg F w.1)
      (fun w => w.2)
      (fun i j φ hcont hcpt _hs =>
        (measurable_entryTest_selectionRespCoeffPlusReg F i j hcont hcpt).comp
          measurable_subtype_coe)
      (fun w : slice k => canonicalRespCoeffPlusOn q hq t F w.1)
      (fun w => by
        rw [canonicalRespCoeffPlusOn_toFun, selectionRespCoeffPlusReg_toFun])
      p r hφm hφb
  have hagree : ∀ (i j : ℕ) (a : CoeffSpace d) (hi : a ∈ slice i) (hj : a ∈ slice j),
      f i ⟨a, hi⟩ = f j ⟨a, hj⟩ := fun _ _ _ _ _ => rfl
  have heq : (fun a : CoeffSpace d => volumeAverage (HighContrast.adaptedCell q t)
        (fun x => φ x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain q hq t)
            (canonicalRespCoeffPlusOn q hq t F a) p r x).1
          (canonicalOptimizerBlockState (adaptedDomain q hq t)
            (canonicalRespCoeffPlusOn q hq t F a) p r x).2)) =
      Set.liftCover slice f hagree hcoverU := by
    funext a
    have ha : a ∈ ⋃ k, slice k := by
      rw [hcoverU]
      exact Set.mem_univ a
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
    rw [Set.liftCover_of_mem (S := slice) (f := f) (hf := hagree) (hS := hcoverU)
      (i := k) hk]
  rw [heq]
  exact measurable_liftCover slice hsliceMeas f hfmeas hagree hcoverU

/-- The quadratic readout of the canonical minus optimizer state of `e.response.cutoff.estimate`
against an arbitrary essentially bounded weight is measurable in the coefficient sample.  The weight
is bounded by `2` in norm, which is the only property of the cutoff class that the fixed-slice
readout argument consumes; the statement is the `hquadMinus` hypothesis of the family reduction of
the cutoff pairing (AK.HC Lemma A.1, (A.4)). -/
theorem measurable_volumeAverage_weighted_quadratic_canonicalRespCoeffMinus [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    {eta : Vec d → ℝ}
    (hetam : AEStronglyMeasurable eta (volumeMeasureOn (HighContrast.adaptedCell q t)))
    (hetab : ∀ᵐ x ∂volumeMeasureOn (HighContrast.adaptedCell q t), ‖eta x‖ ≤ 2) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => eta x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x).1
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x).2) := by
  classical
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal :=
    adaptedCell_volume_toReal_pos q hq t
  let A : CoeffSpace d → RegCoeffField d := fun a => selectionRespCoeffMinusReg F a
  let slice : ℕ → Set (CoeffSpace d) := fun k =>
    {a | AEEQuantitativeEllipticSlice (HighContrast.adaptedCell q t) k (A a).toFun}
  have hsliceMeas : ∀ k, MeasurableSet (slice k) := by
    intro k
    apply Annealed.measurableSet_aeeSlice_of_entryTest_response A hU.isOpen
    intro i j φ hφ'
    exact measurable_entryTest_selectionRespCoeffMinusReg F i j hφ'.contDiff hφ'.hasCompactSupport
  have hcoverU : ⋃ k, slice k = Set.univ := by
    ext a
    constructor
    · intro _
      exact Set.mem_univ a
    · intro _
      obtain ⟨k, hk⟩ := exists_responseSlice_selectionRespCoeffMinusReg q hq t F a
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
  let f : (k : ℕ) → slice k → ℝ := fun _ w => volumeAverage (HighContrast.adaptedCell q t)
    (fun x => eta x * vecDot
      (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F w.1) p r x).1
      (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F w.1) p r x).2)
  have hfmeas : ∀ k, Measurable (f k) := by
    intro k
    exact measurable_cutoffQuad_canonical_of_fixedSlice (Om := slice k)
      (U := adaptedDomain q hq t) hU.isOpen hU.volume_lt_top.ne hvol
      (A := fun w : slice k => selectionRespCoeffMinusReg F w.1)
      (fun w => w.2)
      (fun i j φ hcont hcpt _hs =>
        (measurable_entryTest_selectionRespCoeffMinusReg F i j hcont hcpt).comp
          measurable_subtype_coe)
      (fun w : slice k => canonicalRespCoeffMinusOn q hq t F w.1)
      (fun w => by
        rw [canonicalRespCoeffMinusOn_toFun, selectionRespCoeffMinusReg_toFun])
      p r hetam hetab
  have hagree : ∀ (i j : ℕ) (a : CoeffSpace d) (hi : a ∈ slice i) (hj : a ∈ slice j),
      f i ⟨a, hi⟩ = f j ⟨a, hj⟩ := fun _ _ _ _ _ => rfl
  have heq : (fun a : CoeffSpace d => volumeAverage (HighContrast.adaptedCell q t)
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain q hq t)
            (canonicalRespCoeffMinusOn q hq t F a) p r x).1
          (canonicalOptimizerBlockState (adaptedDomain q hq t)
            (canonicalRespCoeffMinusOn q hq t F a) p r x).2)) =
      Set.liftCover slice f hagree hcoverU := by
    funext a
    have ha : a ∈ ⋃ k, slice k := by
      rw [hcoverU]
      exact Set.mem_univ a
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
    rw [Set.liftCover_of_mem (S := slice) (f := f) (hf := hagree) (hS := hcoverU)
      (i := k) hk]
  rw [heq]
  exact measurable_liftCover slice hsliceMeas f hfmeas hagree hcoverU

/-- The quadratic readout of the canonical plus optimizer state of `e.response.cutoff.estimate`
against an arbitrary essentially bounded weight is measurable in the coefficient sample.  The weight
is bounded by `2` in norm, which is the only property of the cutoff class that the fixed-slice
readout argument consumes; the statement is the `hquadPlus` hypothesis of the family reduction of
the cutoff pairing (AK.HC Lemma A.1, (A.4)). -/
theorem measurable_volumeAverage_weighted_quadratic_canonicalRespCoeffPlus [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (p r : Vec d)
    {eta : Vec d → ℝ}
    (hetam : AEStronglyMeasurable eta (volumeMeasureOn (HighContrast.adaptedCell q t)))
    (hetab : ∀ᵐ x ∂volumeMeasureOn (HighContrast.adaptedCell q t), ‖eta x‖ ≤ 2) :
    Measurable fun a : CoeffSpace d =>
      volumeAverage (HighContrast.adaptedCell q t) (fun x => eta x * vecDot
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x).1
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x).2) := by
  classical
  have hU : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    hU.isFiniteMeasure_restrict_volume
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal :=
    adaptedCell_volume_toReal_pos q hq t
  let A : CoeffSpace d → RegCoeffField d := fun a => selectionRespCoeffPlusReg F a
  let slice : ℕ → Set (CoeffSpace d) := fun k =>
    {a | AEEQuantitativeEllipticSlice (HighContrast.adaptedCell q t) k (A a).toFun}
  have hsliceMeas : ∀ k, MeasurableSet (slice k) := by
    intro k
    apply Annealed.measurableSet_aeeSlice_of_entryTest_response A hU.isOpen
    intro i j φ hφ'
    exact measurable_entryTest_selectionRespCoeffPlusReg F i j hφ'.contDiff hφ'.hasCompactSupport
  have hcoverU : ⋃ k, slice k = Set.univ := by
    ext a
    constructor
    · intro _
      exact Set.mem_univ a
    · intro _
      obtain ⟨k, hk⟩ := exists_responseSlice_selectionRespCoeffPlusReg q hq t F a
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
  let f : (k : ℕ) → slice k → ℝ := fun _ w => volumeAverage (HighContrast.adaptedCell q t)
    (fun x => eta x * vecDot
      (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F w.1) p r x).1
      (canonicalOptimizerBlockState (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F w.1) p r x).2)
  have hfmeas : ∀ k, Measurable (f k) := by
    intro k
    exact measurable_cutoffQuad_canonical_of_fixedSlice (Om := slice k)
      (U := adaptedDomain q hq t) hU.isOpen hU.volume_lt_top.ne hvol
      (A := fun w : slice k => selectionRespCoeffPlusReg F w.1)
      (fun w => w.2)
      (fun i j φ hcont hcpt _hs =>
        (measurable_entryTest_selectionRespCoeffPlusReg F i j hcont hcpt).comp
          measurable_subtype_coe)
      (fun w : slice k => canonicalRespCoeffPlusOn q hq t F w.1)
      (fun w => by
        rw [canonicalRespCoeffPlusOn_toFun, selectionRespCoeffPlusReg_toFun])
      p r hetam hetab
  have hagree : ∀ (i j : ℕ) (a : CoeffSpace d) (hi : a ∈ slice i) (hj : a ∈ slice j),
      f i ⟨a, hi⟩ = f j ⟨a, hj⟩ := fun _ _ _ _ _ => rfl
  have heq : (fun a : CoeffSpace d => volumeAverage (HighContrast.adaptedCell q t)
        (fun x => eta x * vecDot
          (canonicalOptimizerBlockState (adaptedDomain q hq t)
            (canonicalRespCoeffPlusOn q hq t F a) p r x).1
          (canonicalOptimizerBlockState (adaptedDomain q hq t)
            (canonicalRespCoeffPlusOn q hq t F a) p r x).2)) =
      Set.liftCover slice f hagree hcoverU := by
    funext a
    have ha : a ∈ ⋃ k, slice k := by
      rw [hcoverU]
      exact Set.mem_univ a
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ha
    rw [Set.liftCover_of_mem (S := slice) (f := f) (hf := hagree) (hS := hcoverU)
      (i := k) hk]
  rw [heq]
  exact measurable_liftCover slice hsliceMeas f hfmeas hagree hcoverU

end

end Homogenization.HighContrast.Multiscale
