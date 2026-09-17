import HCPoly.Entry.Multiscale.ResponseInputs.GalerkinSelection
import Homogenization.Book.Ch02.Theorems.DoubledMu

/-!
# Recovery of the canonical response optimizer from the doubled minimizer
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

theorem inner_toHilbertBlockL2OfBlockField_eq_integral_response
    {U : Set (Vec d)} {F G : Vec d → BlockVec d}
    (hF : MemBlockL2 U F) (hG : MemBlockL2 U G) :
    inner ℝ (toHilbertBlockL2OfBlockField (U := U) hF)
        (toHilbertBlockL2OfBlockField (U := U) hG) =
      ∫ x in U, blockVecDot (F x) (G x) ∂volume := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (U := U) hF,
    coeFn_toHilbertBlockL2OfBlockField (U := U) hG] with x hx hy
  rw [hx, hy]
  simp [hilbertifyBlockField]

/-- Test state selecting a weighted potential coordinate. -/
def responseGradTestState (η : Vec d → ℝ) (i : Fin d) : BlockState d where
  potential := fun x ↦ η x • basisVec i
  flux := fun _ ↦ 0

/-- Test state selecting a weighted flux coordinate. -/
def responseFluxTestState (η : Vec d → ℝ) (i : Fin d) : BlockState d where
  potential := fun _ ↦ 0
  flux := fun x ↦ η x • basisVec i

theorem memVectorL2_smul_basisVec_response {U : Set (Vec d)} {η : Vec d → ℝ}
    (hη : MemScalarL2 U η) (i : Fin d) :
    MemVectorL2 U (fun x ↦ η x • basisVec i) := by
  have hcomp :=
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec (d := d) i)).lipschitz).comp_memLp
      (by simp) hη
  simpa [Function.comp_def] using hcomp

theorem responseGradTestState_memBlockL2
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {η : Vec d → ℝ}
    (hη : MemScalarL2 U η) (i : Fin d) : MemBlockL2 U (responseGradTestState η i).eval :=
  MeasureTheory.MemLp.of_fst_snd
    ⟨memVectorL2_smul_basisVec_response hη i, MeasureTheory.memLp_const (0 : Vec d)⟩

theorem responseFluxTestState_memBlockL2
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {η : Vec d → ℝ}
    (hη : MemScalarL2 U η) (i : Fin d) : MemBlockL2 U (responseFluxTestState η i).eval :=
  MeasureTheory.MemLp.of_fst_snd
    ⟨MeasureTheory.memLp_const (0 : Vec d), memVectorL2_smul_basisVec_response hη i⟩

/-- Fixed test state for a weighted doubled coordinate. -/
def responseBlockTestState (η : Vec d → ℝ) : BlockCoord d → BlockState d
  | Sum.inl i => responseGradTestState η i
  | Sum.inr i => responseFluxTestState η i

theorem responseBlockTestState_memBlockL2
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {η : Vec d → ℝ}
    (hη : MemScalarL2 U η) (α : BlockCoord d) :
    MemBlockL2 U (responseBlockTestState η α).eval := by
  cases α with
  | inl i => exact responseGradTestState_memBlockL2 hη i
  | inr i => exact responseFluxTestState_memBlockL2 hη i

theorem blockVecDot_responseBlockTestState (η : Vec d → ℝ) (α : BlockCoord d)
    (Z : BlockVec d) (x : Vec d) :
    blockVecDot ((responseBlockTestState η α).eval x) Z =
      η x * toFullBlockVec Z α := by
  cases α with
  | inl i =>
      simp [responseBlockTestState, responseGradTestState, BlockState.eval, blockVecDot,
        vecDot, basisVec, Pi.single_apply, mul_ite, Finset.sum_ite_eq', toFullBlockVec]
  | inr i =>
      simp [responseBlockTestState, responseFluxTestState, BlockState.eval, blockVecDot,
        vecDot, basisVec, Pi.single_apply, mul_ite, Finset.sum_ite_eq', toFullBlockVec]

/-- The complete doubled state of the Chapter-2 canonical response maximizer. -/
def canonicalOptimizerBlockState (U : Book.Ch02.Domain d) (aU : Book.Ch02.CoeffOn U)
    (p q : Vec d) : Vec d → BlockVec d := fun x ↦
  let v := (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p q).toSolution
  (v.toH1.grad x, matVecMul (aU.toCoeffField x) (v.toH1.grad x))

/-- A weighted coordinate readout of the canonical optimizer state. -/
def canonicalOptimizerStateReadout (U : Book.Ch02.Domain d) (aU : Book.Ch02.CoeffOn U)
    (p q : Vec d) (α : BlockCoord d) (η : Vec d → ℝ) : ℝ :=
  ∫ x in (U : Set (Vec d)), η x *
    toFullBlockVec (canonicalOptimizerBlockState U aU p q x) α ∂volume

theorem canonicalOptimizerStateReadout_congr {U : Book.Ch02.Domain d}
    {aU bU : Book.Ch02.CoeffOn U} (h : Book.Ch02.CoeffOn.AEEq aU bU)
    (p q : Vec d) (α : BlockCoord d) (η : Vec d → ℝ) :
    canonicalOptimizerStateReadout U aU p q α η =
      canonicalOptimizerStateReadout U bU p q α η := by
  have hgrad := Book.Ch02.canonicalMaximizer_sameGradientAE_ofAEEq h p q
  refine integral_congr_ae ?_
  filter_upwards [hgrad, h] with x hx hax
  have hx' :
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U aU) p
        q).toSolution.toH1.grad x =
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U bU) p
        q).toSolution.toH1.grad x := hx
  have hstate : canonicalOptimizerBlockState U aU p q x =
      canonicalOptimizerBlockState U bU p q x := by
    simp only [canonicalOptimizerBlockState, hx', hax]
  rw [hstate]

/-- A regular field on a quantitative slice, packaged as a Chapter-2 coefficient object. -/
def responseCoeffOnOfSlice (U : Book.Ch02.Domain d) {k : ℕ} (A : RegCoeffField d)
    (hk : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k A.toFun) : Book.Ch02.CoeffOn U where
  toCoeffField := A.toFun
  lam := ((k + 1 : ℝ)⁻¹)
  Lam := k + 1
  lam_pos := inv_pos.mpr (by positivity)
  lam_le_Lam := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
    exact le_trans ((inv_le_one₀ (by positivity)).2 h) h
  aeStronglyMeasurable := hk.2.1
  aeElliptic := hk.2.2

private theorem isPotentialZeroTraceOn_of_book
    {U : Set (Vec d)} {f : Vec d → Vec d} (hf : Book.Ch01.PotentialZeroTraceFieldOn U f) :
    IsPotentialZeroTraceOn U f := by
  rcases hf with ⟨_, φ, hφ⟩
  exact IsPotentialZeroTraceOn.congr_ae hφ.symm φ.isPotentialZeroTraceOn

/-- A Chapter-2 doubled admissible field is admissible for CG's block-`Mu` problem. -/
theorem isBlockMuAdmissible_of_bookDoubledMuAdmissible
    {U : Book.Ch02.Domain d} {P0 : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P0 X) :
    IsBlockMuAdmissible (U : Set (Vec d)) P0
      ({ potential := X.potential, flux := X.flux } : BlockState d) :=
  ⟨hX.1.1, isPotentialZeroTraceOn_of_book hX.1, hX.2.1, hX.2.2⟩

/-- A pointwise Chapter-2 doubled minimizer represents the same Hilbert minimizer selected by the
general-cell Galerkin construction. -/
theorem toHilbertBlockL2_eq_responseMinimizer_of_isDoubledMuMinimizer
    {U : Book.Ch02.Domain d} [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {k : ℕ} (hvol : 0 < (volume (U : Set (Vec d))).toReal) {aU : Book.Ch02.CoeffOn U}
    (hk : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k aU.toCoeffField)
    (P0 : BlockVec d) {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U aU P0 X)
    (hAdm : IsBlockMuAdmissible (U : Set (Vec d)) P0
      ({ potential := X.potential, flux := X.flux } : BlockState d)) :
    toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hAdm.memBlockL2_eval =
      (responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap P0 := by
  let a : {b : CoeffField d // AEEQuantitativeEllipticSlice (U : Set (Vec d)) k b} :=
    ⟨aU.toCoeffField, hk⟩
  let H := responseCellMuHilbert hvol a
  have hEnergy : blockEnergyAverage (U : Set (Vec d)) aU.toCoeffField
      ({ potential := X.potential, flux := X.flux } : BlockState d) =
        Mu (U : Set (Vec d)) P0 aU.toCoeffField := by
    calc
      blockEnergyAverage (U : Set (Vec d)) aU.toCoeffField
          ({ potential := X.potential, flux := X.flux } : BlockState d) =
          Book.Ch02.doubledMuValue U aU X := rfl
      _ = Book.Ch02.doubledMu U aU P0 := hX.doubledMuValue_eq_doubledMu
      _ = Mu (U : Set (Vec d)) P0 aU.toCoeffField := Book.Ch02.doubledMu_eq_Mu U aU P0
  have hcorr : toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
        hAdm.memBlockL2_eval - H.constantField P0 ∈ H.correctionSpace.correctionSpace := by
    rw [show H.correctionSpace = MuCorrectionSpaceData.ofSubmoduleClosures (U : Set (Vec d)) by
        exact correctionSpace_responseCellMuHilbert hvol a,
      show H.constantField = blockVecToHilbertBlockL2Const (U := (U : Set (Vec d))) by
        exact constantField_responseCellMuHilbert hvol a,
      hAdm.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add,
      add_sub_cancel_left]
    exact hAdm.toCorrectionFieldData_mem_correctionSpace
  have hQuad : quadraticEnergy H.energyBilin
      (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d))) hAdm.memBlockL2_eval) =
        Mu (U : Set (Vec d)) P0 aU.toCoeffField := by
    rw [← hEnergy]
    simpa [H, a, responseCellMuHilbert, responseCellMuSystem,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
      (responseCellMuSystem hvol a).toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        hAdm.memBlockL2_eval
  refine H.eq_minimizerMap_of_quadraticEnergy_le_muCandidate P0 _ hcorr (le_of_eq ?_)
  rw [hQuad]
  simpa [H, MuHilbertRealization.muCandidate, MuHilbertProblem.muCandidate,
    MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
    parameterAffineMinimizerMap] using! responseMu_eq_quadraticEnergy_minimizer hvol a P0

/-- Coordinatewise a.e. recovery of the canonical optimizer's complete doubled state. -/
theorem ae_toFullBlockVec_canonicalOptimizerBlockState
    {U : Book.Ch02.Domain d} {aU : Book.Ch02.CoeffOn U} (p q : Vec d)
    (α : BlockCoord d) {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U aU (-p, q) X) :
    (fun x ↦ toFullBlockVec (canonicalOptimizerBlockState U aU p q x) α)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x ↦ toFullBlockVec (X.eval x) α +
      toFullBlockVec (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x))
        α.swap := by
  cases α with
  | inl i =>
      filter_upwards
        [Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient U aU p q hX]
        with x hx
      show (canonicalOptimizerBlockState U aU p q x).1 i = _
      rw [canonicalOptimizerBlockState, ← hx]
      rfl
  | inr i =>
      filter_upwards
        [Book.Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux U aU p q hX]
        with x hx
      show (canonicalOptimizerBlockState U aU p q x).2 i = _
      rw [canonicalOptimizerBlockState, ← hx]
      rfl

theorem integrableOn_blockPairingIntegrand_of_responseSlice
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)] {k : ℕ} {a : CoeffField d}
    (hSlice : AEEQuantitativeEllipticSlice U k a) {X Y : BlockState d}
    (hX : MemBlockL2 U X.eval) (hY : MemBlockL2 U Y.eval) :
    IntegrableOn (blockPairingIntegrand a X Y) U := by
  have heq : blockPairingIntegrand a X Y = fun x ↦ ∑ α, ∑ β,
      blockPairingEntryWeight X Y α β x *
        toFullBlockMat (blockCoeffField a x) α β := by
    funext x
    exact blockPairingIntegrand_eq_sum_entryWeights a X Y x
  rw [heq]
  exact integrable_finsetSum _ fun α _ ↦ integrable_finsetSum _ fun β _ ↦
    hSlice.integrableOn_pairingWeightedFullBlockCoeffEntry_of_memBlockL2 hX hY α β

/-- Weighted coordinates of the canonical optimizer are the sum of an inner-product readout and
an energy-bilinear readout of the doubled minimizer. -/
theorem integral_weighted_canonicalOptimizerBlockState
    {U : Book.Ch02.Domain d} [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))]
    {k : ℕ} (hvol : 0 < (volume (U : Set (Vec d))).toReal) {aU : Book.Ch02.CoeffOn U}
    (hk : AEEQuantitativeEllipticSlice (U : Set (Vec d)) k aU.toCoeffField)
    (p q : Vec d) (α : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (U : Set (Vec d)) η) :
    ∫ x in (U : Set (Vec d)), η x *
        toFullBlockVec (canonicalOptimizerBlockState U aU p q x) α ∂volume =
      inner ℝ
          (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
            (responseBlockTestState_memBlockL2 hη α))
          ((responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) +
        (volume (U : Set (Vec d))).toReal *
          (responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energyBilin
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (responseBlockTestState_memBlockL2 hη α.swap))
            ((responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) := by
  classical
  obtain ⟨X, hX⟩ := (Book.Ch02.doubledMuTheory U aU).minimizer_exists (-p, q)
  have hAdm : IsBlockMuAdmissible (U : Set (Vec d)) (-p, q)
      ({ potential := X.potential, flux := X.flux } : BlockState d) :=
    isBlockMuAdmissible_of_bookDoubledMuAdmissible hX.1
  have hXmem := hAdm.memBlockL2_eval
  have hMin := toHilbertBlockL2_eq_responseMinimizer_of_isDoubledMuMinimizer
    hvol hk (-p, q) hX hAdm
  have hstate := ae_toFullBlockVec_canonicalOptimizerBlockState (aU := aU) p q α hX
  have hcoord : MemScalarL2 (U : Set (Vec d)) (fun x ↦ toFullBlockVec
      (({ potential := X.potential, flux := X.flux } : BlockState d).eval x) α) :=
    memScalarL2_fullBlockCoord_of_memBlockL2 hXmem α
  have hint1 : IntegrableOn (fun x ↦ η x * toFullBlockVec (X.eval x) α)
      (U : Set (Vec d)) := MeasureTheory.MemLp.integrable_mul hη hcoord
  have hpairing := integrableOn_blockPairingIntegrand_of_responseSlice hk
    (responseBlockTestState_memBlockL2 hη α.swap) hXmem
  have hpairEq : blockPairingIntegrand aU.toCoeffField (responseBlockTestState η α.swap)
      ({ potential := X.potential, flux := X.flux } : BlockState d) = fun x ↦
        η x * toFullBlockVec
          (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)) α.swap := by
    funext x
    exact blockVecDot_responseBlockTestState η α.swap _ x
  have hint2 : IntegrableOn (fun x ↦ η x * toFullBlockVec
      (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)) α.swap)
      (U : Set (Vec d)) := by simpa [hpairEq] using hpairing
  have hsplit : ∫ x in (U : Set (Vec d)), η x *
        toFullBlockVec (canonicalOptimizerBlockState U aU p q x) α ∂volume =
      (∫ x in (U : Set (Vec d)), η x * toFullBlockVec (X.eval x) α ∂volume) +
      ∫ x in (U : Set (Vec d)), η x * toFullBlockVec
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)) α.swap ∂volume := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae ?_
    filter_upwards [hstate] with x hx
    rw [hx, mul_add]
  rw [hsplit]
  congr 1
  · rw [← hMin, inner_toHilbertBlockL2OfBlockField_eq_integral_response]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    exact (blockVecDot_responseBlockTestState η α
      (({ potential := X.potential, flux := X.flux } : BlockState d).eval x) x).symm
  · have hbil :
        (responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energyBilin
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (responseBlockTestState_memBlockL2 hη α.swap))
            ((responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).minimizerMap (-p, q)) =
          blockPairingAverage (U : Set (Vec d)) aU.toCoeffField
            (responseBlockTestState η α.swap)
            ({ potential := X.potential, flux := X.flux } : BlockState d) := by
      rw [← hMin, (responseCellMuHilbert hvol ⟨aU.toCoeffField, hk⟩).energySymm]
      simpa [responseCellMuHilbert, responseCellMuSystem,
        AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        (responseCellMuSystem hvol ⟨aU.toCoeffField, hk⟩).toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
          (responseBlockTestState_memBlockL2 hη α.swap) hXmem
    rw [hbil, blockPairingAverage, volumeAverage, hpairEq, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hvol), one_mul]

/-- Weighted coordinate readouts of the canonical optimizer are measurable on one quantitative
ellipticity slice of a general response cell. -/
theorem measurable_integral_weighted_canonicalOptimizerBlockState
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Book.Ch02.Domain d}
    [IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d)))] {k : ℕ}
    (hUopen : IsOpen (U : Set (Vec d))) (hUfin : volume (U : Set (Vec d)) ≠ ⊤)
    (hvol : 0 < (volume (U : Set (Vec d))).toReal) {A : Om → RegCoeffField d}
    (hSlice : ∀ w : Om, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Vec d)) →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (aU : Om → Book.Ch02.CoeffOn U) (haU : ∀ w : Om, (aU w).toCoeffField = (A w).toFun)
    (p q : Vec d) (α : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (U : Set (Vec d)) η) :
    Measurable fun w : Om ↦ ∫ x in (U : Set (Vec d)), η x *
      toFullBlockVec (canonicalOptimizerBlockState U (aU w) p q x) α ∂volume := by
  have hk : ∀ w : Om,
      AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (aU w).toCoeffField := by
    intro w
    rw [haU w]
    exact hSlice w
  have hEqSlice : ∀ w : Om,
      (⟨(aU w).toCoeffField, hk w⟩ :
        {b : CoeffField d // AEEQuantitativeEllipticSlice (U : Set (Vec d)) k b}) =
      responseSliceOf hSlice w := fun w ↦ Subtype.ext (haU w)
  have heq : (fun w : Om ↦ ∫ x in (U : Set (Vec d)), η x *
      toFullBlockVec (canonicalOptimizerBlockState U (aU w) p q x) α ∂volume) =
      fun w ↦
        inner ℝ
            (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
              (responseBlockTestState_memBlockL2 hη α))
            ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap (-p, q)) +
          (volume (U : Set (Vec d))).toReal *
            (responseCellMuHilbert hvol (responseSliceOf hSlice w)).energyBilin
              (toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
                (responseBlockTestState_memBlockL2 hη α.swap))
              ((responseCellMuHilbert hvol (responseSliceOf hSlice w)).minimizerMap (-p, q)) := by
    funext w
    rw [integral_weighted_canonicalOptimizerBlockState hvol (hk w) p q α hη,
      hEqSlice w]
  rw [heq]
  exact (measurable_inner_responseCellMuMinimizer hUopen hUfin hvol hSlice hEntry (-p, q) _).add
    ((measurable_energyBilin_responseCellMuMinimizer hUopen hUfin hvol hSlice hEntry
      (-p, q) (responseBlockTestState_memBlockL2 hη α.swap)).const_mul _)
end


end Homogenization.HighContrast.Multiscale
