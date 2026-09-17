import HCPoly.Entry.Multiscale.ResponseInputs.OptimizerReadout
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# Gluing optimizer readouts across quantitative slices
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Quantitative slices cover each transformed regular response field on an adapted cell. -/
theorem exists_responseSlice_of_ellipticRepresentative
    {U : Set (Vec d)} (hU : MeasurableSet U) (A : RegCoeffField d)
    {lam Lam : ℝ} {f : CoeffField d} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U f)
    (hae : A.toFun =ᵐ[volumeMeasureOn U] f) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice U k A.toFun := by
  have hAEE : IsAEEllipticFieldOn lam Lam U A.toFun := by
    refine ⟨hU, ?_, ?_⟩
    · intro i j
      exact aestronglyMeasurable_restrictCoeffField_carrier U hU A i j
    · filter_upwards [hae, (IsAEEllipticFieldOn.of_isEllipticFieldOn hEll).2.2]
        with x hx hxf
      simpa [hx] using hxf
  exact AEEQuantitativeEllipticSlice.exists_of_aeeEllipticOn hlam hAEE

/-- Choose a Chapter-2 coefficient object from the first quantitative slice containing a regular
field.  Its raw representative remains exactly the input field. -/
def responseCoeffOnFromSliceCover (U : Book.Ch02.Domain d) (A : RegCoeffField d)
    (hcover : ∃ k : ℕ, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k A.toFun) :
    Book.Ch02.CoeffOn U :=
  responseCoeffOnOfSlice U A (Classical.choose_spec hcover)

@[simp] theorem responseCoeffOnFromSliceCover_toFun (U : Book.Ch02.Domain d)
    (A : RegCoeffField d)
    (hcover : ∃ k : ℕ, AEEQuantitativeEllipticSlice (U : Set (Vec d)) k A.toFun) :
    (responseCoeffOnFromSliceCover U A hcover).toCoeffField = A.toFun := rfl

/-- Glue the fixed-slice weighted-readout theorem across a measurable countable slice cover. -/
theorem measurable_canonicalOptimizerStateReadout_of_sliceCover
    {Om : Type*} [mOm : MeasurableSpace Om] {U : Book.Ch02.Domain d}
    (hUopen : IsOpen (U : Set (Vec d))) (hUfin : volume (U : Set (Vec d)) ≠ ⊤)
    (hvol : 0 < (volume (U : Set (Vec d))).toReal) {A : Om → RegCoeffField d}
    (hcover : ∀ w : Om, ∃ k : ℕ,
      AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun)
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Vec d)) →
        Measurable fun w ↦ entryTestR i j φ (A w))
    (aU : Om → Book.Ch02.CoeffOn U) (haU : ∀ w, (aU w).toCoeffField = (A w).toFun)
    (p q : Vec d) (α : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (U : Set (Vec d)) η) :
    Measurable fun w : Om ↦ canonicalOptimizerStateReadout U (aU w) p q α η := by
  classical
  let slice : ℕ → Set Om := fun k ↦
    {w | AEEQuantitativeEllipticSlice (U : Set (Vec d)) k (A w).toFun}
  have hsliceMeas : ∀ k, MeasurableSet (slice k) := by
    intro k
    apply Annealed.measurableSet_aeeSlice_of_entryTest_response A hUopen
    intro i j φ hφ
    exact hEntry i j hφ.contDiff hφ.hasCompactSupport hφ.tsupport_subset
  have hslices : ⋃ k : ℕ, slice k = Set.univ := by
    ext w
    constructor
    · exact fun _ ↦ Set.mem_univ w
    · intro _
      obtain ⟨k, hk⟩ := hcover w
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
  let f : (k : ℕ) → slice k → ℝ := fun k w ↦
    canonicalOptimizerStateReadout U (responseCoeffOnOfSlice U (A w.1) w.2) p q α η
  have hagree : ∀ (i j : ℕ) (w : Om) (hwi : w ∈ slice i) (hwj : w ∈ slice j),
      f i ⟨w, hwi⟩ = f j ⟨w, hwj⟩ := by
    intro i j w hwi hwj
    apply canonicalOptimizerStateReadout_congr
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hfmeas : ∀ k : ℕ, Measurable (f k) := by
    intro k
    exact measurable_integral_weighted_canonicalOptimizerBlockState hUopen hUfin hvol
      (A := fun w : slice k ↦ A w.1) (fun w ↦ w.2)
      (fun i j φ hφ hc hs ↦ (hEntry i j hφ hc hs).comp measurable_subtype_coe)
      (fun w ↦ responseCoeffOnOfSlice U (A w.1) w.2) (fun _ ↦ rfl) p q α hη
  have heq : (fun w : Om ↦ canonicalOptimizerStateReadout U (aU w) p q α η) =
      Set.liftCover slice f hagree hslices := by
    funext w
    obtain ⟨k, hk⟩ := hcover w
    rw [Set.liftCover_of_mem (S := slice) (f := f) (hf := hagree) (hS := hslices)
      (i := k) hk]
    apply canonicalOptimizerStateReadout_congr
    filter_upwards with x
    exact congrFun (haU w) x
  rw [heq]
  exact measurable_liftCover slice hsliceMeas f hfmeas hagree hslices

/-! ## The actual transformed coefficient fields -/

/-- The minus transformed coefficient lies in some quantitative slice on every adapted cell. -/
theorem exists_responseSlice_selectionRespCoeffMinusReg [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice (HighContrast.adaptedCell q t) k
      (selectionRespCoeffMinusReg F a).toFun := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  exact exists_responseSlice_of_ellipticRepresentative
    (measurableSet_of_isEllipticFieldOn hEll) (selectionRespCoeffMinusReg F a)
    hlam hEll (by simpa only [selectionRespCoeffMinusReg_toFun] using hae)

/-- The plus transformed coefficient lies in some quantitative slice on every adapted cell. -/
theorem exists_responseSlice_selectionRespCoeffPlusReg [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    ∃ k : ℕ, AEEQuantitativeEllipticSlice (HighContrast.adaptedCell q t) k
      (selectionRespCoeffPlusReg F a).toFun := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  exact exists_responseSlice_of_ellipticRepresentative
    (measurableSet_of_isEllipticFieldOn hEll) (selectionRespCoeffPlusReg F a)
    hlam hEll (by simpa only [selectionRespCoeffPlusReg_toFun] using hae)

/-- Canonical Chapter-2 coefficient object for the minus transformed response field. -/
def canonicalRespCoeffMinusOn [NeZero d] (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
  responseCoeffOnFromSliceCover (adaptedDomain q hq t) (selectionRespCoeffMinusReg F a)
    (exists_responseSlice_selectionRespCoeffMinusReg q hq t F a)

@[simp] theorem canonicalRespCoeffMinusOn_toFun [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    (canonicalRespCoeffMinusOn q hq t F a).toCoeffField = respCoeffMinus F a := by
  show (selectionRespCoeffMinusReg F a).toFun = respCoeffMinus F a
  exact selectionRespCoeffMinusReg_toFun F a

/-- Canonical Chapter-2 coefficient object for the plus transformed response field. -/
def canonicalRespCoeffPlusOn [NeZero d] (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) : Book.Ch02.CoeffOn (adaptedDomain q hq t) :=
  responseCoeffOnFromSliceCover (adaptedDomain q hq t) (selectionRespCoeffPlusReg F a)
    (exists_responseSlice_selectionRespCoeffPlusReg q hq t F a)

@[simp] theorem canonicalRespCoeffPlusOn_toFun [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    (canonicalRespCoeffPlusOn q hq t F a).toCoeffField = respCoeffPlus F a := by
  show (selectionRespCoeffPlusReg F a).toFun = respCoeffPlus F a
  exact selectionRespCoeffPlusReg_toFun F a

/-- Adapted cells have positive real volume, in the exact form used by the Galerkin selector. -/
theorem adaptedCell_volume_toReal_pos [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) :
    0 < (volume (HighContrast.adaptedCell q t)).toReal := by
  have hset : HighContrast.adaptedCell q t =
      translateSet 0 (matVecMul q '' openCubeSet (originCube d t)) := by
    rw [← Annealed.adaptedCellTranslate_eq_cg_affine q t 0]
    simp [HighContrast.adaptedCellTranslate]
  rw [hset]
  exact volume_affine_openCube_toReal_pos q hq t 0

/-- Every weighted coordinate readout of the canonical minus optimizer is measurable in the
coefficient sample. -/
theorem measurable_canonicalRespCoeffMinusReadout [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d)
    (p r : Vec d) (alpha : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (HighContrast.adaptedCell q t) η) :
    Measurable fun a : CoeffSpace d ↦
      canonicalOptimizerStateReadout (adaptedDomain q hq t)
        (canonicalRespCoeffMinusOn q hq t F a) p r alpha η := by
  apply measurable_canonicalOptimizerStateReadout_of_sliceCover
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen
    (adaptedCell_isOpenBoundedConvexDomain q hq t).volume_lt_top.ne
    (adaptedCell_volume_toReal_pos q hq t)
    (fun a ↦ exists_responseSlice_selectionRespCoeffMinusReg q hq t F a)
    (fun i j φ hφ hcpt _hs ↦ measurable_entryTest_selectionRespCoeffMinusReg F i j hφ hcpt)
    (fun a ↦ canonicalRespCoeffMinusOn q hq t F a) (fun _ ↦ rfl) p r alpha hη

/-- Every weighted coordinate readout of the canonical plus optimizer is measurable in the
coefficient sample. -/
theorem measurable_canonicalRespCoeffPlusReadout [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d)
    (p r : Vec d) (alpha : BlockCoord d) {η : Vec d → ℝ}
    (hη : MemScalarL2 (HighContrast.adaptedCell q t) η) :
    Measurable fun a : CoeffSpace d ↦
      canonicalOptimizerStateReadout (adaptedDomain q hq t)
        (canonicalRespCoeffPlusOn q hq t F a) p r alpha η := by
  apply measurable_canonicalOptimizerStateReadout_of_sliceCover
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen
    (adaptedCell_isOpenBoundedConvexDomain q hq t).volume_lt_top.ne
    (adaptedCell_volume_toReal_pos q hq t)
    (fun a ↦ exists_responseSlice_selectionRespCoeffPlusReg q hq t F a)
    (fun i j φ hφ hcpt _hs ↦ measurable_entryTest_selectionRespCoeffPlusReg F i j hφ hcpt)
    (fun a ↦ canonicalRespCoeffPlusOn q hq t F a) (fun _ ↦ rfl) p r alpha hη

/-- Restricting the readout weight by an indicator realizes a localized volume average. -/
theorem volumeAverage_weighted_canonicalOptimizerBlockState
    {U : Book.Ch02.Domain d} (aU : Book.Ch02.CoeffOn U) (p r : Vec d)
    (alpha : BlockCoord d) {V : Set (Vec d)} (hV : MeasurableSet V)
    (hVU : V ⊆ (U : Set (Vec d))) (eta : Vec d → ℝ) :
    volumeAverage V (fun x ↦ eta x *
        toFullBlockVec (canonicalOptimizerBlockState U aU p r x) alpha) =
      (volume V).toReal⁻¹ *
        canonicalOptimizerStateReadout U aU p r alpha (V.indicator eta) := by
  unfold volumeAverage canonicalOptimizerStateReadout
  congr 1
  rw [← integral_indicator hV]
  rw [← integral_indicator U.isDomain.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ V
  · simp [hx, hVU hx]
  · by_cases hxu : x ∈ (U : Set (Vec d)) <;> simp [hx, hxu]

/-- Localized weighted averages of the canonical minus optimizer are measurable. -/
theorem measurable_volumeAverage_weighted_canonicalRespCoeffMinus [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d)
    (p r : Vec d) (alpha : BlockCoord d) {V : Set (Vec d)}
    (hV : MeasurableSet V) (hVU : V ⊆ HighContrast.adaptedCell q t)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (HighContrast.adaptedCell q t) (V.indicator eta)) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x) alpha) := by
  have heq : (fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r x) alpha)) =
      fun a ↦ (volume V).toReal⁻¹ *
        canonicalOptimizerStateReadout (adaptedDomain q hq t)
          (canonicalRespCoeffMinusOn q hq t F a) p r alpha (V.indicator eta) := by
    funext a
    exact volumeAverage_weighted_canonicalOptimizerBlockState
      (canonicalRespCoeffMinusOn q hq t F a) p r alpha hV hVU eta
  rw [heq]
  exact (measurable_canonicalRespCoeffMinusReadout q hq t F p r alpha heta).const_mul _

/-- Localized weighted averages of the canonical plus optimizer are measurable. -/
theorem measurable_volumeAverage_weighted_canonicalRespCoeffPlus [NeZero d]
    (q : Mat d) (hq : IsUnit q) (t : ℤ) (F : BlockMat d)
    (p r : Vec d) (alpha : BlockCoord d) {V : Set (Vec d)}
    (hV : MeasurableSet V) (hVU : V ⊆ HighContrast.adaptedCell q t)
    {eta : Vec d → ℝ}
    (heta : MemScalarL2 (HighContrast.adaptedCell q t) (V.indicator eta)) :
    Measurable fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x) alpha) := by
  have heq : (fun a : CoeffSpace d ↦
      volumeAverage V (fun x ↦ eta x * toFullBlockVec
        (canonicalOptimizerBlockState (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r x) alpha)) =
      fun a ↦ (volume V).toReal⁻¹ *
        canonicalOptimizerStateReadout (adaptedDomain q hq t)
          (canonicalRespCoeffPlusOn q hq t F a) p r alpha (V.indicator eta) := by
    funext a
    exact volumeAverage_weighted_canonicalOptimizerBlockState
      (canonicalRespCoeffPlusOn q hq t F a) p r alpha hV hVU eta
  rw [heq]
  exact (measurable_canonicalRespCoeffPlusReadout q hq t F p r alpha heta).const_mul _

end


end Homogenization.HighContrast.Multiscale
