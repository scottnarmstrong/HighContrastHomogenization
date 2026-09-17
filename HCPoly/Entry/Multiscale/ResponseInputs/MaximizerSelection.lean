import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Entry.Annealed.AdaptedLocality

/-!
# Canonical response-maximizer selection: comparison and carrier measurability

The pointwise `Nonempty.some` used by
`AdaptedCutoff.lean` is not definitionally the Chapter-2 canonical maximizer.  Nevertheless,
Chapter 2 uniqueness shows that their gradients, fluxes, and every subcell average of the doubled
state agree almost everywhere.  The second part records, on the library's actual coefficient
carrier, the smooth entry-test measurability needed by the Galerkin selection construction.
-/

open Homogenization.HighContrast (CoeffSpace ae_abs_entry_le_of_aeUniformlyEllipticField
  coeffPairing)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The Chapter-2 canonical maximizer, repackaged on the scalar-response carrier of the entry route. -/
def scalarCanonicalMaximizerOfCoeffOn {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) : ScalarCanonicalMaximizer (U : Set (Vec d)) p q a.toCoeffField where
  toAHarmonicFunctionMeanZero :=
    ⟨(Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a) p q).toSolution,
      (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a) p q).meanZero⟩
  isMaximizer := book_isResponseMaximizer_iff.mp
    (Book.Ch02.canonicalMaximizer (Book.Ch02.responseExistenceTheory U a) p q).isMaximizer

/-- The harmonic-function projection of the preceding canonical package. -/
def canonicalAHarmonicFunctionOfCoeffOn {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) : AHarmonicFunction a.toCoeffField (U : Set (Vec d)) :=
  (scalarCanonicalMaximizerOfCoeffOn a p q).toAHarmonicFunctionMeanZero.toAHarmonicFunction

/-- STEP ZERO.  An arbitrary scalar canonical maximizer (in particular the fresh
`Nonempty.some` in `AdaptedCutoff.lean`) has the same gradient a.e. as the specific Chapter-2
canonical family used by the measurable-selection construction. -/
theorem scalarCanonicalMaximizer_grad_ae_eq_canonicalOfCoeffOn
    {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U) (p q : Vec d)
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q a.toCoeffField) :
    (canonicalAHarmonicFunctionOfCoeffOn a p q).toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad := by
  exact Book.Ch02.canonicalMaximizer_sameGradientAE_of_isResponseMaximizer
    (book_isResponseMaximizer_iff.mpr v.isResponseMaximizer)

/-- Transport a specified scalar maximizer across an a.e. equality of coefficients.  Unlike the
existence-only bridge in `HC1_DomainBridge`, this keeps the chosen object visible for STEP ZERO. -/
def scalarCanonicalMaximizerOfAEEq {U : Set (Vec d)} {a b : CoeffField d}
    (h : a =ᵐ[volumeMeasureOn U] b) (p q : Vec d)
    (v : ScalarCanonicalMaximizer U p q a) : ScalarCanonicalMaximizer U p q b where
  toAHarmonicFunctionMeanZero :=
    ⟨aHarmonicFunctionOfAEEqCoeff h
      v.toAHarmonicFunctionMeanZero.toAHarmonicFunction,
      v.toAHarmonicFunctionMeanZero.meanZero⟩
  isMaximizer := by
    intro w
    have key := v.isMaximizer (aHarmonicFunctionOfAEEqCoeff h.symm w)
    have h1 : volumeAverage U (scalarResponseIntegrand U b p q w) =
        volumeAverage U (scalarResponseIntegrand U a p q
          (aHarmonicFunctionOfAEEqCoeff h.symm w)) :=
      volumeAverage_scalarResponseIntegrand_congr h.symm p q w _ (fun _ => rfl)
    have h2 : volumeAverage U
          (scalarResponseIntegrand U a p q
            v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) =
        volumeAverage U (scalarResponseIntegrand U b p q
          (aHarmonicFunctionOfAEEqCoeff h
            v.toAHarmonicFunctionMeanZero.toAHarmonicFunction)) :=
      volumeAverage_scalarResponseIntegrand_congr h p q _ _ (fun _ => rfl)
    rw [h1, ← h2]
    exact key

/-- STEP ZERO on the actual coefficient shape.  If `b` only has a pointwise elliptic
representative `f`, the arbitrary `Nonempty.some` maximizer for `b` still agrees a.e. in gradient
with the Chapter-2 canonical maximizer for `f`, after the canonical null-set transport. -/
theorem scalarCanonicalMaximizer_grad_ae_eq_canonicalOfAEEq
    {U : Book.Ch02.Domain d} {b f : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (h : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q b) :
    (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q).toH1.grad
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        v.toAHarmonicFunctionMeanZero.toAHarmonicFunction.toH1.grad := by
  let vf : ScalarCanonicalMaximizer (U : Set (Vec d)) p q f :=
    scalarCanonicalMaximizerOfAEEq h p q v
  simpa [vf, scalarCanonicalMaximizerOfAEEq, aHarmonicFunctionOfAEEqCoeff] using
    scalarCanonicalMaximizer_grad_ae_eq_canonicalOfCoeffOn
      (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q vf

/-- The comparison includes the flux: the coefficient equality and gradient uniqueness identify
the complete doubled state on the parent cell. -/
theorem optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
    {U : Book.Ch02.Domain d} {b f : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (h : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q b) :
    optimizerField f
        (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction := by
  filter_upwards [scalarCanonicalMaximizer_grad_ae_eq_canonicalOfAEEq
    hlam hle hEll h p q v, h] with x hxg hxb
  simp only [optimizerField, hxg, ← hxb]

/-- In particular every strict subcell average (`n ≥ 1` as well as `n = 0`) of the ad hoc
maximizer is determined by the measurable canonical selection. -/
theorem cellAverage_scalarCanonicalMaximizer_eq_canonicalOfAEEq
    {U : Book.Ch02.Domain d} {V : Set (Vec d)} (hVU : V ⊆ (U : Set (Vec d)))
    {b f : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) f)
    (h : b =ᵐ[volumeMeasureOn (U : Set (Vec d))] f) (p q : Vec d)
    (v : ScalarCanonicalMaximizer (U : Set (Vec d)) p q b) :
    cellAverage V
        (optimizerField f
          (canonicalAHarmonicFunctionOfCoeffOn (coeffOnOfIsEllipticFieldOn hlam hle hEll) p q)) =
      cellAverage V (optimizerField b v.toAHarmonicFunctionMeanZero.toAHarmonicFunction) :=
  cellAverage_congr_ae hVU
    (optimizerField_scalarCanonicalMaximizer_ae_eq_canonicalOfAEEq
      hlam hle hEll h p q v)

/-- The library's actual a.e.-quotient coefficient carrier, realized in CG's regular carrier. -/
def selectionRegCoeffField (a : CoeffSpace d) : RegCoeffField d where
  toFun := ⇑a.1
  entry_measurable := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp a.1.measurable)
  entry_locInt := by
    intro i j
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨M, -, hM⟩ := ae_abs_entry_le_of_aeUniformlyEllipticField a.2 hK.isBounded
    refine Measure.integrableOn_of_bounded hK.measure_lt_top.ne
      ((continuous_id.matrix_elem i j).comp_aestronglyMeasurable a.1.aestronglyMeasurable) (M := M) ?_
    filter_upwards [ae_restrict_of_ae hM, ae_restrict_mem hK.measurableSet] with x hx hxK
    simpa [Real.norm_eq_abs] using hx hxK i j

@[simp] theorem selectionRegCoeffField_toFun (a : CoeffSpace d) :
    (selectionRegCoeffField a).toFun = (⇑a.1 : CoeffField d) := rfl

/-- The `hEntry` obligation of the Galerkin selection chain is dischargeable from the
actual coefficient carrier and its global smooth-test sigma algebra; it is not an additional
law or `RawOutput` hypothesis. -/
theorem measurable_entryTest_selectionRegCoeffField (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcpt : HasCompactSupport φ) :
    Measurable (fun a : CoeffSpace d ↦ entryTestR i j φ (selectionRegCoeffField a)) := by
  have heq : (fun a : CoeffSpace d ↦ entryTestR i j φ (selectionRegCoeffField a)) =
      coeffPairing (Pi.single j 1) (Pi.single i 1) φ := by
    funext a
    simp [entryTestR, coeffPairing, selectionRegCoeffField, vecDot_single_left,
      matVecMul_single]
  rw [heq]
  exact Annealed.measurable_coeffPairing_local (U := Set.univ) (Pi.single j 1) (Pi.single i 1)
    ⟨hφ, hcpt, Set.subset_univ _⟩

/-! ## The two response-coefficient transformations

The Galerkin selection API uses `RegCoeffField`, whereas the response argument is written on the
raw carrier as `a ↦ a - respg F` or `a ↦ aᵀ + respg F`.  The following carrier lifts make
the algebraic generator transport explicit. -/

/-- The regular-carrier lift of `respCoeffMinus F`. -/
def selectionRespCoeffMinusReg (F : BlockMat d) (a : CoeffSpace d) : RegCoeffField d :=
  selectionRegCoeffField a + (-1 : ℝ) • RegCoeffField.constRegCoeffField (respg F)

@[simp] theorem selectionRespCoeffMinusReg_toFun (F : BlockMat d) (a : CoeffSpace d) :
    (selectionRespCoeffMinusReg F a).toFun = respCoeffMinus F a := by
  funext x i j
  simp [selectionRespCoeffMinusReg, respCoeffMinus, sub_eq_add_neg]

/-- Smooth compactly-supported entry tests of `respCoeffMinus F` are measurable on the actual
coefficient carrier. -/
theorem measurable_entryTest_selectionRespCoeffMinusReg (F : BlockMat d) (i j : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcpt : HasCompactSupport φ) :
    Measurable (fun a : CoeffSpace d ↦
      entryTestR i j φ (selectionRespCoeffMinusReg F a)) := by
  have hprobe : IsProbeR φ := IsProbeR.of_smooth hφ hcpt
  have heq : (fun a : CoeffSpace d ↦
      entryTestR i j φ (selectionRespCoeffMinusReg F a)) =
      fun a ↦ entryTestR i j φ (selectionRegCoeffField a) +
        (-1 : ℝ) * entryTestR i j φ (RegCoeffField.constRegCoeffField (respg F)) := by
    funext a
    rw [selectionRespCoeffMinusReg, entryTestR_add i j hprobe,
      entryTestR_smul]
  rw [heq]
  exact (measurable_entryTest_selectionRegCoeffField i j hφ hcpt).add measurable_const

/-- The regular-carrier lift of `respCoeffPlus F`. -/
def selectionRespCoeffPlusReg (F : BlockMat d) (a : CoeffSpace d) : RegCoeffField d :=
  adjointReg (selectionRegCoeffField a) + RegCoeffField.constRegCoeffField (respg F)

@[simp] theorem selectionRespCoeffPlusReg_toFun (F : BlockMat d) (a : CoeffSpace d) :
    (selectionRespCoeffPlusReg F a).toFun = respCoeffPlus F a := by
  funext x i j
  simp [selectionRespCoeffPlusReg, respCoeffPlus, matTranspose]

/-- Smooth compactly-supported entry tests of `respCoeffPlus F` are measurable on the actual
coefficient carrier; transpose merely swaps the tested indices. -/
theorem measurable_entryTest_selectionRespCoeffPlusReg (F : BlockMat d) (i j : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcpt : HasCompactSupport φ) :
    Measurable (fun a : CoeffSpace d ↦
      entryTestR i j φ (selectionRespCoeffPlusReg F a)) := by
  have hprobe : IsProbeR φ := IsProbeR.of_smooth hφ hcpt
  have heq : (fun a : CoeffSpace d ↦
      entryTestR i j φ (selectionRespCoeffPlusReg F a)) =
      fun a ↦ entryTestR j i φ (selectionRegCoeffField a) +
        entryTestR i j φ (RegCoeffField.constRegCoeffField (respg F)) := by
    funext a
    rw [selectionRespCoeffPlusReg, entryTestR_add i j hprobe,
      entryTestR_adjointReg]
  rw [heq]
  exact (measurable_entryTest_selectionRegCoeffField j i hφ hcpt).add measurable_const

end

end Homogenization.HighContrast.Multiscale
