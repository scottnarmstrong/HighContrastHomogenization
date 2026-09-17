import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakCarrierInputs

/-!
# Integrability of the doubled optimizer field on the estimate's own cell

The cell-average steps of the diagonal weak-norm estimate move a matrix through the cell average
of the doubled optimizer field `optimizerField b u = (∇v, b ∇v)`.  Integrability of both slots and
of the scalar self-pairing `x ↦ blockVecDot X(x) X(x)` is needed on the estimate's own adapted
cell, not only on its aligned subcells.

The two slots are handled as in the subcell statements.  The gradient slot is the weak gradient of
an `H¹` function and is `L²` with no ellipticity hypothesis.  The flux slot `x ↦ b(x) ∇u(x)` is
`L²` because the tree supplies an a.e.-equal representative that is pointwise elliptic on the cell
(`exists_elliptic_representative_respCoeffMinus`, `…Plus`); the two fields agree almost everywhere,
so integrability transfers.  The self-pairing is `L¹` because the product of two `L²` scalar
components is `L¹` (Cauchy-Schwarz), and finite-measure `L²` is `L¹`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The recentred coefficient `a_- = respCoeffMinus F a` -/

/-- **Both slots of the doubled optimizer field are `L²` on the adapted cell, for
`respCoeffMinus F a`.**  The gradient slot is the weak gradient of the `H¹` function carried by
the `AHarmonicFunction`, and the flux slot is `L²` through the a.e.-equal pointwise elliptic
representative of `respCoeffMinus F a` on the cell. -/
theorem h6a_memVectorL2_optimizerField_respCoeffMinus_cell (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t)) :
    MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (optimizerField (respCoeffMinus F a) u x).1) ∧
      MemVectorL2 (HighContrast.adaptedCell q t)
        (fun x => (optimizerField (respCoeffMinus F a) u x).2) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  refine ⟨?_, ?_⟩
  · simpa [optimizerField] using u.toH1.grad_memVectorL2
  · simpa [optimizerField] using
      h6a_memVectorL2_optimizerField_flux_of_aeEq (subset_refl _) hEll hae u

/-- **Both slots of the doubled optimizer field are integrable on the adapted cell, for
`respCoeffMinus F a`.**  Square-integrability on the finite-measure adapted cell gives
integrability of each component. -/
theorem h6a_integrableOn_optimizerField_respCoeffMinus_cell (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t)) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (HighContrast.adaptedCell q t) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (HighContrast.adaptedCell q t) := by
  obtain ⟨hmem1, hmem2⟩ :=
    h6a_memVectorL2_optimizerField_respCoeffMinus_cell q hq t F a u
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  exact ⟨MemLp.integrable (by norm_num) ((MeasureTheory.memLp_pi_iff.mp hmem1) j),
    MemLp.integrable (by norm_num) ((MeasureTheory.memLp_pi_iff.mp hmem2) j)⟩

/-! ## The transposed recentred coefficient `a_+ = respCoeffPlus F a` -/

/-- **Both slots of the doubled optimizer field are `L²` on the adapted cell, for
`respCoeffPlus F a`.**  The transposed twin of
`h6a_memVectorL2_optimizerField_respCoeffMinus_cell`. -/
theorem h6a_memVectorL2_optimizerField_respCoeffPlus_cell (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t)) :
    MemVectorL2 (HighContrast.adaptedCell q t) (fun x => (optimizerField (respCoeffPlus F a) u x).1) ∧
      MemVectorL2 (HighContrast.adaptedCell q t)
        (fun x => (optimizerField (respCoeffPlus F a) u x).2) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  refine ⟨?_, ?_⟩
  · simpa [optimizerField] using u.toH1.grad_memVectorL2
  · simpa [optimizerField] using
      h6a_memVectorL2_optimizerField_flux_of_aeEq (subset_refl _) hEll hae u

/-- **Both slots of the doubled optimizer field are integrable on the adapted cell, for
`respCoeffPlus F a`.**  The transposed twin of
`h6a_integrableOn_optimizerField_respCoeffMinus_cell`. -/
theorem h6a_integrableOn_optimizerField_respCoeffPlus_cell (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t)) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (HighContrast.adaptedCell q t) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (HighContrast.adaptedCell q t) := by
  obtain ⟨hmem1, hmem2⟩ :=
    h6a_memVectorL2_optimizerField_respCoeffPlus_cell q hq t F a u
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) :=
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  exact ⟨MemLp.integrable (by norm_num) ((MeasureTheory.memLp_pi_iff.mp hmem1) j),
    MemLp.integrable (by norm_num) ((MeasureTheory.memLp_pi_iff.mp hmem2) j)⟩

end

end Homogenization.HighContrast.Multiscale
