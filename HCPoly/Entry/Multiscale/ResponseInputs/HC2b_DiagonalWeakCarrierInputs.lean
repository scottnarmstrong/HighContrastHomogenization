import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakOptimizerIntegrable
import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput

/-!
# Pointwise ellipticity and integrability of the recentred field at the carriers

Every cell-average step of the diagonal weak-norm estimate moves a matrix through the cell
average of the doubled optimizer field `optimizerField b u = (∇v, b ∇v)`, so those steps ask
for two things about the recentred coefficient `b = respCoeffMinus F a` (or `b = respCoeffPlus
F a`): uniform ellipticity of `b` on the cell and integrability of both slots of the doubled
field.

Pointwise ellipticity is **not** derivable.  A point of `CoeffSpace d` is an a.e. class, while
`IsEllipticFieldOn lam Lam U b` requires `IsEllipticMatrix lam Lam (b x)` at every `x ∈ U`; an
arbitrary representative of the class may be modified on a null set and remain locally uniformly
elliptic almost everywhere, so only the a.e. shape `IsAEEllipticFieldOn lam Lam U b` is
available.  The tree carries the a.e.-representative datum for the two response coefficients,
`exists_elliptic_representative_respCoeffMinus` and `…Plus` (`H8bEllipticInput.lean`): some
field `f` pointwise elliptic on the cell and equal to `b` there almost everywhere.

This file discharges the integrability side conditions through that representative.  Integrals
are a.e. invariant, so the representative suffices.  The flux slot `x ↦ b(x) ∇u(x)` is `L²`
because the representative's flux is `L²` (`memVectorL2_matVecMul_of_isEllipticFieldOn`) and the
two agree almost everywhere; the scalar energy density `∇u · b ∇u` is the `vecDot` pairing of
two `L²` fields (`integrableOn_vecDot_of_memVectorL2`); and it is nonnegative almost everywhere
because the representative is elliptic on the cell, so the `vecDot` against its lower bound is
a.e. nonnegative and `volumeAverage` inherits that sign.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## Transport of the flux and the energy density across the a.e. representative -/

omit [NeZero d] in
/-- **The flux slot is `L²` through the a.e. representative.**  If `b` agrees almost everywhere
on a set `U` with a field `f` pointwise elliptic on a subset `V ⊆ U`, then `x ↦ b(x) ∇u(x)` is
`L²` on `V` for any `AHarmonicFunction` of `b` on `U`: the representative's flux is `L²` there
and the two coincide a.e. on `V`. -/
theorem h6a_memVectorL2_optimizerField_flux_of_aeEq {U V : Set (Vec d)} (hVU : V ⊆ U)
    {b f : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam V f)
    (hbf : b =ᵐ[volumeMeasureOn U] f) (u : AHarmonicFunction b U) :
    MemVectorL2 V (fun x => matVecMul (b x) (u.toH1.grad x)) := by
  have hbfV : b =ᵐ[volumeMeasureOn V] f :=
    MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_mono hVU le_rfl) hbf
  have hgradV : MemVectorL2 V u.toH1.grad :=
    (u.toH1.grad_memVectorL2).mono_measure (MeasureTheory.Measure.restrict_mono hVU le_rfl)
  have hfluxf : MemVectorL2 V (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hgradV
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x)) =ᵐ[volumeMeasureOn V]
      (fun x => matVecMul (b x) (u.toH1.grad x)) := by
    filter_upwards [hbfV] with x hx
    rw [hx]
  exact (MeasureTheory.memLp_congr_ae hae).mp hfluxf

omit [NeZero d] in
/-- **The scalar energy density is integrable through the a.e. representative.**  If `b` agrees
almost everywhere on `U` with a field `f` pointwise elliptic on `U`, then
`x ↦ ∇u(x) · b(x) ∇u(x)` is integrable on `U`: the gradient is `L²` and the representative's
flux is `L²`, so their `vecDot` pairing is `L¹`, and the a.e. equality transports it to `b`. -/
theorem h6a_integrableOn_energyDensity_of_aeEq {U : Set (Vec d)} {b f : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U f) (hbf : b =ᵐ[volumeMeasureOn U] f)
    (u : AHarmonicFunction b U) :
    IntegrableOn (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2) U := by
  have hgrad : MemVectorL2 U u.toH1.grad := u.toH1.grad_memVectorL2
  have hfluxf : MemVectorL2 U (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hgrad
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x)) =ᵐ[volumeMeasureOn U]
      (fun x => matVecMul (b x) (u.toH1.grad x)) := by
    filter_upwards [hbf] with x hx
    rw [hx]
  have hfluxb : MemVectorL2 U (fun x => matVecMul (b x) (u.toH1.grad x)) :=
    (MeasureTheory.memLp_congr_ae hae).mp hfluxf
  simpa [optimizerField] using integrableOn_vecDot_of_memVectorL2 hgrad hfluxb

omit [NeZero d] in
/-- **The averaged energy density is nonnegative through the a.e. representative.**  If `b`
agrees almost everywhere on a measurable set `U` with a field `f` pointwise elliptic on `U`
with lower constant `lam > 0`, then the volume average over `U` of
`x ↦ ∇u(x) · b(x) ∇u(x)` is nonnegative.  On the full-measure set where `b = f`, the integrand
is bounded below by `lam * ‖∇u(x)‖²`, hence nonnegative, and `integral_nonneg_of_ae` gives the
sign of the average. -/
theorem h6a_volumeAverage_energyDensity_nonneg_of_aeEq {U : Set (Vec d)}
    (hU : MeasurableSet U) {b f : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U f) (hbf : b =ᵐ[volumeMeasureOn U] f)
    (u : AHarmonicFunction b U) :
    0 ≤ volumeAverage U (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2) := by
  unfold volumeAverage
  refine mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) ?_
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [hbf, MeasureTheory.ae_restrict_mem hU] with x hxb hxU
  simp only [optimizerField]
  rw [hxb]
  have hlow := (hEll.2 x hxU).2.2.1 (u.toH1.grad x)
  have hnn : 0 ≤ lam * vecNormSq (u.toH1.grad x) := mul_nonneg hlam.le (vecNormSq_nonneg _)
  exact le_trans hnn hlow

/-! ## The recentred coefficient `a_- = respCoeffMinus F a` -/

/-- **Integrability of both slots of the doubled optimizer field on a triadic subcell, for
`respCoeffMinus F a`.**  For an invertible grid `q`, generation `t` and depth `n`, both slots of
the doubled optimizer field of an arbitrary `AHarmonicFunction` attached to `respCoeffMinus F a`
on `HighContrast.adaptedCell q t` are integrable on every aligned depth-`n` subcell
`adaptedCellAtCenter q (t - n) w`.  The gradient slot needs no ellipticity; the flux slot uses the
a.e.-elliptic representative on the subcell. -/
theorem h6a_integrableOn_optimizerField_respCoeffMinus_box (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t))
    (n : ℕ) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d n) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ)) w).isFiniteMeasure_restrict_volume
  have hVmeas : MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    IsEllipticFieldOn.mono hEll hVmeas hVU
  have hflux : MemVectorL2 (adaptedCellAtCenter q (t - (n : ℤ)) w)
      (fun x => matVecMul ((respCoeffMinus F a) x) (u.toH1.grad x)) :=
    h6a_memVectorL2_optimizerField_flux_of_aeEq hVU hEllV hae u
  refine ⟨h6a_integrableOn_optimizerField_fst_pub hVU hVfin (respCoeffMinus F a) u j, ?_⟩
  have hmem : MemLp (fun x => (optimizerField (respCoeffMinus F a) u x).2 j) 2
      (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [optimizerField] using (MeasureTheory.memLp_pi_iff.mp hflux) j
  exact MemLp.integrable (by norm_num) hmem

/-- **Integrability of the scalar energy density on the parent cell, for
`respCoeffMinus F a`.**  The energy density `x ↦ ∇u(x) · (respCoeffMinus F a)(x) ∇u(x)` of an
arbitrary `AHarmonicFunction` attached to `respCoeffMinus F a` on the adapted cell is integrable
there. -/
theorem h6a_integrableOn_energyDensity_respCoeffMinus (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t)) :
    IntegrableOn (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
      (optimizerField (respCoeffMinus F a) u x).2) (HighContrast.adaptedCell q t) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  exact h6a_integrableOn_energyDensity_of_aeEq hEll hae u

/-- **Nonnegativity of the averaged energy density, for `respCoeffMinus F a`.**  The volume
average over the adapted cell of the energy density of an arbitrary `AHarmonicFunction` attached
to `respCoeffMinus F a` is nonnegative. -/
theorem h6a_energyDensity_average_nonneg (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (HighContrast.adaptedCell q t)) :
    0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (fun x => vecDot (optimizerField (respCoeffMinus F a) u x).1
        (optimizerField (respCoeffMinus F a) u x).2) := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffMinus q hq t F a
  exact h6a_volumeAverage_energyDensity_nonneg_of_aeEq
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen.measurableSet hlam hEll hae u

/-! ## The transposed recentred coefficient `a_+ = respCoeffPlus F a` -/

/-- **Integrability of both slots of the doubled optimizer field on a triadic subcell, for
`respCoeffPlus F a`.**  The transposed twin of
`h6a_integrableOn_optimizerField_respCoeffMinus_box`. -/
theorem h6a_integrableOn_optimizerField_respCoeffPlus_box (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t))
    (n : ℕ) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d n) (j : Fin d) :
    IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).1 j)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) ∧
      IntegrableOn (fun x => (optimizerField (respCoeffPlus F a) u x).2 j)
        (adaptedCellAtCenter q (t - (n : ℤ)) w) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  have hVU : adaptedCellAtCenter q (t - (n : ℤ)) w ⊆ HighContrast.adaptedCell q t :=
    adaptedCellAtCenter_subset_adaptedCell q t n hw
  have hVfin : volume (adaptedCellAtCenter q (t - (n : ℤ)) w) ≠ ⊤ :=
    Geometry.volume_adaptedCellAtCenter_ne_top q (t - (n : ℤ)) w
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_adaptedCellAtCenter q hq (t - (n : ℤ)) w).isFiniteMeasure_restrict_volume
  have hVmeas : MeasurableSet (adaptedCellAtCenter q (t - (n : ℤ)) w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hEllV : IsEllipticFieldOn lam Lam (adaptedCellAtCenter q (t - (n : ℤ)) w) f :=
    IsEllipticFieldOn.mono hEll hVmeas hVU
  have hflux : MemVectorL2 (adaptedCellAtCenter q (t - (n : ℤ)) w)
      (fun x => matVecMul ((respCoeffPlus F a) x) (u.toH1.grad x)) :=
    h6a_memVectorL2_optimizerField_flux_of_aeEq hVU hEllV hae u
  refine ⟨h6a_integrableOn_optimizerField_fst_pub hVU hVfin (respCoeffPlus F a) u j, ?_⟩
  have hmem : MemLp (fun x => (optimizerField (respCoeffPlus F a) u x).2 j) 2
      (volumeMeasureOn (adaptedCellAtCenter q (t - (n : ℤ)) w)) := by
    simpa [optimizerField] using (MeasureTheory.memLp_pi_iff.mp hflux) j
  exact MemLp.integrable (by norm_num) hmem

/-- **Integrability of the scalar energy density on the parent cell, for `respCoeffPlus F a`.**
The transposed twin of `h6a_integrableOn_energyDensity_respCoeffMinus`. -/
theorem h6a_integrableOn_energyDensity_respCoeffPlus (q : Mat d) (hq : IsUnit q)
    (t : ℤ) (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t)) :
    IntegrableOn (fun x => vecDot (optimizerField (respCoeffPlus F a) u x).1
      (optimizerField (respCoeffPlus F a) u x).2) (HighContrast.adaptedCell q t) := by
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  exact h6a_integrableOn_energyDensity_of_aeEq hEll hae u

/-- **Nonnegativity of the averaged energy density, for `respCoeffPlus F a`.**  The transposed
twin of `h6a_energyDensity_average_nonneg`. -/
theorem h6a_energyDensity_average_nonneg_plus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffPlus F a) (HighContrast.adaptedCell q t)) :
    0 ≤ volumeAverage (HighContrast.adaptedCell q t)
      (fun x => vecDot (optimizerField (respCoeffPlus F a) u x).1
        (optimizerField (respCoeffPlus F a) u x).2) := by
  obtain ⟨lam, Lam, f, hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_respCoeffPlus q hq t F a
  exact h6a_volumeAverage_energyDensity_nonneg_of_aeEq
    (adaptedCell_isOpenBoundedConvexDomain q hq t).isOpen.measurableSet hlam hEll hae u

end

end Homogenization.HighContrast.Multiscale
