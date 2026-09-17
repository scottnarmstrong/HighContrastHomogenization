import HCPoly.Entry.Multiscale.ResponseInputs.H8bEllipticInput
import HCPoly.Entry.Multiscale.ResponseInputs.HC2_WeakSeminorm

/-!
# Square integrability of the doubled optimizer state on an adapted cell

The scale-average seminorm bound of `e.response.weak.estimate` is applied to the doubled
optimizer state `M_0^{1/2}\bigl((\nabla v, a\nabla v) - Y\bigr)` on an adapted cell.  Its
hypothesis is that the squared Euclidean length of that state is integrable on the cell, and
this file supplies that hypothesis.

The gradient slot is square integrable because the optimizer is an `H^1` function; the flux slot
is square integrable because the coefficient is uniformly elliptic on the cell after modification
on a null set, which is the form in which a qualitatively locally uniformly elliptic sample
provides ellipticity; the constant `Y` is square integrable because the cell has finite measure;
and a constant block matrix carries square integrable coordinates to square integrable
coordinates.

Paper: `e.response.weak.estimate`, and the normalization of the doubled state that precedes it.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Coordinatewise square integrability -/

/-- If every coordinate of a doubled field is square integrable, its squared Euclidean length is
integrable. -/
theorem memLp_one_blockVecDot_self_of_coords {V : Set (Vec d)} {W : Vec d → BlockVec d}
    (h1 : ∀ i, MemLp (fun x => (W x).1 i) 2 (volume.restrict V))
    (h2 : ∀ i, MemLp (fun x => (W x).2 i) 2 (volume.restrict V)) :
    MemLp (fun x => blockVecDot (W x) (W x)) 1 (volume.restrict V) := by
  rw [memLp_one_iff_integrable]
  have hs1 : Integrable (fun x => ∑ i, (W x).1 i * (W x).1 i) (volume.restrict V) := by
    refine integrable_finsetSum _ fun i _ => ?_
    simpa [Pi.mul_def] using (h1 i).integrable_mul (h1 i)
  have hs2 : Integrable (fun x => ∑ i, (W x).2 i * (W x).2 i) (volume.restrict V) := by
    refine integrable_finsetSum _ fun i _ => ?_
    simpa [Pi.mul_def] using (h2 i).integrable_mul (h2 i)
  simpa only [blockVecDot, vecDot] using! hs1.add hs2

/-- A constant block matrix carries a doubled field with square integrable coordinates to a
doubled field with square integrable coordinates. -/
theorem memLp_two_coords_blockMatVecMul {V : Set (Vec d)} (S : BlockMat d)
    {Z : Vec d → BlockVec d}
    (h1 : ∀ i, MemLp (fun x => (Z x).1 i) 2 (volume.restrict V))
    (h2 : ∀ i, MemLp (fun x => (Z x).2 i) 2 (volume.restrict V)) :
    (∀ i, MemLp (fun x => (blockMatVecMul S (Z x)).1 i) 2 (volume.restrict V)) ∧
      ∀ i, MemLp (fun x => (blockMatVecMul S (Z x)).2 i) 2 (volume.restrict V) := by
  have key : ∀ (A B : Mat d) (i : Fin d),
      MemLp (fun x => (∑ j, A i j * (Z x).1 j) + ∑ j, B i j * (Z x).2 j) 2
        (volume.restrict V) := by
    intro A B i
    refine MemLp.add ?_ ?_
    · exact memLp_finsetSum _ (fun j _ => (h1 j).const_mul (A i j))
    · exact memLp_finsetSum _ (fun j _ => (h2 j).const_mul (B i j))
  constructor
  · intro i
    simpa only [blockMatVecMul, matVecMul, Pi.add_apply] using key S.upperLeft S.upperRight i
  · intro i
    simpa only [blockMatVecMul, matVecMul, Pi.add_apply] using key S.lowerLeft S.lowerRight i

/-! ## The doubled optimizer state -/

/-- Both slots of the centred doubled optimizer field are square integrable on an adapted cell,
for a coefficient that agrees almost everywhere on the cell with a uniformly elliptic field. -/
theorem memLp_two_coords_optimizerField_sub_const [NeZero d] {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hbf : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t)) (Y : BlockVec d) :
    (∀ i, MemLp (fun x => (optimizerField b u x - Y).1 i) 2
        (volume.restrict (HighContrast.adaptedCell q t))) ∧
      ∀ i, MemLp (fun x => (optimizerField b u x - Y).2 i) 2
        (volume.restrict (HighContrast.adaptedCell q t)) := by
  have : IsFiniteMeasure (volume.restrict (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using
      (adaptedCell_isOpenBoundedConvexDomain q hq t).isFiniteMeasure_restrict_volume
  have hgrad : ∀ i, MemLp (fun x => u.toH1.grad x i) 2
      (volume.restrict (HighContrast.adaptedCell q t)) := fun i => u.toH1.gradMemL2 i
  have hfluxf : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x))
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        fun x => matVecMul (b x) (u.toH1.grad x) := by
    filter_upwards [hbf] with x hx
    rw [hx]
  have hfluxb : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (b x) (u.toH1.grad x)) := (memLp_congr_ae hae).mp hfluxf
  have hflux : ∀ i, MemLp (fun x => matVecMul (b x) (u.toH1.grad x) i) 2
      (volume.restrict (HighContrast.adaptedCell q t)) := fun i =>
    (memLp_pi_iff.mp hfluxb) i
  constructor
  · intro i
    simpa only [optimizerField, Prod.fst_sub, Pi.sub_apply] using!
      (hgrad i).sub (memLp_const (Y.1 i))
  · intro i
    simpa only [optimizerField, Prod.snd_sub, Pi.sub_apply] using!
      (hflux i).sub (memLp_const (Y.2 i))

end

end Homogenization.HighContrast.Multiscale
