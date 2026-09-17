import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# Expectation of a pathwise coarse-block quadratic form

The quadratic form of a coarse block `𝐀(V; b a)` in a fixed vector is a finite linear combination
of the entries of the block.  The Bochner integral therefore commutes with the quadratic form, and
the expectation of the pathwise form is the form of the annealed block `E[𝐀(V; b)]`.  These are the
identities at which the expectation lands on the diagonal blocks used by the source load of
`p.response.transfer`, so that the load is read from `E[𝐀(V; b)]` rather than from a pointwise
Cauchy--Schwarz bound.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The expectation of the upper-left pathwise quadratic form is the annealed quadratic form.**
For an integrable family of coarse blocks, the expectation of `Y · (𝐀(V; b a).upperLeft) Y` equals
`Y · (E[𝐀(V; b)].upperLeft) Y`, the quadratic form of the upper-left diagonal block of the
annealed block that defines the source load of `p.response.transfer`. -/
theorem integral_vecDot_coarseBlock_upperLeft {d : ℕ} (P : Measure (CoeffSpace d))
    (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d) (Y : Vec d)
    (hint : ∀ i j, Integrable (fun a => (coarseBlockMatrix V (b a)).upperLeft i j) P) :
    (∫ a, vecDot Y (matVecMul (coarseBlockMatrix V (b a)).upperLeft Y) ∂P)
      = vecDot Y (matVecMul (annealedBlockOf P V b).upperLeft Y) := by
  have hrow : ∀ i : Fin d, Integrable (fun a => ∑ j : Fin d,
      Y i * ((coarseBlockMatrix V (b a)).upperLeft i j * Y j)) P :=
    fun i => integrable_finsetSum _ fun j _ =>
      ((hint i j).mul_const (Y j)).const_mul (Y i)
  unfold vecDot matVecMul annealedBlockOf
  simp only [Matrix.of_apply, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hrow i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hint i j).mul_const (Y j)).const_mul (Y i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

/-- **The expectation of the lower-right pathwise quadratic form is the annealed quadratic form.**
For an integrable family of coarse blocks, the expectation of `Y · (𝐀(V; b a).lowerRight) Y` equals
`Y · (E[𝐀(V; b)].lowerRight) Y`, the quadratic form of the lower-right diagonal block of the
annealed block that defines the source load of `p.response.transfer`. -/
theorem integral_vecDot_coarseBlock_lowerRight {d : ℕ} (P : Measure (CoeffSpace d))
    (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d) (Y : Vec d)
    (hint : ∀ i j, Integrable (fun a => (coarseBlockMatrix V (b a)).lowerRight i j) P) :
    (∫ a, vecDot Y (matVecMul (coarseBlockMatrix V (b a)).lowerRight Y) ∂P)
      = vecDot Y (matVecMul (annealedBlockOf P V b).lowerRight Y) := by
  have hrow : ∀ i : Fin d, Integrable (fun a => ∑ j : Fin d,
      Y i * ((coarseBlockMatrix V (b a)).lowerRight i j * Y j)) P :=
    fun i => integrable_finsetSum _ fun j _ =>
      ((hint i j).mul_const (Y j)).const_mul (Y i)
  unfold vecDot matVecMul annealedBlockOf
  simp only [Matrix.of_apply, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hrow i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hint i j).mul_const (Y j)).const_mul (Y i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

end

end Homogenization.HighContrast.Multiscale
