import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportWeak

/-!
# Passing a pathwise cutoff bound through the law

The weak response energy `respWeakEnergy` bounds the scale-weighted squared scale-average
seminorm of the doubled optimizer state, uniformly over admissible families of cell
maximizers.  This file records the elementary integration step that turns a bound holding at
each sample into a bound on the expectation: if a pathwise quantity is dominated by a
nonnegative multiple of that seminorm square, and the seminorm square is Bochner integrable,
then the expectation of the absolute value of the quantity is bounded by the same multiple of
the weak response energy.  This is the integration in the sample variable `a` of the weak
estimate `e.response.weak.estimate`.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- If a pathwise quantity `G` is dominated, sample by sample, by `C₀` times the
scale-weighted squared scale-average seminorm of the doubled optimizer state of an admissible
family of cell maximizers, with `C₀ ≥ 0`, and that seminorm square is Bochner integrable, then
the expectation of `|G|` is at most `C₀` times the weak response energy `W`.  The integrability
hypothesis is what makes the dominating function Bochner integrable, so that monotonicity of the
integral applies; the branch where `|G|` is not integrable is handled by the junk value of the
Bochner integral and the nonnegativity of `W`.  This is the annealed form of
`e.response.weak.estimate`. -/
theorem integral_abs_le_respWeakEnergy_of_pathwise {d : ℕ}
    (P : Measure (CoeffSpace d)) (qq : Mat d) (t : ℤ) (M0 : BlockMat d) (p q' : Vec d)
    (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) (G : CoeffSpace d → ℝ)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hbdd : BddAbove (respWeakEnergySet P qq t M0 p q' b Y))
    (u : (a : CoeffSpace d) → AHarmonicFunction (b a) (HighContrast.adaptedCell qq t))
    (hu : ∀ a, IsResponseMaximizer (HighContrast.adaptedCell qq t) p q' (b a) (u a))
    (hintegrable : Integrable (fun a => besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt M0)
          (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
            (optimizerField (b a) (u a)) - Y)) ^ 2) P)
    (hptwise : ∀ a : CoeffSpace d, |G a| ≤
      C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt M0)
          (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
            (optimizerField (b a) (u a)) - Y)) ^ 2)) :
    (∫ a, |G a| ∂P) ≤ C₀ * respWeakEnergy P qq t M0 p q' b Y := by
  set Gsq : CoeffSpace d → ℝ := fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt M0)
        (cellAverage (adaptedCellAtCenter qq (t - (n : ℤ)) z)
          (optimizerField (b a) (u a)) - Y)) ^ 2
  have hsup : (3 : ℝ) ^ (-(t : ℝ)) * ∫ a, Gsq a ∂P ≤ respWeakEnergy P qq t M0 p q' b Y :=
    le_respWeakEnergy P qq t M0 p q' b Y hbdd u hu
  by_cases hI : Integrable (fun a => |G a|) P
  · have hIg : Integrable (fun a => C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * Gsq a)) P :=
      (hintegrable.const_mul ((3 : ℝ) ^ (-(t : ℝ)))).const_mul C₀
    calc (∫ a, |G a| ∂P)
        ≤ ∫ a, C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * Gsq a) ∂P := integral_mono hI hIg hptwise
      _ = C₀ * ((3 : ℝ) ^ (-(t : ℝ)) * ∫ a, Gsq a ∂P) := by
          rw [integral_const_mul, integral_const_mul]
      _ ≤ C₀ * respWeakEnergy P qq t M0 p q' b Y := mul_le_mul_of_nonneg_left hsup hC₀
  · rw [integral_undef hI]
    exact mul_nonneg hC₀ (respWeakEnergy_nonneg P qq t M0 p q' b Y)

end

end Homogenization.HighContrast.Multiscale
