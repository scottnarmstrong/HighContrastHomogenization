import Homogenization.Ambient.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Sample integrability of the quadratic readouts of a coarse block

The cell half and the oscillation half of the cutoff-mean row of `p.response.transfer` read the
pathwise coarse block only through four scalars: the two diagonal quadratic forms against the
deterministic dual variable, their crossed product of square roots, and the square of their sum.
All four are integrable as soon as the entries of the block are, because the quadratic form is a
fixed real linear combination of the entries and the crossed product of square roots is dominated
by the arithmetic mean of the two forms.

This module records those four steps, together with the two bookkeeping facts the rows consume
about flat averages of integrable families and about domination by an absolute value.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

/-- **Domination by an integrable envelope.**  A measurable function whose modulus is bounded by an
integrable function is integrable. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hmeas : AEStronglyMeasurable f P) (hg : Integrable g P) (h : ∀ a, |f a| ≤ g a) :
    Integrable f P := by
  refine hg.mono' hmeas ?_
  filter_upwards with a
  rw [Real.norm_eq_abs]
  exact h a

/-- **Integrability of a flat average of an integrable family.**  A normalized finite sum of
`P`-integrable functions is `P`-integrable. -/
theorem integrable_avsum {α ι : Type*} [MeasurableSpace α] {P : Measure α} (Z : Finset ι)
    (h : ι → α → ℝ) (hh : ∀ w ∈ Z, Integrable (h w) P) :
    Integrable (fun a => ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, h w a) P :=
  (integrable_finsetSum Z hh).const_mul _

/-- **The crossed product of square roots of two nonnegative integrable functions is
integrable.**  The product is dominated by the arithmetic mean of the two functions, by the
nonnegativity of the square of the difference of the square roots. -/
theorem integrable_sqrt_mul_sqrt_gen {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a) (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P := by
  have hmeas : AEStronglyMeasurable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.1)
  refine integrable_of_abs_le hmeas ((hf.add hg).const_mul (1 / 2 : ℝ)) ?_
  intro a
  have hsq : (Real.sqrt (f a) - Real.sqrt (g a)) ^ 2
      = f a - 2 * (Real.sqrt (f a) * Real.sqrt (g a)) + g a := by
    rw [sub_sq, Real.sq_sqrt (hf0 a), Real.sq_sqrt (hg0 a)]
    ring
  have hnn : 0 ≤ (Real.sqrt (f a) - Real.sqrt (g a)) ^ 2 := sq_nonneg _
  rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  simp only [Pi.add_apply]
  linarith only [hnn, hsq]

/-- **The crossed product of square roots is integrable without a sign hypothesis.**  The square
root of a negative number is zero, so the product is bounded by the crossed product of the square
roots of the moduli, and the previous domination applies to those. -/
theorem integrable_sqrt_mul_sqrt' {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P := by
  have habs := integrable_sqrt_mul_sqrt_gen (P := P) (f := fun a => |f a|) (g := fun a => |g a|)
    (fun a => abs_nonneg _) (fun a => abs_nonneg _) hf.abs hg.abs
  refine integrable_of_abs_le ?_ habs ?_
  · exact (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.1)
  · intro a
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul (Real.sqrt_le_sqrt (le_abs_self _)) (Real.sqrt_le_sqrt (le_abs_self _))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- **The square of the sum of the two square roots is integrable.**  Expanding the square gives
the two functions plus twice their crossed product of square roots. -/
theorem integrable_sq_sqrt_add_sqrt_gen {α : Type*} [MeasurableSpace α] {P : Measure α}
    {f g : α → ℝ} (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a)
    (hf : Integrable f P) (hg : Integrable g P) :
    Integrable (fun a => (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2) P := by
  have hcross := integrable_sqrt_mul_sqrt_gen hf0 hg0 hf hg
  have hsum : Integrable (fun a => f a + 2 * (Real.sqrt (f a) * Real.sqrt (g a)) + g a) P :=
    (hf.add (hcross.const_mul 2)).add hg
  refine hsum.congr ?_
  filter_upwards with a
  rw [add_sq, Real.sq_sqrt (hf0 a), Real.sq_sqrt (hg0 a)]
  ring

/-- **The quadratic form of a matrix family against a fixed vector is integrable.**  The form is
the fixed real linear combination `∑ i ∑ k, Y i * M i k * Y k` of the entries. -/
theorem integrable_vecDot_matVecMul {d : ℕ} {α : Type*} [MeasurableSpace α] {P : Measure α}
    (M : α → Mat d) (Y : Vec d) (hM : ∀ i k : Fin d, Integrable (fun a => M a i k) P) :
    Integrable (fun a => vecDot Y (matVecMul (M a) Y)) P := by
  have hEq : (fun a => vecDot Y (matVecMul (M a) Y))
      = fun a => ∑ i : Fin d, ∑ k : Fin d, Y i * (M a i k * Y k) := by
    funext a
    simp only [vecDot, matVecMul, Finset.mul_sum]
  rw [hEq]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => ?_
  exact ((hM i k).mul_const (Y k)).const_mul (Y i)

end Homogenization.HighContrast.Multiscale
