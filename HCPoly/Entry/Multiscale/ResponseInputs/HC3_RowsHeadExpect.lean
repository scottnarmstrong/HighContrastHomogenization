import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsCSIntegral

/-!
# The expectation of the squared two-term head

For a measure `P` and integrable nonnegative functions `f` and `g`, the expectation of the square
of the sum of the two square roots is bounded by the square of the sum of the square roots of the
expectations:

`∫ (√f + √g)^2 ≤ (√(∫ f) + √(∫ g))^2`.

Expanding the square, the two pure terms integrate to the annealed quantities `∫ f` and `∫ g`,
while the cross term is controlled in the sample by the annealed Cauchy--Schwarz inequality
`integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt`; the pieces reassemble into the square of the sum of the
square roots of the annealed quantities.  This is how the pathwise head of the direct full-dual
pairing is dominated by the head of `respSourceLoad`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The expectation of the squared two-term head: if `f` and `g` are integrable and nonnegative
and the square `(√f + √g)^2` is integrable, then
`∫ (√f + √g)^2 ≤ (√(∫ f) + √(∫ g))^2`.  The square is expanded pointwise into
`f + g + 2 √f √g`, the two pure terms integrate to `∫ f` and `∫ g`, and the cross term is bounded
by the annealed Cauchy--Schwarz inequality `integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt`; the result
recombines into the square of the sum of the square roots of the annealed quantities.  This is the
estimate behind the head of `respSourceLoad` in the first error row of `e.response.cutoff.estimate`.
-/
theorem integral_sq_sqrt_add_sqrt_le {alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) {f g : alpha → ℝ}
    (hf : Integrable f P) (hg : Integrable g P)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a)
    (hfg : Integrable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P)
    (hsq : Integrable (fun a => (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2) P) :
    (∫ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2 ∂P)
      ≤ (Real.sqrt (∫ a, f a ∂P) + Real.sqrt (∫ a, g a ∂P)) ^ 2 := by
  have hpt : ∀ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2
      = f a + g a + 2 * (Real.sqrt (f a) * Real.sqrt (g a)) := by
    intro a
    rw [add_sq, Real.sq_sqrt (hf0 a), Real.sq_sqrt (hg0 a)]
    ring
  have hsum : Integrable (fun a => f a + g a + 2 * (Real.sqrt (f a) * Real.sqrt (g a))) P :=
    hsq.congr (Filter.Eventually.of_forall fun a => hpt a)
  have hcross : Integrable (fun a => 2 * (Real.sqrt (f a) * Real.sqrt (g a))) P :=
    (hsum.sub (hf.add hg)).congr (Filter.Eventually.of_forall fun a => by
      show (f a + g a + 2 * (Real.sqrt (f a) * Real.sqrt (g a))) - (f a + g a)
        = 2 * (Real.sqrt (f a) * Real.sqrt (g a))
      ring)
  have hA0 : 0 ≤ ∫ a, f a ∂P := integral_nonneg fun a => hf0 a
  have hB0 : 0 ≤ ∫ a, g a ∂P := integral_nonneg fun a => hg0 a
  have hLHS : (∫ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2 ∂P)
      = (∫ a, f a ∂P) + (∫ a, g a ∂P)
        + 2 * (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) := by
    calc (∫ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2 ∂P)
        = ∫ a, f a + g a + 2 * (Real.sqrt (f a) * Real.sqrt (g a)) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun a => hpt a)
      _ = (∫ a, f a + g a ∂P)
          + ∫ a, 2 * (Real.sqrt (f a) * Real.sqrt (g a)) ∂P :=
          integral_add (hf.add hg) hcross
      _ = (∫ a, f a ∂P) + (∫ a, g a ∂P)
          + 2 * (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) := by
          rw [integral_add hf hg, integral_const_mul]
  have hCS : (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P)
      ≤ Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) :=
    integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt P hf hg hf0 hg0 hfg
  have hRHS : (Real.sqrt (∫ a, f a ∂P) + Real.sqrt (∫ a, g a ∂P)) ^ 2
      = (∫ a, f a ∂P) + (∫ a, g a ∂P)
        + 2 * (Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P)) := by
    rw [add_sq, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
    ring
  calc (∫ a, (Real.sqrt (f a) + Real.sqrt (g a)) ^ 2 ∂P)
      = (∫ a, f a ∂P) + (∫ a, g a ∂P)
        + 2 * (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) := hLHS
    _ ≤ (∫ a, f a ∂P) + (∫ a, g a ∂P)
        + 2 * (Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P)) := by linarith [hCS]
    _ = (Real.sqrt (∫ a, f a ∂P) + Real.sqrt (∫ a, g a ∂P)) ^ 2 := hRHS.symm

end

end Homogenization.HighContrast.Multiscale
