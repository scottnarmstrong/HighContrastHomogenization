import HCPoly.Entry.Multiscale.ResponseInputs.HC3_DirectCellQuad

/-!
# The per-depth annealed readouts of the descendant sum are integrable

The oscillation half of the cutoff-mean row of `p.response.transfer`, in its dominated form, asks
for five `P`-integrabilities at every refinement depth: the flat average of the squared pathwise
head, the flat average of the doubled cell energies, the product of the square roots of those two
flat averages, the weighted flat average of their per-cell product, and the generation increment
itself.  Each is a finite normalized sum of per-cell readouts, and the only non-algebraic step is
the crossed product of square roots, which is dominated by the arithmetic mean of the moduli.

This module records the five reductions once and for all, so that the carrier instantiation has to
supply only the three per-cell integrabilities — the squared head, the cell energy and the crossed
pairing.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {α : Type*} [MeasurableSpace α] {P : Measure α} {d : ℕ}

/-- **The flat average of the squared pathwise head is integrable.** -/
theorem integrable_avsum_sq_head (Z : ℕ → Finset (Fin d → ℤ)) (G : ℕ → (Fin d → ℤ) → α → ℝ)
    (hGsqI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => (G n W a) ^ 2) P) (n : ℕ) :
    Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) P :=
  integrable_avsum (Z n) (fun W a => (G n W a) ^ 2) (hGsqI n)

/-- **The flat average of the doubled cell energies is integrable.** -/
theorem integrable_avsum_two_mul_energy (Z : ℕ → Finset (Fin d → ℤ))
    (D : ℕ → (Fin d → ℤ) → α → ℝ)
    (hDI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => D n W a) P) (n : ℕ) :
    Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) P :=
  integrable_avsum (Z n) (fun W a => 2 * D n W a) (fun W hW => (hDI n W hW).const_mul 2)

/-- **The Cauchy--Schwarz middle term is integrable.**  The product of the square roots of the two
flat averages is dominated by the arithmetic mean of their moduli. -/
theorem integrable_sqrt_avsum_mul_sqrt_avsum (Z : ℕ → Finset (Fin d → ℤ))
    (G D : ℕ → (Fin d → ℤ) → α → ℝ)
    (hGsqI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => (G n W a) ^ 2) P)
    (hDI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => D n W a) P) (n : ℕ) :
    Integrable (fun a =>
      Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a)) P :=
  integrable_sqrt_mul_sqrt' (integrable_avsum_sq_head Z G hGsqI n)
    (integrable_avsum_two_mul_energy Z D hDI n)

/-- **The weighted flat average of the per-cell products is integrable.** -/
theorem integrable_avsum_weighted_sqrt_mul_sqrt (Z : ℕ → Finset (Fin d → ℤ))
    (θ : ℕ → (Fin d → ℤ) → ℝ) (G D : ℕ → (Fin d → ℤ) → α → ℝ)
    (hGsqI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => (G n W a) ^ 2) P)
    (hDI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => D n W a) P) (n : ℕ) :
    Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
      θ n W * (Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a))) P :=
  integrable_avsum (Z n)
    (fun W a => θ n W * (Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a)))
    (fun W hW => (integrable_sqrt_mul_sqrt' (hGsqI n W hW)
      ((hDI n W hW).const_mul 2)).const_mul (θ n W))

/-- **The generation increment is integrable.**  It is the weighted flat average of the per-cell
crossed pairings. -/
theorem integrable_avsum_weighted_pairing (Z : ℕ → Finset (Fin d → ℤ))
    (θ : ℕ → (Fin d → ℤ) → ℝ) (pairing : ℕ → (Fin d → ℤ) → α → ℝ)
    (hPairI : ∀ (n : ℕ), ∀ W ∈ Z n, Integrable (fun a => pairing n W a) P) (n : ℕ) :
    Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a) P :=
  integrable_avsum (Z n) (fun W a => θ n W * pairing n W a)
    (fun W hW => (hPairI n W hW).const_mul (θ n W))

end

end Homogenization.HighContrast.Multiscale
