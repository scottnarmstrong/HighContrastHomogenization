import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cauchy--Schwarz for the square roots of two integrable functions

For a measure `P` and integrable nonnegative functions `f` and `g`, the integral of the product of
the square roots is bounded by the product of the square roots of the integrals:

`∫ √f √g ≤ √(∫ f) · √(∫ g)`.

This is the annealed Cauchy--Schwarz inequality behind the cell part of the first error row of
`e.response.cutoff.estimate`: it compares the difference energy `f` with the cell energy `g` of
the sample.  The proof integrates the pointwise Young inequality
`√f √g ≤ (lam f + g / lam) / 2` against the measure; the optimal choice of `lam` reproduces the
geometric mean `√(∫ f) · √(∫ g)`.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Cauchy--Schwarz for the square roots of two integrable functions: if `f` and `g` are integrable
and nonnegative, then `∫ √f √g ≤ √(∫ f) · √(∫ g)`.  The pointwise Young inequality
`2 √(f a) √(g a) ≤ lam f a + g a / lam` is integrated against `P`, and the parameter `lam` is then
chosen as `√(∫ g) / √(∫ f)`; when one of the integrals vanishes, the corresponding function vanishes
almost everywhere and so does the product.  This is the annealed Cauchy--Schwarz inequality behind
the cell part of the first error row of `e.response.cutoff.estimate`. -/
theorem integral_sqrt_mul_sqrt_le_sqrt_mul_sqrt {alpha : Type*} [MeasurableSpace alpha]
    (P : Measure alpha) {f g : alpha → ℝ}
    (hf : Integrable f P) (hg : Integrable g P)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a)
    (hfg : Integrable (fun a => Real.sqrt (f a) * Real.sqrt (g a)) P) :
    (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P)
      ≤ Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
  have hA0 : 0 ≤ ∫ a, f a ∂P := integral_nonneg fun a => hf0 a
  have hB0 : 0 ≤ ∫ a, g a ∂P := integral_nonneg fun a => hg0 a
  have hR0 : 0 ≤ Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hA0 with hA | hA
  · -- `∫ f = 0`, so `f` vanishes almost everywhere and the product has zero integral.
    have hfae : f =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun a => hf0 a) hf).mp hA.symm
    have hprodae : (fun a => Real.sqrt (f a) * Real.sqrt (g a)) =ᵐ[P] 0 :=
      hfae.mono fun a ha => by
        show Real.sqrt (f a) * Real.sqrt (g a) = 0
        simp only [ha, Pi.zero_apply, Real.sqrt_zero, zero_mul]
    have hI : (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) = 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun a => mul_nonneg (Real.sqrt_nonneg (f a)) (Real.sqrt_nonneg (g a))) hfg).mpr hprodae
    exact hI.trans_le hR0
  · rcases eq_or_lt_of_le hB0 with hB | hB
    · -- `∫ g = 0`, symmetric.
      have hgae : g =ᵐ[P] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun a => hg0 a) hg).mp hB.symm
      have hprodae : (fun a => Real.sqrt (f a) * Real.sqrt (g a)) =ᵐ[P] 0 :=
        hgae.mono fun a ha => by
          show Real.sqrt (f a) * Real.sqrt (g a) = 0
          simp only [ha, Pi.zero_apply, Real.sqrt_zero, mul_zero]
      have hI : (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P) = 0 :=
        (integral_eq_zero_iff_of_nonneg
          (fun a => mul_nonneg (Real.sqrt_nonneg (f a)) (Real.sqrt_nonneg (g a))) hfg).mpr hprodae
      exact hI.trans_le hR0
    · -- Both integrals are positive: integrate the pointwise Young inequality.
      set lam : ℝ := Real.sqrt (∫ a, g a ∂P) / Real.sqrt (∫ a, f a ∂P) with hlamdef
      have hlam : 0 < lam := by
        rw [hlamdef]
        exact div_pos (Real.sqrt_pos.mpr hB) (Real.sqrt_pos.mpr hA)
      have hpt : ∀ a, Real.sqrt (f a) * Real.sqrt (g a)
          ≤ (lam * f a + g a / lam) / 2 := by
        intro a
        have hmul : 2 * lam * (Real.sqrt (f a) * Real.sqrt (g a))
            ≤ lam ^ 2 * f a + g a := by
          have h := sq_nonneg (lam * Real.sqrt (f a) - Real.sqrt (g a))
          nlinarith [h, Real.sq_sqrt (hf0 a), Real.sq_sqrt (hg0 a)]
        have heq : (lam ^ 2 * f a + g a) / (2 * lam) = (lam * f a + g a / lam) / 2 := by
          field_simp
        rw [← heq]
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * lam)]
        nlinarith [hmul]
      have hRint : Integrable (fun a => (lam * f a + g a / lam) / 2) P :=
        ((hf.const_mul lam).add (hg.div_const lam)).div_const 2
      have hmono : (∫ a, Real.sqrt (f a) * Real.sqrt (g a) ∂P)
          ≤ ∫ a, (lam * f a + g a / lam) / 2 ∂P :=
        integral_mono_ae hfg hRint (Filter.Eventually.of_forall hpt)
      have hint : (∫ a, (lam * f a + g a / lam) / 2 ∂P)
          = (lam * (∫ a, f a ∂P) + (∫ a, g a ∂P) / lam) / 2 := by
        rw [integral_div, integral_add (hf.const_mul lam) (hg.div_const lam),
          integral_const_mul, integral_div]
      have hAne : Real.sqrt (∫ a, f a ∂P) ≠ 0 := (Real.sqrt_pos.mpr hA).ne'
      have hBne : Real.sqrt (∫ a, g a ∂P) ≠ 0 := (Real.sqrt_pos.mpr hB).ne'
      have hA' : (∫ a, f a ∂P) = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, f a ∂P) := by
        rw [← sq]
        exact (Real.sq_sqrt hA0).symm
      have hB' : (∫ a, g a ∂P) = Real.sqrt (∫ a, g a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
        rw [← sq]
        exact (Real.sq_sqrt hB0).symm
      have hAd : (∫ a, f a ∂P) / Real.sqrt (∫ a, f a ∂P) = Real.sqrt (∫ a, f a ∂P) := by
        rw [div_eq_iff hAne]
        exact hA'
      have hBd : (∫ a, g a ∂P) / Real.sqrt (∫ a, g a ∂P) = Real.sqrt (∫ a, g a ∂P) := by
        rw [div_eq_iff hBne]
        exact hB'
      have hla : lam * (∫ a, f a ∂P)
          = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
        calc lam * (∫ a, f a ∂P)
            = (Real.sqrt (∫ a, g a ∂P) / Real.sqrt (∫ a, f a ∂P))
              * (∫ a, f a ∂P) := by rw [hlamdef]
          _ = Real.sqrt (∫ a, g a ∂P)
              * ((∫ a, f a ∂P) / Real.sqrt (∫ a, f a ∂P)) := by
              rw [div_mul_eq_mul_div, mul_div_assoc]
          _ = Real.sqrt (∫ a, g a ∂P) * Real.sqrt (∫ a, f a ∂P) := by rw [hAd]
          _ = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by ring
      have hlb : (∫ a, g a ∂P) / lam
          = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
        calc (∫ a, g a ∂P) / lam
            = (∫ a, g a ∂P) / (Real.sqrt (∫ a, g a ∂P) / Real.sqrt (∫ a, f a ∂P)) := by
              rw [hlamdef]
          _ = (∫ a, g a ∂P) * Real.sqrt (∫ a, f a ∂P) / Real.sqrt (∫ a, g a ∂P) := by
              rw [div_div_eq_mul_div]
          _ = ((∫ a, g a ∂P) / Real.sqrt (∫ a, g a ∂P)) * Real.sqrt (∫ a, f a ∂P) := by
              rw [div_mul_eq_mul_div]
          _ = Real.sqrt (∫ a, g a ∂P) * Real.sqrt (∫ a, f a ∂P) := by rw [hBd]
          _ = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by ring
      have hval : (lam * (∫ a, f a ∂P) + (∫ a, g a ∂P) / lam) / 2
          = Real.sqrt (∫ a, f a ∂P) * Real.sqrt (∫ a, g a ∂P) := by
        rw [hla, hlb]
        ring
      exact (hmono.trans_eq hint).trans_eq hval

end

end Homogenization.HighContrast.Multiscale
