import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65bMeasurable
import HCPoly.Entry.Setup.SelectionExponents
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrability of the all-scale envelope times the response

The all-scale maximum `ℳ = sup_{k <= t} 3^{-ρ(t-k)} max_z |(...)_+|` of
`p.response.transfer` dominates the normalized spectral defect of every
triadic cell at every depth, and the response estimate `e.response.weak.estimate` controls
its `Q`-th moment.  This file records the elementary consequence used when the envelope
multiplies a pathwise response: if `ℳ ^ Q` is `P`-integrable with `2 ≤ Q` and the response
`J` is square integrable, then `(1 + ℳ) J` is `P`-integrable.

Because `P` is a probability measure and `ℳ ≥ 0`, the pointwise bound
`ℳ ^ 2 ≤ 1 + ℳ ^ Q` (split at `ℳ = 1`) makes `ℳ` square integrable.  The product
`(1 + ℳ) J = J + ℳ J` is then a sum of integrable functions: `J` is integrable as an
`L²` function on a finite measure, and `ℳ J` is the product of two `L²` functions
(Hölder with conjugate exponents `2` and `2`).  The pathwise response is that of AK.HC (2.15).
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Integrability of `(1 + ℳ) J` from the envelope moment and square integrability of `J`.**
Let `ℳ = respAllScaleMax` be the all-scale maximum of `p.response.transfer`, let
`J` be measurable, and suppose `ℳ` is measurable, `ℳ ^ Q` is `P`-integrable with `2 ≤ Q`, and
`J ^ 2` is `P`-integrable.  Since `P` is a probability measure and `ℳ ≥ 0`, the bound
`ℳ ^ 2 ≤ 1 + ℳ ^ Q` gives `ℳ ∈ L²`; with `J ∈ L²` the product `ℳ J` is integrable by Hölder,
and `(1 + ℳ) J = J + ℳ J` is a sum of integrable functions. -/
private theorem integrable_one_add_respAllScaleMax_mul_of {d : ℕ} [NeZero d] (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hQ : 2 ≤ bigQ d γ)
    (J : CoeffSpace d → ℝ)
    (hJsq : Integrable (fun a => J a ^ 2) P)
    (hJmeas : AEStronglyMeasurable J P) :
    Integrable (fun a => (1 + respAllScaleMax P γ jStar F t a) * J a) P := by
  have hM2int : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ 2) P := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hMint) (hMmeas.pow 2) ?_
    filter_upwards with a
    have h0 : 0 ≤ respAllScaleMax P γ jStar F t a := respAllScaleMax_nonneg P γ jStar F t a
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 2)]
    simp only [Pi.add_apply]
    rcases le_or_gt (respAllScaleMax P γ jStar F t a) 1 with h1 | h1
    · have hsq : respAllScaleMax P γ jStar F t a ^ 2 ≤ 1 := by nlinarith
      have hQnn : (0 : ℝ) ≤ respAllScaleMax P γ jStar F t a ^ bigQ d γ := pow_nonneg h0 _
      linarith
    · have hsq : respAllScaleMax P γ jStar F t a ^ 2 ≤
          respAllScaleMax P γ jStar F t a ^ bigQ d γ := pow_le_pow_right₀ h1.le hQ
      have hQnn : (0 : ℝ) ≤ respAllScaleMax P γ jStar F t a ^ bigQ d γ := pow_nonneg h0 _
      linarith
  have hMmemLp : MemLp (respAllScaleMax P γ jStar F t) 2 P :=
    (memLp_two_iff_integrable_sq hMmeas).2 hM2int
  have hJmemLp : MemLp J 2 P := (memLp_two_iff_integrable_sq hJmeas).2 hJsq
  have hJint : Integrable J P := hJmemLp.integrable (by norm_num)
  have : ENNReal.HolderTriple 2 2 1 := by
    simpa only [ENNReal.ofReal_ofNat] using Real.HolderConjugate.two_two.ennrealOfReal
  have hMJint : Integrable (respAllScaleMax P γ jStar F t * J) P :=
    hMmemLp.integrable_mul hJmemLp
  have hsum : Integrable (J + respAllScaleMax P γ jStar F t * J) P := hJint.add hMJint
  exact hsum.congr (Filter.Eventually.of_forall fun a => by
    simp only [Pi.add_apply, Pi.mul_apply]
    ring)

/-- **Integrability of the all-scale envelope times the recentred response.**  For a probability
law `P`, the all-scale maximum `ℳ` of `p.response.transfer` with `Q`-th moment
integrable, `2 ≤ Q`, multiplies the pathwise recentred response `J(U_t; a_-, p, q')` of
AK.HC (2.15) into a `P`-integrable function: `(1 + ℳ) J` is integrable whenever `ℳ` is
measurable and `J ^ 2` is integrable and measurable. -/
theorem integrable_one_add_respAllScaleMax_mul_respJ {d : ℕ} [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (p q' : Vec d)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hQ : 2 ≤ bigQ d γ)
    (hJsq : Integrable (fun a => respJ (respGrid jStar F) t p q' (respCoeffMinus F a) ^ 2) P)
    (hJmeas : AEStronglyMeasurable
      (fun a => respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P) :
    Integrable (fun a =>
      (1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) P := by
  have _ := hd
  have _ := hγ
  exact integrable_one_add_respAllScaleMax_mul_of γ P jStar F t hMmeas hMint hQ
    (fun a => respJ (respGrid jStar F) t p q' (respCoeffMinus F a)) hJsq hJmeas

/-- **Integrability of the all-scale envelope times the adjoint recentred response.**  The
adjoint twin of `integrable_one_add_respAllScaleMax_mul_respJ`: the same probability-law
argument applies with the pathwise adjoint recentred response `J(U_t; a_+, p, q')` of
AK.HC (2.15) in place of `J(U_t; a_-, p, q')`, so `(1 + ℳ) J` is `P`-integrable under the
same envelope-moment, measurability and square-integrability hypotheses. -/
theorem integrable_one_add_respAllScaleMax_mul_respJPlus {d : ℕ} [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (p q' : Vec d)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (hQ : 2 ≤ bigQ d γ)
    (hJsq : Integrable (fun a => respJ (respGrid jStar F) t p q' (respCoeffPlus F a) ^ 2) P)
    (hJmeas : AEStronglyMeasurable
      (fun a => respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P) :
    Integrable (fun a =>
      (1 + respAllScaleMax P γ jStar F t a) *
        respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) P := by
  have _ := hd
  have _ := hγ
  exact integrable_one_add_respAllScaleMax_mul_of γ P jStar F t hMmeas hMint hQ
    (fun a => respJ (respGrid jStar F) t p q' (respCoeffPlus F a)) hJsq hJmeas

end

end Homogenization.HighContrast.Multiscale
