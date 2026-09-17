import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# A nonnegative series with summable annealed means

The increment envelope of the descendant sum of `p.response.transfer` is built generation by
generation, and what the carriers control is the annealed mean of each generation: the layer load
bounds the head and the terminal energy bounds the cell energy, so the series of annealed means is
summable.  Monotone convergence turns that single fact into the two hypotheses the descendant
limit consumes: the series converges along almost every sample, and its sum is `P`-integrable.

Nothing here is specific to the response transfer; the statement is the Beppo Levi theorem for a
nonnegative family of integrable functions indexed by the generations.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **Beppo Levi for a nonnegative generation series.**  A nonnegative family of `P`-integrable
functions whose annealed means form a summable series converges along almost every sample, and its
sample sum is `P`-integrable.

This is the producer of the `henvsum` and `henvI` hypotheses of the descendant limit: the carriers
supply a summable bound on `∫ env n` alone. -/
theorem aeSummable_and_integrable_tsum_of_summable_integral
    {α : Type*} [MeasurableSpace α] (P : Measure α) (g : ℕ → α → ℝ)
    (hg0 : ∀ (n : ℕ) (a : α), 0 ≤ g n a) (hgint : ∀ n : ℕ, Integrable (g n) P)
    (hgS : Summable fun n : ℕ => ∫ a, g n a ∂P) :
    (∀ᵐ a ∂P, Summable fun n : ℕ => g n a) ∧ Integrable (fun a => ∑' n : ℕ, g n a) P := by
  classical
  -- The `ℝ≥0∞` version of the family, and its sample sum.
  set G : ℕ → α → ENNReal := fun n a => ENNReal.ofReal (g n a) with hGdef
  have hGmeas : ∀ n : ℕ, AEMeasurable (G n) P := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hgint n).aestronglyMeasurable.aemeasurable
  have hGlin : ∀ n : ℕ, ∫⁻ a, G n a ∂P = ENNReal.ofReal (∫ a, g n a ∂P) := by
    intro n
    exact (ofReal_integral_eq_lintegral_ofReal (hgint n)
      (Filter.Eventually.of_forall (hg0 n))).symm
  -- The total mass of the sample sum is the sum of the annealed means, which is finite.
  have hInt0 : ∀ n : ℕ, 0 ≤ ∫ a, g n a ∂P := fun n =>
    integral_nonneg (hg0 n)
  have htot : ∫⁻ a, (∑' n : ℕ, G n a) ∂P = ENNReal.ofReal (∑' n : ℕ, ∫ a, g n a ∂P) := by
    rw [lintegral_tsum hGmeas]
    rw [ENNReal.ofReal_tsum_of_nonneg hInt0 hgS]
    exact tsum_congr hGlin
  have htop : ∫⁻ a, (∑' n : ℕ, G n a) ∂P ≠ ⊤ := by
    rw [htot]
    exact ENNReal.ofReal_ne_top
  -- Hence the sample sum is finite almost everywhere.
  have hfin : ∀ᵐ a ∂P, (∑' n : ℕ, G n a) ≠ ⊤ := by
    have hmeas : AEMeasurable (fun a => ∑' n : ℕ, G n a) P :=
      AEMeasurable.tsum hGmeas
    exact (ae_lt_top' hmeas htop).mono fun a ha => ha.ne
  -- Finiteness of the `ℝ≥0∞` sum bounds every partial sum, hence gives summability.
  have hsummable : ∀ᵐ a ∂P, Summable fun n : ℕ => g n a := by
    filter_upwards [hfin] with a ha
    refine summable_of_sum_range_le (fun n => hg0 n a) (c := (∑' n : ℕ, G n a).toReal) ?_
    intro N
    have hle : ENNReal.ofReal (∑ n ∈ Finset.range N, g n a) ≤ ∑' n : ℕ, G n a := by
      have h1 : ENNReal.ofReal (∑ n ∈ Finset.range N, g n a)
          = ∑ n ∈ Finset.range N, G n a := by
        induction N with
        | zero => simp [hGdef]
        | succ M ih =>
            rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih,
              ← ENNReal.ofReal_add (Finset.sum_nonneg fun n _ => hg0 n a) (hg0 M a)]
      rw [h1]
      exact ENNReal.sum_le_tsum (Finset.range N)
    have h2 : (ENNReal.ofReal (∑ n ∈ Finset.range N, g n a)).toReal
        ≤ (∑' n : ℕ, G n a).toReal := ENNReal.toReal_mono ha hle
    rwa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun n _ => hg0 n a)] at h2
  refine ⟨hsummable, ?_⟩
  -- The sample sum agrees almost everywhere with the real part of the `ℝ≥0∞` sum, which is
  -- measurable and of finite integral.
  have hcong : (fun a => ∑' n : ℕ, g n a)
      =ᵐ[P] fun a => (∑' n : ℕ, G n a).toReal := by
    filter_upwards [hsummable] with a ha
    have := ENNReal.ofReal_tsum_of_nonneg (fun n => hg0 n a) ha
    rw [← this, ENNReal.toReal_ofReal (tsum_nonneg fun n => hg0 n a)]
  have hmeasG : AEMeasurable (fun a => ∑' n : ℕ, G n a) P :=
    AEMeasurable.tsum hGmeas
  refine Integrable.congr ?_ hcong.symm
  refine ⟨hmeasG.ennreal_toReal.aestronglyMeasurable, ?_⟩
  have : ∫⁻ a, ‖(∑' n : ℕ, G n a).toReal‖ₑ ∂P ≤ ∫⁻ a, (∑' n : ℕ, G n a) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hfin] with a ha
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha]
  exact lt_of_le_of_lt this (lt_top_iff_ne_top.2 htop)

end

end Homogenization.HighContrast.Multiscale
