import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsFlatWeight
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsGeomCS
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsOscEnvSum

/-!
# The increment envelope of the descendant sum

The generation increments of the descendant sum of `p.response.transfer` are flat averages, over
the cells of one generation, of a cutoff weight of size `K 3^{-n}` against the crossed pairing of
the deterministic dual variable with the cell average of the optimizer state.  Cauchy--Schwarz over
the cells bounds such an increment by `K 3^{-n}` times the square root of the flat head energy
times the square root of the flat cell energy, and Young's inequality with the weight `3^{-n/2}`
splits that product into

```
(K/2) (3^{-3n/2} · flat head energy + 3^{-n/2} · flat cell energy) ,
```

which is the envelope below.  Its annealed mean is summable, because the head energy is summable
against `3^{-3n/2}` (that is the source load) and the cell energy is bounded by the terminal energy
at every depth; monotone convergence then makes the envelope series converge along almost every
sample with a `P`-integrable sum.  Nothing here uses a moment of the coefficient field.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The increment envelope of the descendant sum: Young's splitting, with the weight `3^{-n/2}`,
of `K 3^{-n}` times the Cauchy--Schwarz product of the flat head energy and the flat cell energy of
the generation-`n` cells. -/
def descendantEnvelope {iota alpha : Type*} (Z : ℕ → Finset iota)
    (G D : ℕ → iota → alpha → ℝ) (K : ℝ) (n : ℕ) (a : alpha) : ℝ :=
  (K / 2) *
    ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
        (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
      + (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) *
        (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a))

/-- The envelope is nonnegative. -/
theorem descendantEnvelope_nonneg {iota alpha : Type*} (Z : ℕ → Finset iota)
    (G D : ℕ → iota → alpha → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a) (n : ℕ) (a : alpha) :
    0 ≤ descendantEnvelope Z G D K n a := by
  have hF : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun W _ => sq_nonneg _)
  have hDd : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a :=
    mul_nonneg (by positivity)
      (Finset.sum_nonneg fun W hW => by
        have := hD n W hW a
        linarith only [this])
  have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) := by positivity
  have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) := by positivity
  have : (0 : ℝ) ≤ K / 2 := by linarith only [hK]
  exact mul_nonneg this (add_nonneg (mul_nonneg h1 hF) (mul_nonneg h2 hDd))

/-- **Young's splitting of the geometric Cauchy--Schwarz product.**  For nonnegative `X`, `Y` and
`K`, the product `K 3^{-n} √X √Y` is at most `(K/2)(3^{-3n/2} X + 3^{-n/2} Y)`. -/
theorem mul_rpow_neg_sqrt_mul_sqrt_le {K X Y : ℝ} (hK : 0 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (n : ℕ) :
    K * (3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y)
      ≤ (K / 2) * ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * X
          + (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) * Y) := by
  set u : ℝ := (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * X with hu
  set v : ℝ := (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) * Y with hv
  have hu0 : 0 ≤ u := mul_nonneg (by positivity) hX
  have hv0 : 0 ≤ v := mul_nonneg (by positivity) hY
  -- The arithmetic--geometric mean inequality.
  have hAM : 2 * (Real.sqrt u * Real.sqrt v) ≤ u + v := by
    have hexp : (Real.sqrt u - Real.sqrt v) ^ 2
        = u - 2 * (Real.sqrt u * Real.sqrt v) + v := by
      rw [sub_sq, Real.sq_sqrt hu0, Real.sq_sqrt hv0]; ring
    have := sq_nonneg (Real.sqrt u - Real.sqrt v)
    linarith only [this, hexp]
  -- The two geometric weights multiply to `3^{-n}`.
  have hw : Real.sqrt ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)))
      * Real.sqrt ((3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))) = (3 : ℝ) ^ (-(n : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hprod : Real.sqrt u * Real.sqrt v
      = (3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y) := by
    rw [hu, hv, Real.sqrt_mul (by positivity) X, Real.sqrt_mul (by positivity) Y]
    calc Real.sqrt ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))) * Real.sqrt X
            * (Real.sqrt ((3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))) * Real.sqrt Y)
        = (Real.sqrt ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)))
            * Real.sqrt ((3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))))
              * (Real.sqrt X * Real.sqrt Y) := by ring
      _ = (3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y) := by rw [hw]
  have hmain : 2 * ((3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y)) ≤ u + v := by
    rw [← hprod]; exact hAM
  have hfin := mul_le_mul_of_nonneg_left hmain (show (0 : ℝ) ≤ K / 2 by linarith only [hK])
  calc K * (3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y)
      = K / 2 * (2 * ((3 : ℝ) ^ (-(n : ℝ)) * (Real.sqrt X * Real.sqrt Y))) := by ring
    _ ≤ K / 2 * (u + v) := hfin

/-- **The envelope dominates the generation increment.**  With cutoff weights of size `K 3^{-n}`
and a crossed pairing bounded by the head times the square root of twice the cell energy, the flat
average defining the generation-`n` increment is at most the envelope. -/
theorem abs_flat_weighted_pairing_le_descendantEnvelope {iota alpha : Type*}
    (Z : ℕ → Finset iota) (θ : ℕ → iota → ℝ) (pairing G D : ℕ → iota → alpha → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hθ : ∀ n : ℕ, ∀ W ∈ Z n, |θ n W| ≤ K * (3 : ℝ) ^ (-(n : ℝ)))
    (hG : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ G n W a)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a)
    (hbd : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, |pairing n W a| ≤ G n W a * Real.sqrt (2 * D n W a))
    (n : ℕ) (a : alpha) :
    |((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a|
      ≤ descendantEnvelope Z G D K n a := by
  have hcard : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ := by positivity
  have hw0 : (0 : ℝ) ≤ K * (3 : ℝ) ^ (-(n : ℝ)) := by positivity
  -- Peel the weights off the flat average.
  have step1 : |((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a|
      ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
          (K * (3 : ℝ) ^ (-(n : ℝ))) * (G n W a * Real.sqrt (2 * D n W a)) := by
    rw [abs_mul, abs_of_nonneg hcard]
    refine mul_le_mul_of_nonneg_left ?_ hcard
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun W hW => ?_)
    rw [abs_mul]
    have h1 : |θ n W| * |pairing n W a|
        ≤ (K * (3 : ℝ) ^ (-(n : ℝ))) * |pairing n W a| :=
      mul_le_mul_of_nonneg_right (hθ n W hW) (abs_nonneg _)
    have h2 : (K * (3 : ℝ) ^ (-(n : ℝ))) * |pairing n W a|
        ≤ (K * (3 : ℝ) ^ (-(n : ℝ))) * (G n W a * Real.sqrt (2 * D n W a)) :=
      mul_le_mul_of_nonneg_left (hbd n W hW a) hw0
    linarith only [h1, h2]
  -- Cauchy--Schwarz over the cells of the generation.
  have step2 : ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
        (K * (3 : ℝ) ^ (-(n : ℝ))) * (G n W a * Real.sqrt (2 * D n W a))
      = K * (3 : ℝ) ^ (-(n : ℝ)) * (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
          Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [Real.sqrt_sq (hG n W hW a)]
    ring
  have hCS : ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
        Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a)
      ≤ Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
        * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) :=
    flat_average_sqrt_mul_sqrt_le (Z n) (fun W => (G n W a) ^ 2) (fun W => 2 * D n W a)
      (fun W _ => sq_nonneg _) (fun W hW => by have := hD n W hW a; linarith only [this])
  have hX : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 :=
    mul_nonneg hcard (Finset.sum_nonneg fun W _ => sq_nonneg _)
  have hY : (0 : ℝ) ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a :=
    mul_nonneg hcard (Finset.sum_nonneg fun W hW => by
      have := hD n W hW a; linarith only [this])
  calc |((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, θ n W * pairing n W a|
      ≤ ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
          (K * (3 : ℝ) ^ (-(n : ℝ))) * (G n W a * Real.sqrt (2 * D n W a)) := step1
    _ = K * (3 : ℝ) ^ (-(n : ℝ)) * (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n,
          Real.sqrt ((G n W a) ^ 2) * Real.sqrt (2 * D n W a)) := step2
    _ ≤ K * (3 : ℝ) ^ (-(n : ℝ)) *
          (Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2)
            * Real.sqrt (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a)) :=
        mul_le_mul_of_nonneg_left hCS hw0
    _ ≤ descendantEnvelope Z G D K n a := mul_rpow_neg_sqrt_mul_sqrt_le hK hX hY n

/-- **The envelope series converges along almost every sample, with an integrable sum.**  The
annealed mean of the generation-`n` envelope is at most `(K/2)(3^{-3n/2} L n + 3^{-n/2} 2 E[J])`,
where `L` is the layer head energy of the source load and `E[J]` bounds the cell energy at every
depth.  That series is summable, so monotone convergence gives both hypotheses the descendant
limit consumes. -/
theorem aeSummable_and_integrable_tsum_descendantEnvelope {iota alpha : Type*}
    [MeasurableSpace alpha] (P : Measure alpha) (Z : ℕ → Finset iota)
    (G D : ℕ → iota → alpha → ℝ) (L : ℕ → ℝ) (K EJ : ℝ) (hK : 0 ≤ K)
    (hD : ∀ n : ℕ, ∀ W ∈ Z n, ∀ a, 0 ≤ D n W a)
    (hGsq : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P) ≤ L n)
    (hDval : ∀ n : ℕ, (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P) ≤ 2 * EJ)
    (hFint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) P)
    (hDint : ∀ n : ℕ, Integrable (fun a => ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) P)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n) :
    (∀ᵐ a ∂P, Summable fun n : ℕ => descendantEnvelope Z G D K n a)
      ∧ Integrable (fun a => ∑' n : ℕ, descendantEnvelope Z G D K n a) P := by
  have henvint : ∀ n : ℕ, Integrable (fun a => descendantEnvelope Z G D K n a) P := by
    intro n
    exact (((hFint n).const_mul _).add ((hDint n).const_mul _)).const_mul _
  have hval : ∀ n : ℕ, (∫ a, descendantEnvelope Z G D K n a ∂P)
      = (K / 2) * ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
            * (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P)
          + (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))
            * (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P)) := by
    intro n
    have e1 : (∫ a, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
          * (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2) ∂P)
        = (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
          * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P :=
      integral_const_mul _ _
    have e2 : (∫ a, (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))
          * (((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a) ∂P)
        = (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))
          * ∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P :=
      integral_const_mul _ _
    simp only [descendantEnvelope]
    rw [integral_const_mul, integral_add ((hFint n).const_mul _) ((hDint n).const_mul _), e1, e2]
  -- The summable majorant of the annealed envelope means.
  have hmaj : Summable fun n : ℕ => (K / 2) * ((3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n
      + (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) * (2 * EJ)) := by
    refine Summable.mul_left _ (hsum.add ?_)
    refine Summable.mul_right _ ?_
    refine summable_rpow_neg_half.congr fun n => ?_
    rw [show -((n : ℝ) / 2) = -((1 : ℝ) / 2) * (n : ℝ) by ring]
  refine aeSummable_and_integrable_tsum_of_summable_integral P
    (fun n a => descendantEnvelope Z G D K n a)
    (fun n a => descendantEnvelope_nonneg Z G D K hK hD n a) henvint ?_
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · exact integral_nonneg fun a => descendantEnvelope_nonneg Z G D K hK hD n a
  · rw [hval n]
    have hc1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) := by positivity
    have hc2 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) := by positivity
    have h1 : (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ))
          * (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, (G n W a) ^ 2 ∂P)
        ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * L n :=
      mul_le_mul_of_nonneg_left (hGsq n) hc1
    have h2 : (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ))
          * (∫ a, ((Z n).card : ℝ)⁻¹ * ∑ W ∈ Z n, 2 * D n W a ∂P)
        ≤ (3 : ℝ) ^ (-((1 : ℝ) / 2) * (n : ℝ)) * (2 * EJ) :=
      mul_le_mul_of_nonneg_left (hDval n) hc2
    exact mul_le_mul_of_nonneg_left (by linarith only [h1, h2])
      (by linarith only [hK] : (0 : ℝ) ≤ K / 2)

end

end Homogenization.HighContrast.Multiscale
