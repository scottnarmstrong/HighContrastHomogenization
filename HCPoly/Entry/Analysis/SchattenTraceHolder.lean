import HCPoly.Entry.Analysis.SchattenSpectral
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The even trace bridge, the `ℓ^p ⊆ ℓ^1` embedding and finite Hölder

Three elementary ingredients of the printed proof of
`l.fixed.geometry.matrix.averaging`, all deterministic:

* `trace_even_pow_eq_absSchattenNorm_pow` — for even `N ≥ 2` and a symmetric block `H`,
  `tr ((toFullBlockMat H) ^ N) = |H|_{S_N} ^ N`, and that number is nonnegative.  This is the
  print's "since `N` is even, `tr(Y^N) = |Y|_{S_N}^N` for every symmetric matrix `Y`".  It is
  the existing `HCPoly.Entry.Analysis.SchattenSpectral.absSchattenNorm_even_pow_eq_trace` with the real
  index `2 * (k : ℝ)` reconciled with the natural index `N`; the identity is already
  proved there and no eigenvalue sum is restated here.

* `sum_rpow_le_rpow_sum` — the `ℓ^p ⊆ ℓ^1` embedding `∑ i, s i ^ p ≤ (∑ i, s i) ^ p` for
  `1 ≤ p` and nonnegative `s`.  This is the step that turns a block-size exponent `|B| / N`
  into the printed `2 / N` and `|B| / 2`, and it is exactly where "no singleton blocks"
  (`2 ≤ |B|`, hence `1 ≤ |B| / 2`) is consumed.

* `sum_prod_le_prod_sum_rpow` — generalized finite Hölder for `N` nonnegative families with
  all exponents equal to `N`, proved by normalising each family to unit `ℓ^N` mass and
  applying weighted AM-GM (`Real.geom_mean_le_arith_mean_weighted`) with equal weights `1/N`.

**What this file does not contain, and why.**  Trace Hölder
`|tr (A_1 ⋯ A_N)| ≤ ∏ k, |A_k|_{S_N}` for arbitrary noncommuting symmetric factors, is **not**
proved here and is **not** stated here as a `def`, an axiom or a `sorry`.  It is absent and is
neither used nor assumed by any declaration in this file.  The obstruction is genuine: even a
constant-factor variant of the inequality does not hold.  Nothing below depends on it.
-/

namespace Homogenization.HighContrast.Analysis

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The even trace identity -/

/-- **The even trace bridge.**  For an even natural `N ≥ 2` and a symmetric block `H`,
`tr ((toFullBlockMat H) ^ N) = |H|_{S_N} ^ N`.  The print's sentence "since `N` is even,
`tr(Y^N) = |Y|_{S_N}^N` for every symmetric matrix `Y`" (`l.fixed.geometry.matrix.averaging`).

Derived from `absSchattenNorm_even_pow_eq_trace`, which carries the real index `2 * (k : ℝ)`
and the natural power `2 * k`; `N = 2 * k` with `1 ≤ k` comes from `hNeven` and `hN`. -/
theorem trace_even_pow_eq_absSchattenNorm_pow {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℕ} (hN : 2 ≤ N) (hNeven : Even N) :
    Matrix.trace ((toFullBlockMat H) ^ N) = absSchattenNorm (N : ℝ) H ^ N := by
  obtain ⟨k, hk⟩ := hNeven
  have hNk : N = 2 * k := by omega
  have hk1 : 1 ≤ k := by omega
  have hcast : (N : ℝ) = 2 * (k : ℝ) := by rw [hNk]; push_cast; ring
  subst hNk
  rw [hcast]
  exact (absSchattenNorm_even_pow_eq_trace hH k hk1).symm

/-! ## The `ℓ^p ⊆ ℓ^1` embedding -/

/-- **`ℓ^p ⊆ ℓ^1`.**  For `1 ≤ p` and nonnegative `s`, `∑ i ∈ t, s i ^ p ≤ (∑ i ∈ t, s i) ^ p`
(real `rpow`).  Applied with `p = |B| / 2` and `2 ≤ |B|` this is the printed passage from a
block of size `|B|` to the exponent `|B| / 2` on the single sum `∑ i, (tr E[Y_i^N])^{2/N}`. -/
theorem sum_rpow_le_rpow_sum {ι : Type*} (t : Finset ι) (s : ι → ℝ)
    (hs : ∀ i ∈ t, 0 ≤ s i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ t, s i ^ p ≤ (∑ i ∈ t, s i) ^ p := by
  classical
  induction t using Finset.cons_induction with
  | empty => simp [Real.zero_rpow (by linarith : p ≠ 0)]
  | cons a t ha ih =>
      have hsa : 0 ≤ s a := hs a (Finset.mem_cons_self a t)
      have hst : ∀ i ∈ t, 0 ≤ s i := fun i hi => hs i (Finset.mem_cons_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ t, s i := Finset.sum_nonneg hst
      rw [Finset.sum_cons, Finset.sum_cons]
      calc s a ^ p + ∑ i ∈ t, s i ^ p
          ≤ s a ^ p + (∑ i ∈ t, s i) ^ p := by linarith [ih hst]
        _ ≤ (s a + ∑ i ∈ t, s i) ^ p := Real.add_rpow_le_rpow_add hsa hsum hp

/-! ## Generalized finite Hölder for `N` families -/

/-- **Generalized finite Hölder**, all `N` exponents equal to `N`.  For nonnegative families
`f 0, …, f (N-1)` on a finset `t`,
`∑ i ∈ t, ∏ k, f k i ≤ ∏ k, (∑ i ∈ t, f k i ^ N) ^ (1/N)`.

Route: if some family has zero `ℓ^N` mass it vanishes on `t` and both sides are `0`; otherwise
normalise each family to unit mass and apply weighted AM-GM with equal weights `1/N`. -/
theorem sum_prod_le_prod_sum_rpow {ι : Type*} {N : ℕ} (hN : 0 < N) (t : Finset ι)
    (f : Fin N → ι → ℝ) (hf : ∀ k, ∀ i ∈ t, 0 ≤ f k i) :
    ∑ i ∈ t, ∏ k : Fin N, f k i
      ≤ ∏ k : Fin N, (∑ i ∈ t, f k i ^ (N : ℝ)) ^ ((N : ℝ)⁻¹) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the `ℓ^N` masses
  set S : Fin N → ℝ := fun k => (∑ i ∈ t, f k i ^ (N : ℝ)) ^ ((N : ℝ)⁻¹) with hS
  have hSnn : ∀ k, 0 ≤ S k := fun k =>
    Real.rpow_nonneg (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf k i hi) _) _
  by_cases hzero : ∃ k, S k = 0
  · -- a vanishing family kills both sides
    obtain ⟨k₀, hk₀⟩ := hzero
    have hsum0 : ∑ i ∈ t, f k₀ i ^ (N : ℝ) = 0 := by
      by_contra hne
      have hpos : 0 < ∑ i ∈ t, f k₀ i ^ (N : ℝ) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf k₀ i hi) _)
          (Ne.symm hne)
      exact absurd hk₀ (ne_of_gt (Real.rpow_pos_of_pos hpos _))
    have hfi : ∀ i ∈ t, f k₀ i = 0 := by
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => Real.rpow_nonneg (hf k₀ j hj) ((N : ℝ)))).1 hsum0 i hi
      by_contra hne
      exact hne (by
        have hpos : 0 < f k₀ i := lt_of_le_of_ne (hf k₀ i hi) (Ne.symm hne)
        exact absurd this (ne_of_gt (Real.rpow_pos_of_pos hpos _)))
    have hlhs : ∑ i ∈ t, ∏ k : Fin N, f k i = 0 :=
      Finset.sum_eq_zero fun i hi =>
        Finset.prod_eq_zero (Finset.mem_univ k₀) (hfi i hi)
    have hrhs : (0 : ℝ) ≤ ∏ k : Fin N, S k := Finset.prod_nonneg fun k _ => hSnn k
    rw [hlhs]
    exact hrhs
  · push Not at hzero
    have hSpos : ∀ k, 0 < S k := fun k => lt_of_le_of_ne (hSnn k) (Ne.symm (hzero k))
    -- normalised families
    set g : Fin N → ι → ℝ := fun k i => f k i / S k with hg
    have hgnn : ∀ k, ∀ i ∈ t, 0 ≤ g k i := fun k i hi =>
      div_nonneg (hf k i hi) (hSnn k)
    have hmass : ∀ k, ∑ i ∈ t, g k i ^ (N : ℝ) = 1 := by
      intro k
      have hbase : (0 : ℝ) ≤ ∑ i ∈ t, f k i ^ (N : ℝ) :=
        Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf k i hi) _
      have hSk : S k ^ (N : ℝ) = ∑ i ∈ t, f k i ^ (N : ℝ) := by
        show ((∑ i ∈ t, f k i ^ (N : ℝ)) ^ ((N : ℝ)⁻¹)) ^ (N : ℝ) = _
        rw [← Real.rpow_mul hbase, inv_mul_cancel₀ (ne_of_gt hNR), Real.rpow_one]
      have : ∑ i ∈ t, g k i ^ (N : ℝ) = (∑ i ∈ t, f k i ^ (N : ℝ)) / S k ^ (N : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hg, Real.div_rpow (hf k i hi) (hSnn k)]
      rw [this, hSk, div_self]
      exact ne_of_gt (by
        have := hSpos k
        have hSkpow : 0 < S k ^ (N : ℝ) := Real.rpow_pos_of_pos this _
        rw [hSk] at hSkpow
        exact hSkpow)
    -- pointwise AM-GM with equal weights
    have hpt : ∀ i ∈ t, ∏ k : Fin N, g k i ≤ ∑ k : Fin N, ((N : ℝ)⁻¹) * g k i ^ (N : ℝ) := by
      intro i hi
      have hw : ∀ k : Fin N, k ∈ (Finset.univ : Finset (Fin N)) → (0 : ℝ) ≤ (N : ℝ)⁻¹ :=
        fun k _ => le_of_lt (inv_pos.2 hNR)
      have hw' : ∑ _k : Fin N, ((N : ℝ)⁻¹) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_inv_cancel₀ (ne_of_gt hNR)
      have hz : ∀ k : Fin N, k ∈ (Finset.univ : Finset (Fin N)) →
          (0 : ℝ) ≤ g k i ^ (N : ℝ) := fun k _ => Real.rpow_nonneg (hgnn k i hi) _
      have := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin N))
        (fun _ => (N : ℝ)⁻¹) (fun k => g k i ^ (N : ℝ)) hw hw' hz
      refine le_trans (le_of_eq ?_) this
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Real.rpow_mul (hgnn k i hi), mul_inv_cancel₀ (ne_of_gt hNR), Real.rpow_one]
    -- sum and exchange
    have hnorm : ∑ i ∈ t, ∏ k : Fin N, g k i ≤ 1 := by
      calc ∑ i ∈ t, ∏ k : Fin N, g k i
          ≤ ∑ i ∈ t, ∑ k : Fin N, ((N : ℝ)⁻¹) * g k i ^ (N : ℝ) :=
            Finset.sum_le_sum hpt
        _ = ∑ k : Fin N, ((N : ℝ)⁻¹) * ∑ i ∈ t, g k i ^ (N : ℝ) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
        _ = 1 := by
            simp only [hmass, mul_one]
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            exact mul_inv_cancel₀ (ne_of_gt hNR)
    -- undo the normalisation
    have hfactor : ∀ i ∈ t, ∏ k : Fin N, f k i
        = (∏ k : Fin N, S k) * ∏ k : Fin N, g k i := by
      intro i _
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hne : S k ≠ 0 := ne_of_gt (hSpos k)
      show f k i = S k * (f k i / S k)
      field_simp
    have hprodS : (0 : ℝ) ≤ ∏ k : Fin N, S k := Finset.prod_nonneg fun k _ => hSnn k
    calc ∑ i ∈ t, ∏ k : Fin N, f k i
        = (∏ k : Fin N, S k) * ∑ i ∈ t, ∏ k : Fin N, g k i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl hfactor
      _ ≤ (∏ k : Fin N, S k) * 1 := by
          exact mul_le_mul_of_nonneg_left hnorm hprodS
      _ = ∏ k : Fin N, S k := mul_one _

end

end Homogenization.HighContrast.Analysis
