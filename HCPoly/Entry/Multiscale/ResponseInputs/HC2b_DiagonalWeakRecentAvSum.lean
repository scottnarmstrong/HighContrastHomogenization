import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentCellSum
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedEnergy

/-!
# The `weakAverageSum` half of the diagonal weak-norm bound and the nondegeneracy discharge

## The nondegeneracy discharge

In the branch where `respEhatMinus P jStar F t` is singular, the diagonal weak-norm statement
(`HC2b_DiagonalWeakRecent.lean`) is equivalent to its left-hand side being exactly `0`.
That branch is never proved: every `diagonalWeak*` lemma excludes it, by the pair
of binders `(hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)`
(`DiagonalWeakNormPrimal.lean`), and the
only junk branch anywhere near this material — `canonFactor_exists`
(`Canonical.lean`) — carries the docstring
"the junk value on non-positive data is never used".  So the missing case is a DROPPED
HYPOTHESIS, not a missing proof.

The results below show that the dropped hypothesis is FREE at the consumers: the route's own
`RespCalibrated Cc P jStar F s t` (`AdaptedAlgebra.lean`) already contains
`C⁻¹ M_0 ≤ Ehat_t^±` in the Loewner order, and `RawOutput.symm`/`RawOutput.pos`
(`AdaptedDefs.lean`) already give `(explicitCanonicalMetric F).PosDef`, hence
`(toFullBlockMat (respM0 F)).PosDef` (`AdaptedEnergy.lean`).  Both binders are in scope at
`respWeakEnergyOf_minus_le` (`AdaptedWeakRoute.lean`) and at
`response_weak_estimate_of_route` (`AdaptedWeakRoute.lean`) already, so no statement text
changes.  The satisfiability statement is in `∃` form.

## The `weakAverageSum` half

For the second printed summand, the estimate
`diagonalWeak_recent_average_good_le` (`DiagonalWeakNormRecentBound.lean`) feeds into
`normalized_diagonalWeak_recent_head_le` (`DiagonalWeakNormRecentHead.lean`).  Its
per-scale analytic input — the energy map `metricBlockNormSq_recent_difference_le`
(`DiagonalWeakNormRecentEnergyMap.lean`) composed with the difference-energy bound
`diagonalWeak_recent_difference_energy_le` (`DiagonalWeakNormRecentQuadratic.lean`) — has
no counterpart in this tree yet and is left as the explicit hypothesis `hscale` of
`h6a_weakAverageSum_half_le`.
Everything between that input and `weakAverageSum` is proved here:
the good-branch coefficient arithmetic `√2 (1 + √M·R) ≤ 4R` (`h6a_avCoeff_le`, cf.
`DiagonalWeakNormRecentBound.lean`), the weight identity `W · R = 3^{-(1/2-ρ/2)n}`
(`h6a_recentWeight_mul`, cf. `DiagonalWeakNormRecentHead.lean`), and the window
summation into `weakAverageSum` (`h6a_weakAverageSum_window_le`, cf.
`DiagonalWeakNormRecentHead.lean`).

CARRIER MAP (the section docstring of `HC2b_DiagonalWeakRecent.lean` is authoritative):
the source estimates use `E ↦ respEhatMinus P jStar F t`, `m ↦ respM0 F`,
`q ↦ respGrid jStar F`, `s = 1/2`, `rho = respRho γ`, `delta = 1`, `k = t - n`.  The
source carriers are `ℝ≥0∞` with an
`if diagonalWeakMaximum … = ⊤ then ⊤ else …` guard; here everything is plain `ℝ`, so the guard
vanishes and the `hfinite : diagonalWeakMaximum … ≠ ⊤` binder has no counterpart at all —
`respAllScaleMax` is real-valued by construction (`AdaptedDefs.lean`).  The inner
size `blockSize D (blockIdentity d)` of the source carriers is this tree's
`‖toFullBlockMat D‖`
(`HC2b_DiagonalWeakRecentSupport.lean`), which is why
`blockSize_diagonalWeakAverageDefect_nonneg`
(`DiagonalWeakNormComparison.lean`) — one of the five leaf consumers of `hEpd` — is here
just `norm_nonneg` and needs nothing.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The dropped hypothesis and its discharge at the consumers. -/

/-! ## The `weakAverageSum` half, assembled.

The analytic input feeding this assembly is
`diagonalWeak_recent_average_bound`
(`DiagonalWeakNormRecentBound.lean`), whose own inputs are the
energy map `metricBlockNormSq_recent_difference_le`
(`…/DiagonalWeakNormRecentEnergyMap.lean`) and the difference-energy bound
`diagonalWeak_recent_difference_energy_le` (`…/DiagonalWeakNormRecentQuadratic.lean`).
Neither has a counterpart in this tree; both appear here as the hypothesis `hscale` of
`h6a_weakAverageSum_half_le`. -/

/-- `rho = respRho γ = (1+γ)/2` is positive on `γ ∈ Set.Ico 0 1`; this is
the side condition `hrho : 0 < rho` (`…/DiagonalWeakNormPrimal.lean`), discharged here
rather than assumed, exactly as the section docstring of `HC2b_DiagonalWeakRecent.lean` records. -/
theorem h6a_respRho_pos {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : 0 < respRho γ := by
  obtain ⟨hγ0, _⟩ := hγ
  rw [respRho]
  linarith

/-- The geometric weight `R = 3^{rho(t-k)/2}` at `k = t - n` is `3^{rho n / 2} ≥ 1`,
the condition `hR1` of `diagonalWeak_recent_average_good_le`
(`…/DiagonalWeakNormRecentBound.lean`). -/
theorem h6a_one_le_recentWeight {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    (1 : ℝ) ≤ (3 : ℝ) ^ (rho * (n : ℝ) / 2) := by
  have hexp : (0 : ℝ) ≤ rho * (n : ℝ) / 2 :=
    div_nonneg (mul_nonneg hrho (Nat.cast_nonneg n)) (by norm_num)
  simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp

/-- The good-branch coefficient: `√2 (1 + √M R) ≤ 4 R` whenever `M ≤ 1` and `1 ≤ R`.
This is the content of the good branch for the averaged term, the condition `hcoeff` of
`diagonalWeak_recent_average_good_le` (`…/DiagonalWeakNormRecentBound.lean`), at
`delta = 1` so that `hgood : M ≤ delta` and `hdelta1 : delta ≤ 1` collapse into `M ≤ 1`. -/
theorem h6a_avCoeff_le {M R : ℝ} (hM1 : M ≤ 1) (hR1 : (1 : ℝ) ≤ R) :
    Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 4 * R := by
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR1
  have hrootM : Real.sqrt M ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hM1
  have hmR : Real.sqrt M * R ≤ R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrootM hR0
  have hB0 : (0 : ℝ) ≤ 1 + Real.sqrt M * R :=
    add_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) hR0)
  have hB : 1 + Real.sqrt M * R ≤ 2 * R := by linarith only [hmR, hR1]
  have hroot2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  calc
    Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 2 * (1 + Real.sqrt M * R) :=
      mul_le_mul_of_nonneg_right hroot2 hB0
    _ ≤ 2 * (2 * R) := mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = 4 * R := by ring

/-- The weight identity: `W · R = 3^{-(s - rho/2) n}` at `s = 1/2`, which is the
`weakAverageSum` weight of `HC2b_DiagonalWeakRecentSupport.lean`, the condition `hpow` of
`normalized_diagonalWeak_recent_head_le` (`…/DiagonalWeakNormRecentHead.lean`). -/
theorem h6a_recentWeight_mul (rho : ℝ) (n : ℕ) :
    (3 : ℝ) ^ (-((n : ℝ) / 2)) * (3 : ℝ) ^ (rho * (n : ℝ) / 2) =
      (3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

omit [NeZero d] in
/-- The window summation: a per-scale bound against the printed `weakAverageSum` weight
sums over the window `n ≤ H` to exactly `K L · weakAverageSum`, the condition `hsum` of
`normalized_diagonalWeak_recent_head_le` (`…/DiagonalWeakNormRecentHead.lean`), whose
`diagonalWeakAverageSum_eq` unfolding is here the `def` itself. -/
theorem h6a_weakAverageSum_window_le (q : Mat d) (t : ℤ) (H : ℕ) (rho : ℝ) (E : BlockMat d)
    (b : CoeffField d) {K L : ℝ} (A : ℕ → ℝ)
    (hterm : ∀ n ∈ Finset.range (H + 1), A n ≤
      K * L * ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ)) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect q t n E b)‖)) :
    ∑ n ∈ Finset.range (H + 1), A n ≤ K * L * weakAverageSum q t H rho E b := by
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [weakAverageSum, Finset.mul_sum]

omit [NeZero d] in
/-- The `weakAverageSum` half: `diagonalWeak_recent_average_good_le`
(`…/DiagonalWeakNormRecentBound.lean`) composed with the averaged branch of
`normalized_diagonalWeak_recent_head_le` (`…/DiagonalWeakNormRecentHead.lean`), on these
carriers at `s = 1/2`, `rho = respRho γ`, `delta = 1`.

`hscale` is `diagonalWeak_recent_average_bound`
(`…/DiagonalWeakNormRecentBound.lean`) on these carriers; it is the only analytic input
and it has no counterpart here yet.  `hE` is the positive-definiteness condition on
`respEhatMinus P jStar F t`, discharged at the consumers.  Everything else — the good-branch
coefficient (`h6a_avCoeff_le`), the weight identity (`h6a_recentWeight_mul`), the window
summation (`h6a_weakAverageSum_window_le`) — is proved.

The `hfinite : diagonalWeakMaximum … ≠ ⊤` binder has no counterpart: `respAllScaleMax` is
real-valued (`AdaptedDefs.lean`), so the `⊤` guard vanishes with it. -/
theorem h6a_weakAverageSum_half_le (P : Measure (CoeffSpace d)) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d)
    {K L : ℝ} (hK0 : 0 ≤ K) (hL0 : 0 ≤ L) (A : ℕ → ℝ)
    (_hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (hscale : ∀ n : ℕ, A n ≤
      Real.sqrt 2 * K *
        (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
          (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) * L *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) :
    ∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n ≤
      4 * K * L *
        weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatMinus P jStar F t)
          (respCoeffMinus F a) := by
  have hrho0 : 0 ≤ respRho γ := (h6a_respRho_pos hγ).le
  refine h6a_weakAverageSum_window_le (K := 4 * K) (L := L) _ t H (respRho γ) _ _
    (fun n => (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n) ?_
  intro n _
  set M : ℝ := respAllScaleMax P γ jStar F t a with hM
  set R : ℝ := (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2) with hR
  set W : ℝ := (3 : ℝ) ^ (-((n : ℝ) / 2)) with hW
  set D : ℝ := Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
    (respEhatMinus P jStar F t) (respCoeffMinus F a))‖ with hD
  have hR1 : (1 : ℝ) ≤ R := h6a_one_le_recentWeight hrho0 n
  have hW0 : (0 : ℝ) ≤ W := Real.rpow_nonneg (by norm_num) _
  have hD0 : (0 : ℝ) ≤ D := Real.sqrt_nonneg _
  have hrest0 : (0 : ℝ) ≤ K * L * D := mul_nonneg (mul_nonneg hK0 hL0) hD0
  have hcoeff : Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 4 * R := h6a_avCoeff_le hgood hR1
  have hstep : A n ≤ (4 * R) * (K * L * D) := by
    refine (hscale n).trans ?_
    calc
      Real.sqrt 2 * K * (1 + Real.sqrt M * R) * L * D
          = (Real.sqrt 2 * (1 + Real.sqrt M * R)) * (K * L * D) := by ring
      _ ≤ (4 * R) * (K * L * D) := mul_le_mul_of_nonneg_right hcoeff hrest0
  calc
    W * A n ≤ W * ((4 * R) * (K * L * D)) := mul_le_mul_of_nonneg_left hstep hW0
    _ = 4 * K * L * ((W * R) * D) := by ring
    _ = 4 * K * L * ((3 : ℝ) ^ (-((1 / 2 : ℝ) - respRho γ / 2) * (n : ℝ)) * D) := by
        rw [hW, hR, h6a_recentWeight_mul]

/-! ## The all-scale-maximum bricks, stated carrier-free.

These are the three arithmetic steps that turn the all-scale maximum into the
per-cell response size `B = 1 + √M · 3^{rho n/2}` used by `hsize` of
`diagonalWeak_recent_average_bound`
(`DiagonalWeakNormRecentBound.lean`).  They are stated here on
bare reals, so they carry no `E`-nondegeneracy at all and are reusable for any carrier choice.
The step that is NOT carrier-free — `‖N‖ ≤ 1 + blockSpecBound (N - I)` for
positive semidefinite `N`, the estimate `blockSize_le_one_add_blockExcess`
(`…/DiagonalWeakNormMaximum.lean`) — is NOT here: it needs `blockSpecBound`
subadditivity, which exists in this tree only as the `private` `h67_blockSpecBound_le_add`
(`AdaptedWeakRoute.lean`), DOWNSTREAM of this file. -/

omit [NeZero d] in
/-- Removing the maximum's weight costs the reciprocal geometric factor, the estimate
`blockExcess_le_mul_rpow_of_weighted_le` (`…/DiagonalWeakNormMaximum.lean`), at
`k = t - n` so that `t - k` is `n`. -/
theorem h6a_le_mul_rpow_of_weighted_le {rho B x : ℝ} (n : ℕ)
    (hweighted : (3 : ℝ) ^ (-(rho * (n : ℝ))) * x ≤ B) :
    x ≤ B * (3 : ℝ) ^ (rho * (n : ℝ)) := by
  have hfac0 : (0 : ℝ) ≤ (3 : ℝ) ^ (rho * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hcancel : (3 : ℝ) ^ (rho * (n : ℝ)) * (3 : ℝ) ^ (-(rho * (n : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), add_neg_cancel, Real.rpow_zero]
  calc
    x = (3 : ℝ) ^ (rho * (n : ℝ)) * ((3 : ℝ) ^ (-(rho * (n : ℝ))) * x) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (3 : ℝ) ^ (rho * (n : ℝ)) * B := mul_le_mul_of_nonneg_left hweighted hfac0
    _ = B * (3 : ℝ) ^ (rho * (n : ℝ)) := mul_comm _ _

omit [NeZero d] in
/-- The square root inherits half the maximum's geometric weight, producing exactly the
`√M · 3^{rho n/2}` of `B`, the estimate
`sqrt_blockExcess_le_sqrt_mul_rpow_of_weighted_le` (`…/DiagonalWeakNormMaximum.lean`).
Composed with `h6a_le_mul_rpow_of_weighted_le` this is
`sqrt_blockSize_adaptedResponse_le_of_maximum_finite`
(`…/DiagonalWeakNormMaximum.lean`) up to the one non-carrier-free step named in the
section note above. -/
theorem h6a_sqrt_le_sqrt_mul_rpow_of_weighted_le {rho B x : ℝ} (n : ℕ) (hB : 0 ≤ B)
    (hweighted : (3 : ℝ) ^ (-(rho * (n : ℝ))) * x ≤ B) :
    Real.sqrt x ≤ Real.sqrt B * (3 : ℝ) ^ (rho * (n : ℝ) / 2) := by
  have hrootB0 : (0 : ℝ) ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hfac0 : (0 : ℝ) ≤ (3 : ℝ) ^ (rho * (n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hfacSq : ((3 : ℝ) ^ (rho * (n : ℝ) / 2)) ^ 2 = (3 : ℝ) ^ (rho * (n : ℝ)) := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg hrootB0 hfac0, ?_⟩
  calc
    x ≤ B * (3 : ℝ) ^ (rho * (n : ℝ)) := h6a_le_mul_rpow_of_weighted_le n hweighted
    _ = (Real.sqrt B * (3 : ℝ) ^ (rho * (n : ℝ) / 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hB, hfacSq]

end

end Homogenization.HighContrast.Multiscale
