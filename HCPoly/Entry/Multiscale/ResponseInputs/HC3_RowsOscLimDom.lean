import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The descendant limit by domination instead of a remainder bound

The descendant telescoping of the cutoff-mean row of `p.response.transfer` writes the annealed
functional, at every refinement depth, as its cell part plus the first `N` generation increments
plus a remainder.  The passage to the limit does NOT need an annealed bound on the remainder: it
needs only that the remainder tends to zero along every sample, together with an integrable
envelope for the whole series of increments.  Since the increments are flat averages of pairings
of a deterministic dual variable with cell averages of the optimizer state, such an envelope is
supplied by the scale-average seminorm of those cell averages, whereas a bound on the remainder
would need the annealed mean of a pointwise modulus.  This module records the limit in that form,
and concludes the integrability of the annealed functional as well as the bound.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Filter

open scoped Topology

noncomputable section

/-- **The descendant limit from a pathwise vanishing remainder and an integrable envelope.**  If a
sample functional `Phi` splits, at every refinement depth `N`, into a cell part `Tcell`, the first
`N` generation increments and a remainder `rem N`; if the remainder tends to zero along every
sample; if the increments are dominated by a nonnegative family `g` whose sample sum is
`P`-integrable; and if every partial sum of the annealed increments is at most `B`; then `Phi` is
`P`-integrable and its annealed mean differs from that of the cell part by at most `B`.

This replaces the annealed remainder bound of
`abs_integral_sub_integral_le_of_descendant_bound` by hypotheses that the carriers supply: the
pathwise vanishing of the remainder needs only ellipticity along each sample, and the envelope
needs only the cell averages of the state, never a pointwise modulus. -/
theorem integrable_and_abs_integral_sub_integral_le_of_dominated_descendant
    {α : Type*} [MeasurableSpace α] (P : Measure α)
    (Phi Tcell : α → ℝ) (inc rem : ℕ → α → ℝ) (g : ℕ → α → ℝ) (B : ℝ)
    (hdec : ∀ (N : ℕ) (a : α),
      Phi a = Tcell a + (∑ n ∈ Finset.range N, inc n a) + rem N a)
    (hg0 : ∀ (n : ℕ) (a : α), 0 ≤ g n a)
    (hdom : ∀ (n : ℕ) (a : α), |inc n a| ≤ g n a)
    (hgsum : ∀ᵐ a ∂P, Summable (fun n : ℕ => g n a))
    (hgsumI : Integrable (fun a => ∑' n : ℕ, g n a) P)
    (hrem0 : ∀ a : α, Tendsto (fun N : ℕ => rem N a) atTop (𝓝 0))
    (hB : ∀ N : ℕ, |∑ n ∈ Finset.range N, ∫ a, inc n a ∂P| ≤ B)
    (hT : Integrable Tcell P)
    (hPhiM : AEStronglyMeasurable Phi P)
    (hinc : ∀ n : ℕ, Integrable (inc n) P) :
    Integrable Phi P
      ∧ |(∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P| ≤ B := by
  -- The partial sums are the functional minus the remainder.
  have hSeq : ∀ (N : ℕ) (a : α),
      Tcell a + ∑ n ∈ Finset.range N, inc n a = Phi a - rem N a := by
    intro N a
    rw [hdec N a]
    ring
  -- Hence they converge to the functional along every sample.
  have hlim : ∀ a : α,
      Tendsto (fun N : ℕ => Tcell a + ∑ n ∈ Finset.range N, inc n a) atTop (𝓝 (Phi a)) := by
    intro a
    have h : Tendsto (fun N : ℕ => Phi a - rem N a) atTop (𝓝 (Phi a - 0)) :=
      tendsto_const_nhds.sub (hrem0 a)
    rw [sub_zero] at h
    exact h.congr fun N => (hSeq N a).symm
  -- The envelope dominates every partial sum, along almost every sample.
  have hbd : ∀ᵐ a ∂P, ∀ N : ℕ,
      |Tcell a + ∑ n ∈ Finset.range N, inc n a| ≤ |Tcell a| + ∑' n : ℕ, g n a := by
    filter_upwards [hgsum] with a hsa
    intro N
    have h1 : |∑ n ∈ Finset.range N, inc n a| ≤ ∑ n ∈ Finset.range N, |inc n a| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : (∑ n ∈ Finset.range N, |inc n a|) ≤ ∑ n ∈ Finset.range N, g n a :=
      Finset.sum_le_sum fun n _ => hdom n a
    have h3 : (∑ n ∈ Finset.range N, g n a) ≤ ∑' n : ℕ, g n a :=
      hsa.sum_le_tsum (Finset.range N) fun n _ => hg0 n a
    have h0 : |Tcell a + ∑ n ∈ Finset.range N, inc n a|
        ≤ |Tcell a| + |∑ n ∈ Finset.range N, inc n a| := abs_add_le _ _
    linarith only [h0, h1, h2, h3]
  have hGint : Integrable (fun a => |Tcell a| + ∑' n : ℕ, g n a) P := hT.abs.add hgsumI
  -- The envelope dominates the functional itself, so the functional is integrable.
  have hPhibd : ∀ᵐ a ∂P, |Phi a| ≤ |Tcell a| + ∑' n : ℕ, g n a := by
    filter_upwards [hbd] with a ha
    exact le_of_tendsto (hlim a).abs (Eventually.of_forall fun N => ha N)
  have hPhiI : Integrable Phi P :=
    hGint.mono' hPhiM (hPhibd.mono fun a ha => by
      rw [Real.norm_eq_abs]; exact ha)
  refine ⟨hPhiI, ?_⟩
  -- Dominated convergence transfers the limit to the annealed means.
  have hSint : ∀ N : ℕ,
      Integrable (fun a => Tcell a + ∑ n ∈ Finset.range N, inc n a) P := fun N =>
    hT.add (integrable_finsetSum _ fun n _ => hinc n)
  have hconv : Tendsto (fun N : ℕ => ∫ a, (Tcell a + ∑ n ∈ Finset.range N, inc n a) ∂P)
      atTop (𝓝 (∫ a, Phi a ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun a => |Tcell a| + ∑' n : ℕ, g n a)
      (fun N => (hSint N).aestronglyMeasurable) hGint
      (fun N => hbd.mono fun a ha => by rw [Real.norm_eq_abs]; exact ha N)
      (Eventually.of_forall hlim)
  have hSval : ∀ N : ℕ, (∫ a, (Tcell a + ∑ n ∈ Finset.range N, inc n a) ∂P)
      = (∫ a, Tcell a ∂P) + ∑ n ∈ Finset.range N, ∫ a, inc n a ∂P := by
    intro N
    rw [integral_add hT (integrable_finsetSum _ fun n _ => hinc n),
      integral_finsetSum (Finset.range N) fun n _ => hinc n]
  have hconst : Tendsto (fun _ : ℕ => (∫ a, Tcell a ∂P)) atTop (𝓝 (∫ a, Tcell a ∂P)) :=
    tendsto_const_nhds
  have hconv2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, ∫ a, inc n a ∂P)
      atTop (𝓝 ((∫ a, Phi a ∂P) - ∫ a, Tcell a ∂P)) :=
    ((hconv.congr hSval).sub hconst).congr fun N => by ring
  exact le_of_tendsto hconv2.abs (Eventually.of_forall hB)

/-- **A geometrically small pathwise remainder vanishes.**  If the modulus of `rem N a` is at most
`C a · 3^{-N}` for a finite sample constant `C a`, then `rem N a → 0` along every sample.  This is
the `hrem0` hypothesis of
`integrable_and_abs_integral_sub_integral_le_of_dominated_descendant`, and it is all that the
descendant remainder of the cutoff-mean row has to supply: the sample constant is the cell average
of the modulus of the crossed pairing, which is finite along every sample by pathwise ellipticity
but has no annealed bound. -/
theorem tendsto_zero_of_abs_le_geometric {α : Type*} (rem : ℕ → α → ℝ) (C : α → ℝ)
    (hbd : ∀ (N : ℕ) (a : α), |rem N a| ≤ C a * (3 : ℝ) ^ (-(N : ℝ))) (a : α) :
    Tendsto (fun N : ℕ => rem N a) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => ((3 : ℝ)⁻¹) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have hmul : Tendsto (fun N : ℕ => C a * ((3 : ℝ)⁻¹) ^ N) atTop (𝓝 0) := by
    have h := hpow.const_mul (C a)
    rwa [mul_zero] at h
  have hfun : (fun N : ℕ => C a * (3 : ℝ) ^ (-(N : ℝ)))
      = fun N : ℕ => C a * ((3 : ℝ)⁻¹) ^ N := by
    funext N
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  have hbound : Tendsto (fun N : ℕ => C a * (3 : ℝ) ^ (-(N : ℝ))) atTop (𝓝 0) := by
    rw [hfun]; exact hmul
  refine squeeze_zero_norm ?_ hbound
  intro N
  rw [Real.norm_eq_abs]
  exact hbd N a

end

end Homogenization.HighContrast.Multiscale
