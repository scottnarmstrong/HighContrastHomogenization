/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Quenched.FixedGridWindowAccount
import HCPoly.Provider.Quenched.SmallContrastAbsorptionChoice
import HCPoly.Provider.Quenched.SmallContrastAdjointMirrors
import HCPoly.Provider.Quenched.SmallContrastAlignedGeometry
import HCPoly.Provider.Quenched.SmallContrastAnnealedEnvelope
import HCPoly.Provider.Quenched.SmallContrastAverageDrops
import HCPoly.Provider.Quenched.SmallContrastCenteringCap
import HCPoly.Provider.Quenched.SmallContrastEntryCapsIsotropy
import HCPoly.Provider.Quenched.SmallContrastEntryEnvelope
import HCPoly.Provider.Quenched.SmallContrastEntryRateMean
import HCPoly.Provider.Quenched.SmallContrastEntrySupply
import HCPoly.Provider.Quenched.SmallContrastFusionStep
import HCPoly.Provider.Quenched.SmallContrastHatDecay
import HCPoly.Provider.Quenched.SmallContrastHvarFamily
import HCPoly.Provider.Quenched.SmallContrastMeanDropCarrier
import HCPoly.Provider.Quenched.SmallContrastOneStepHub
import HCPoly.Provider.Quenched.SmallContrastRealClauses
import HCPoly.Provider.Quenched.SmallContrastRowAtCenters
import HCPoly.Provider.Quenched.SmallContrastSingleCellVariance
import HCPoly.Provider.Quenched.SmallContrastSlotValue
import HCPoly.Provider.Quenched.SmallContrastTerminalComparability
import HCPoly.Provider.Quenched.SmallContrastVarianceLagged
import HCPoly.Provider.Quenched.SmallContrastWeakCap
import HCPoly.Provider.Quenched.SmallContrastWeakValue
import HCPoly.Provider.Response.DiagonalWeakNormAdjointAlgebra
import HCPoly.Provider.Response.PreYoungFixedGridCells
import HCPoly.Provider.Response.ProfileRowOscillationSum
import HCPoly.Provider.Response.ProfileRowSchur
import HCPoly.Provider.Response.ProfileRowSkewCarriers

/-!
# The dilation device: the burn-in clock

Change variables so that the burn-in is one step, then apply the recursion
inequality.

With `G m := F (s * m)` at `s` the recursion's start, the three groups transform:

* **the drop history** — the one place a factor could hide, and it does not:
  grouping `k ∈ ((j-1)s, js]` telescopes to `F (s(j-1)) - F (s j) = G (j-1) - G j`,
  and `s*m - k ≥ s*(m-j)` gives `r ^ (s*m-k) ≤ (r ^ s) ^ (m-j)`, so the dilated
  sum **dominates** the original, which is the drop-sum bound below;
* **the quadratic index** — `l' m := 3 * m / 4` works, because
  `s * (3 * m / 4) ≤ 3 * (s * m) / 4` and `F` is antitone
  and `l'` satisfies the iteration decay's free index hypothesis
  `m ≤ 2 * l' m + 1`;
* **the source** — exactly `delta * (r ^ s) ^ m`, no bookkeeping at all.

So the general iteration decay applies to `G` unchanged, at the dilated rate
`r ^ s`, with `delayFactor = 1` — and `hsmall` in the dilated variable is
law-free.

## The cost the sketch does not name, and where it goes

The lemma requires its rate at most `1/2`, so the dilated rate must be taken as
`min (alpha * s) (1/2)`.  When `alpha * s > 1/2` — which is the case, since
`s = Θ(N₁)` — the dilated conclusion is at rate `1/(640 A)` per dilated step,
i.e. `1/(640 A s)` per original generation: **law-dependent**.  The binder fixes
`alpha` before the law, so the decay rate cannot absorb it, and a single dilated
pass does not close the endpoint.

**It closes in two stages, and this is what "the burn-in rides in the starting
threshold" means.**  Stage 1 (dilated) is used only to reach smallness: it gives
`F (s * m) ≤ K · delta · 3 ^ (-m/(640 A))`, so at
`m₁ := ⌈640 A · log₃ (1/eps)⌉` the excess is below any prescribed `eps`, at the
scale `s * m₁` — law-dependent, but a *starting scale*, which is exactly the
`Cdelay` slot the binder sanctions and bounds.  Stage 2 restarts the
**undilated** account at base `N₀' := s * m₁`, where `hinit` is supplied by stage
1 rather than by the bootstrap floor — so the recursion tolerance may be taken
as small as
the law requires, `hsmall` holds, and the conclusion is at the **law-free** rate
`alpha / (320 A)`.

That is the resolution: the recursion tolerance's lower bound was the bootstrap
floor `5 * cStar`, pinned before the law; stage 1 replaces that floor by a
quantity chosen after the law, and the pinning disappears.
-/

namespace Homogenization.HighContrast.Quenched

noncomputable section

/-! ## 1. The telescoping of one dilated block -/

theorem telescope_Ioc {F : ℕ → ℝ} (a : ℕ) :
    ∀ b : ℕ, a ≤ b → ∑ k ∈ Finset.Ioc a b, (F (k - 1) - F k) = F a - F b := by
  intro b
  induction b with
  | zero =>
    intro h
    have ha : a = 0 := by omega
    subst ha
    simp
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge a (n + 1) with hlt | hge
    · have han : a ≤ n := by omega
      have hsplit := Finset.sum_Ioc_consecutive
        (fun k => F (k - 1) - F k) han (Nat.le_succ n)
      rw [← hsplit, ih han]
      have hsingle : Finset.Ioc n (n + 1) = {n + 1} := by
        ext x
        simp only [Finset.mem_Ioc, Finset.mem_singleton]
        omega
      rw [hsingle, Finset.sum_singleton, Nat.add_sub_cancel]
      ring
    · have ha : a = n + 1 := by omega
      subst ha
      simp

/-! ## 2. The drop history under dilation -/

/-! ## 3. The quadratic index under dilation -/

end

end Homogenization.HighContrast.Quenched
