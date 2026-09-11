/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Geometry.ProjectiveDistance
import HCPoly.Geometry.ReferenceAspectRatio
import HCPoly.Setup.SourceObjects

/-!
# The retained prefix and the scales it reaches

The successful short test of `p.successful.short.bridge` reads a
retained finite prefix of projective hops and one further scale, and its proof
uses four bookkeeping facts about that data.

The alignment scale of a coupled window sits above the rounding scale, because
the source burn `e.source.lower.scale` is a maximum taken over it.  This is
what lets the rounded-hop bound be read at the alignment scale — including at
coincident witnesses, where the projective distance is zero.

The scale recursion `s_{i+1} ≥ s_i + ℓ₀` compounds, so the entry scale plus `k`
hop lengths is below `s_k`, and the projective jumps compound by the triangle
inequality, so the identity witness is within `k` jump lengths of the `k`-th
witness.

Finally the entry-scale clause is not vacuous: the reference aspect ratio is at
least one under `e.coarse.ellipticity` at a probability law, so its base-three
logarithm shifted by two is at least one, and a positive cutoff coefficient puts
the entry scale strictly above the alignment scale.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The alignment scale sits above the rounding scale -/

/-- **The alignment scale of a coupled window is at or above the rounding
scale.**  The source burn is a maximum taken over the rounding scale. -/
theorem kZero_le_of_isCoupledWindow {Q K : ℝ} {jStar M : ℤ}
    (hw : IsCoupledWindow d Q K jStar M) : (kZero d : ℤ) ≤ jStar :=
  le_trans (le_max_left _ _) hw.1

/-! ## The two compounding facts of the prefix -/

/-- **The scale recursion compounds.**  A prefix whose scales increase by at
least the hop length reaches `s_0 + kℓ₀` after `k` hops. -/
theorem scale_recursion {ss : ℕ → ℤ} {l0 : ℤ} {k : ℕ}
    (hstep : ∀ i : ℕ, i < k → ss i + l0 ≤ ss (i + 1)) :
    ss 0 + (k : ℤ) * l0 ≤ ss k := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hm := ih fun i hi => hstep i (Nat.lt_succ_of_lt hi)
    have hlast := hstep m (Nat.lt_succ_self m)
    have hcast : ((m + 1 : ℕ) : ℤ) * l0 = (m : ℤ) * l0 + l0 := by push_cast; ring
    rw [hcast]
    omega

/-- **The projective jumps compound.**  A prefix of hops of length at most
`c_hop` keeps the `i`-th witness within `i` hop lengths of the first. -/
theorem projDist_prefix [Nonempty (Fin d)] {mus : ℕ → Mat d} {chop : ℝ} {k : ℕ}
    (hpos : ∀ i : ℕ, i ≤ k → (mus i).PosDef)
    (hjump : ∀ i : ℕ, i < k → projDist (mus i) (mus (i + 1)) ≤ chop) :
    ∀ i : ℕ, i ≤ k → projDist (mus 0) (mus i) ≤ (i : ℝ) * chop := by
  intro i
  induction i with
  | zero =>
    intro h0
    rw [projDist_self (hpos 0 h0)]
    norm_num
  | succ m ih =>
    intro hm
    have hmk : m ≤ k := Nat.le_of_succ_le hm
    have htri := projDist_triangle (hpos 0 (Nat.zero_le k)) (hpos m hmk) (hpos (m + 1) hm)
    have hstep := hjump m (Nat.lt_of_succ_le hm)
    have hcast : ((m + 1 : ℕ) : ℝ) * chop = (m : ℝ) * chop + chop := by push_cast; ring
    rw [hcast]
    linarith only [htri, hstep, ih hmk]

/-! ## The entry-scale clause is not vacuous -/

/-- The base-three logarithm of two plus the reference aspect ratio is at least
one, because the aspect ratio is at least one. -/
theorem one_le_logb_two_add_aspectRatio {E : BlockMat d} (hE : 1 ≤ aspectRatio E) :
    1 ≤ Real.logb 3 (2 + aspectRatio E) := by
  have h3 : (3 : ℝ) ≤ 2 + aspectRatio E := by linarith only [hE]
  have hb : (1 : ℝ) < 3 := by norm_num
  have hmono := Real.logb_le_logb_of_le hb (by norm_num : (0 : ℝ) < 3) h3
  rwa [Real.logb_self_eq_one hb] at hmono

/-- **The entry scale is strictly above the alignment scale.**  The entry-scale
clause of the short test bounds `r_0 - j_*` below by the cutoff coefficient
times a logarithm that the aspect-ratio floor keeps at or above one. -/
theorem lt_entry_scale [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) {B : ℝ} (hB : 0 < B)
    {jStar r0 : ℤ}
    (hentry : B * Real.logb 3 (2 + aspectRatio E) ≤ (r0 : ℝ) - (jStar : ℝ)) :
    jStar < r0 := by
  have hlog := one_le_logb_two_add_aspectRatio
    (one_le_aspectRatio_of_coarseEllipticityDagger hdag)
  have hmul : B ≤ B * Real.logb 3 (2 + aspectRatio E) := by
    nlinarith only [hB, hlog]
  have hlt : (jStar : ℝ) < (r0 : ℝ) := by linarith only [hentry, hmul, hB]
  exact_mod_cast hlt

end

end ShortHop
end HighContrast
end Homogenization
