/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.WindowDefinedness
import HCPoly.Frozen.CoarseEllipticityDagger

/-!
# The blocks of the terminal range of a selector execution

The proof of `t.polynomial.entry` reads the annealed blocks
`E_k^q` of the selected grid at every generation `k` between the coupled
execution burn `j_†` and the terminal generation `t`, and needs three facts
about them: each is an expectation, each is positive definite, and the terminal
one is below every earlier one,

`E_t^q ≤ E_k^q,   j_† ≤ k ≤ t`,

which is the monotonicity of the annealed blocks along the adapted grid.

The printed derivation is the aligned-subdivision property of the coarse block:
since `q = 𝒬_{j_†}(m_0)` and `j_† ≥ j_S ≥ k_0(d)`,
the terminal cell splits into exactly `3^{d(t-k)}` equal-volume cells
`z + ⋄_k^q` with integer translation vectors, each contained in `⋄_t^q ⊆ P_exec`,
so the adapted-cell bound `e.source.adapted.bound` of
`e.source.multiplier` applies on each with zero burn discount and gives
`𝐀(z + ⋄_k^q) ≤ B_q Y_{P_exec} 𝐄` almost surely; taking expectations with the
uniform moment bound for the source multiplier bounds `E_k^q` by `2 B_q 𝐄`, and
the equal-volume subadditivity estimate `e.fixed.geometry.parent.child` together
with stationarity under the integral translations gives the order.

Both halves of that derivation are available for a bounded window: the
containment of the terminal tower in the window turns the window multiplier's
own cell bound into finiteness and positivity at each generation of the range,
and the subdivision argument then supplies the order.  The only step the entry
argument still has to make is the one below — reading the selected grid
`q = 𝒬_{j_†}(m_0)` as a rounded adapted grid at the alignment scale, which the
coupled window pair guarantees, so that the range hypothesis of the window
becomes the admissible-index hypothesis of those three conclusions.
-/

namespace Homogenization
namespace HighContrast
namespace Entry

open MeasureTheory

noncomputable section

/-- **The terminal range of a selector execution is well behaved.**  At every
generation between the alignment scale of the coupled window and the terminal
generation the annealed block of the selected grid is an expectation and is
positive definite, and the terminal block is below it. -/
theorem terminal_range_blocks (d : ℕ) (hd : 2 ≤ d) (g : ℝ)
    (_hg : g ∈ Set.Ico (0 : ℝ) 1) (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (_hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    ∀ (Cd : ℝ) (m0 q : Mat d) (jS tt MM : ℤ) (Y : CoeffSpace d → ℝ),
      m0.PosDef → q = roundedGrid jS m0 →
      IsCoupledWindow d (initExpQ d g : ℝ) K jS MM →
      IsWindowMultiplier P g E Ψ K Cd jS MM Y →
      (∀ k : ℤ, jS ≤ k → k ≤ tt → adaptedCell q k ⊆ centeredCube d MM) →
      ∀ k : ℤ, jS ≤ k → k ≤ tt →
        HasFiniteAdaptedMean P q k ∧ Book.Ch02.BlockPosDef (adaptedMean P q k) ∧
          BlockMatLoewnerLE (adaptedMean P q tt) (adaptedMean P q k) := by
  haveI : NeZero d := ⟨by omega⟩
  intro Cd m0 q jS tt MM Y hm0 hq hcw hY hcont k hk1 hk2
  subst hq
  have hgrid : IsRoundedGrid jS (roundedGrid jS m0) :=
    Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hcw hm0
  exact ⟨Transport.hasFiniteAdaptedMean_of_isWindowMultiplier hY hm0 hgrid hk1 (hcont k hk1 hk2),
    Transport.blockPosDef_adaptedMean_of_isWindowMultiplier hY hm0 hgrid hk1 (hcont k hk1 hk2),
    Transport.adaptedMean_le_of_isWindowMultiplier hstat hY hm0 hgrid hk1 hk2 (hcont k hk1 hk2)
      (hcont tt (hk1.trans hk2) le_rfl)⟩

end

end Entry
end HighContrast
end Homogenization
