import Homogenization.CoarseGraining.Definitions
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import HCPoly.Entry.CG.Proofs.ResponseSummable

/-!
# A statement in CoarseGraining's own vocabulary

Stated in CoarseGraining's own vocabulary and namespace, with CG's hypotheses and no predicate
of this library, so that upstreaming is a file move.

**Why the Lean route differs from the paper's.** The paper argues through the coarse block of the
remaining set `W \ ⋃_{i≤N} U_i`, its pointwise-average bound, and local integrability. That route
needs the block on sets that are not open, which CoarseGraining does not define and nothing here
needs. The Lean
proof is direct: every `ResponseJ (U i) p q a` lies in `[0, λ⁻¹(Λ²|p|² + |q|²)]` with the
*container's* `λ, Λ` (CG's plain bound), the weights sum to at most one, so the series converges
absolutely; the inequality is then the variational argument pointwise in the test vector, exactly
CG's `intro X`. No Loewner limit is taken.

The proof applies `Homogenization.HighContrast.CG.summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn_provider` (`HCPoly/Entry/CG/Proofs/ResponseSummable.lean`).
-/

namespace Homogenization.HighContrast.CG

open MeasureTheory

/-- **Summability of the weighted responses.** Needs neither exhaustion nor openness of the
container: it is the uniform plain bound times weights summing to at most one. Summability is a
conclusion delivered here, never a hypothesis of the subadditivity theorem. -/
theorem summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn {d : ℕ}
    {ι : Type*} {s : Set ι} (hs : s.Countable) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a) (p q : Vec d) :
    Summable (fun i : s => (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a) := by exact Homogenization.HighContrast.CG.summable_volumeRatio_mul_responseJ_of_isEllipticFieldOn_provider hs hopen hsub hdisj hEll p q

end Homogenization.HighContrast.CG
