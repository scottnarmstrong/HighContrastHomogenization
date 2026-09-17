import Homogenization.CoarseGraining.Definitions
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import HCPoly.Entry.CG.Proofs.ResponseSubadditiveCountable

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

The proof applies `Homogenization.HighContrast.CG.responseJ_subadditive_countable_of_isEllipticFieldOn_provider` (`HCPoly/Entry/CG/Proofs/ResponseSubadditiveCountable.lean`).
-/

namespace Homogenization.HighContrast.CG

open MeasureTheory

/-- **Countable subadditivity of the scalar response.** For a countable disjoint family of open
subsets exhausting an open container up to a null set, the response on the container is at most
the volume-weighted series of the responses on the pieces. Ellipticity is assumed on the container
only; its constants do not appear in the conclusion. -/
theorem responseJ_subadditive_countable_of_isEllipticFieldOn {d : ℕ}
    {ι : Type*} {s : Set ι} (hs : s.Countable) {W : Set (Vec d)} {U : ι → Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn W)]
    (hWopen : IsOpen W) (hWvol : (volume W).toReal ≠ 0)
    (hopen : ∀ i ∈ s, IsOpen (U i)) (hsub : ∀ i ∈ s, U i ⊆ W)
    (hdisj : s.PairwiseDisjoint U) (hnull : volume (W \ ⋃ i ∈ s, U i) = 0)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam W a) (p q : Vec d) :
    ResponseJ W p q a ≤
      ∑' i : s, (volume (U i)).toReal / (volume W).toReal * ResponseJ (U i) p q a := by exact Homogenization.HighContrast.CG.responseJ_subadditive_countable_of_isEllipticFieldOn_provider hs hWopen hWvol hopen hsub hdisj hnull hEll p q

end Homogenization.HighContrast.CG
