import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakHeadTail
import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedDefs

/-!
# The scale-average seminorm: head window plus per-scale tail

The scale-average seminorm
`besovSeminorm t avg = ∑' n, 3 ^ ((t - n) / 2) * √(card⁻¹ ∑_w |avg n w|²)`
splits at the window edge `H`: the first `H + 1` terms are the head, the older-scale terms are the
tail.  The split landed here keeps every tail term intact, in the per-scale shape the energy bound
reads, rather than collapsing the tail through Jensen.  Both statements are series identities
about the seminorm itself; nothing here mentions a cell, a coefficient field, or a maximizer.

`besovTerm` is defined in a module above this one and is deliberately not imported, so the `n`-th
term is spelled out here.  The tail index follows `h6a_tsum_split_range`, namely `j + (H + 1)`.
-/

namespace Homogenization.HighContrast.Multiscale

noncomputable section

variable {d : ℕ}

/-- Normalizing by the factor `3 ^ (-(t/2))` moves the weight of the `n`-th scale-average term
from the paper's `3 ^ ((t - n)/2)` to `3 ^ (-(n/2))`. -/
theorem h6a_normalized_besovTerm (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d) (n : ℕ) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        ((3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
          Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
            ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
      = (3 : ℝ) ^ (-((n : ℝ) / 2)) *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) := by
  rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hexp : -((t : ℝ) / 2) + (((t : ℝ) - (n : ℝ)) / 2) = -((n : ℝ) / 2) := by ring
  rw [hexp]

/-- The normalized scale-average seminorm is the finite head over `range (H + 1)` plus the
per-scale tail of every older term, each term kept as an individual weighted scale average. -/
theorem h6a_besovSeminorm_window_tail_eq (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
    (H : ℕ) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) * besovSeminorm t avg
      = (∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)))
        + ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
            Real.sqrt ((((triadicIndexBox d (j + (H + 1))).card : ℝ))⁻¹ *
              ∑ w ∈ triadicIndexBox d (j + (H + 1)),
                blockVecDot (avg (j + (H + 1)) w) (avg (j + (H + 1)) w)) := by
  classical
  have hbes : besovSeminorm t avg =
      ∑' n : ℕ, (3 : ℝ) ^ (((t : ℝ) - (n : ℝ)) / 2) *
        Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) := rfl
  rw [hbes, ← tsum_mul_left]
  rw [tsum_congr fun n => h6a_normalized_besovTerm t avg n]
  have hnorm : Summable fun n : ℕ => (3 : ℝ) ^ (-((n : ℝ) / 2)) *
      Real.sqrt ((((triadicIndexBox d n).card : ℝ))⁻¹ *
        ∑ w ∈ triadicIndexBox d n, blockVecDot (avg n w) (avg n w)) :=
    (hsum.mul_left _).congr fun n => h6a_normalized_besovTerm t avg n
  rw [h6a_tsum_split_range hnorm H]
  have htail : (∑' j : ℕ, (3 : ℝ) ^ (-((((j + (H + 1) : ℕ) : ℝ)) / 2)) *
        Real.sqrt ((((triadicIndexBox d (j + (H + 1))).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d (j + (H + 1)),
            blockVecDot (avg (j + (H + 1)) w) (avg (j + (H + 1)) w)))
      = ∑' j : ℕ, (3 : ℝ) ^ (-(((H : ℝ) + 1 + (j : ℝ)) / 2)) *
        Real.sqrt ((((triadicIndexBox d (j + (H + 1))).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d (j + (H + 1)),
            blockVecDot (avg (j + (H + 1)) w) (avg (j + (H + 1)) w)) :=
    tsum_congr fun j => by
      have hcast : (((j + (H + 1) : ℕ) : ℝ)) = (j : ℝ) + ((H : ℝ) + 1) := by
        push_cast; ring
      have hexp : -((((j + (H + 1) : ℕ) : ℝ)) / 2) = -(((H : ℝ) + 1 + (j : ℝ)) / 2) := by
        rw [hcast]; ring
      rw [hexp]
  rw [htail]

end

end Homogenization.HighContrast.Multiscale
