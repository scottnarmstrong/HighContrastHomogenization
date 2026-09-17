import HCPoly.Entry.Annealed.ParentChildRecurrence
import HCPoly.Entry.MatrixAveraging

/-!
# Exact parent–child recurrence

The type repeats the statement of `HCPoly/Entry/Statements/ParentChildRecurrence.lean`.
We return the same source constant as the matrix-averaging statement,
and pass the standing threshold hypothesis directly to its averaging theorem.
Unused ∀ proof-binder names carry a leading underscore. Only those names differ from the literal statement header;
every binder type, kind, position and dependent occurrence is preserved.
The recurrence assembly derives both mean positive-definiteness proofs and
all finite-moment premises, using the two printed constants without slack.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Provider
open MeasureTheory

/-- The exact printed recurrence, near `p.fixed.geometry.parent.child.recurrence`. -/
theorem fixed_geometry_parent_child_recurrence
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
        (_hP : IsProbabilityMeasure P) (_hstat : IsStationaryLaw P) (_hunit : IsUnitRangeLaw P)
        (_hell : CoarseEllipticityDagger P γ E Ψ K S)
        (N : ℕ) (_hN : 2 ≤ N) (_hNeven : Even N)
        (jStar : ℕ) (_hj : 2 * d ≤ 3 ^ jStar)
        (_hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
        (m : Mat d) (_hm : m.PosDef)
        (j h : ℤ) (_hjgen : (jStar : ℤ) ≤ j) (_hh : 1 ≤ h),
        lqSchattenNorm P (N : ℝ)
            (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) (j + h)) ≤
          (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * (1 + (2 * (d : ℝ)) ^ ((N : ℝ))⁻¹) *
                (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
                Real.exp (logDetLoss P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
              lqSchattenNorm P (N : ℝ)
                (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) j) +
            2 * (1 + (d : ℝ) ^ (1 - ((N : ℝ))⁻¹)) *
                Real.exp
                  ((1 - ((N : ℝ))⁻¹) *
                    logDetLoss P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
                (Real.exp (logDetLoss P (Geometry.explicitRoundedGrid jStar m) j (j + h)) - 1) ^
                  ((N : ℝ))⁻¹ := by
  obtain ⟨Csrc, hCsrc, havg⟩ := fixed_geometry_matrix_averaging d hd γ hγ
  refine ⟨Csrc, hCsrc, ?_⟩
  intro P E Ψ K S hP hstat hunit hell N hN hNeven jStar hj hsrc m hm j h hjgen hh
  apply Annealed.parent_child_recurrence_of_averaging d hd P hP γ E Ψ K S hstat hell
    N hN jStar hj m hm j h hjgen hh
  dsimp only
  intro R hRsymm hRpos
  exact havg P E Ψ K S hP hstat hunit hell N hN hNeven jStar hj hsrc m hm j hjgen
    (Annealed.alignedChildren (Geometry.explicitRoundedGrid jStar m) j h.toNat)
    (Annealed.alignedChildren_nonempty _ _ _) (Annealed.alignedChildren_subset_lattice _ _ _)
    R hRsymm hRpos

end Homogenization.HighContrast.Provider
