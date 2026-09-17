import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakDecompBox
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentScaleInput

/-!
# Assembly of the diagonal weak norm estimate

This file assembles the estimate `diagonalWeakNorm_primal_le`
(`HC2b_DiagonalWeakRecent.lean`) from its two halves.  It adds declarations only and restates
or weakens none of them.

## What this file is for

The statement omitted the hypothesis pair `(hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)`
that the printed argument carries at the route's energy estimate.  Here the surviving gap is
exactly `(toFullBlockMat (respEhatMinus P jStar F t)).PosDef`, and that gap is dischargeable,
as established in `HC2b_DiagonalWeakRecentAvSum.lean`, from `RespCalibrated` together with
`RawOutput.symm` and `RawOutput.pos`.  This file chains those discharges into the context of
`diagonalWeakNorm_primal_le` rather than leaving them standing alone.

The results fall into three groups.

* The first concerns the maximum: the real-valued `respAllScaleMax` (`AdaptedDefs.lean`) is a
  bare `sSup`, which on an unbounded set takes Lean's junk value `0`; an explicit finiteness
  hypothesis `hfinite : diagonalWeakMaximum … ≠ ⊤` excludes that.  An envelope constant —
  precisely what `b130_pathwise_envelope` (`AdaptedWeakRoute.lean`) delivers almost
  everywhere — makes the defining set `BddAbove`, and the membership inequality that `hfinite`
  was there to license follows.
* The second concerns the mismatch between the two spectral quantities: the `weakCellSum` half
  concludes against `√‖toFullBlockMat (normalizedBlock Ê M₀)‖`, whereas the statement prints
  `√(blockSpecBound (normalizedBlock Ê M₀))`, and `blockSpecBound N ≤ ‖toFullBlockMat N‖` is the
  wrong direction.  Under the positive-definiteness condition the two are equal, because
  `normalizedBlock Ê M₀` is then positive definite, so the half can be restated on the printed
  quantity without touching the statement.
* The third composes the two halves into the printed first summand and reduces the remaining
  hypothesis to the two analytic facts on which it rests, recording what is still missing.

Every statement is proved here, on the carriers of this library.  The positive-definiteness of
the normalized block is supplied by `Annealed.normalizedBlock_posDef`
(`HCPoly/Entry/Annealed/Normalization.lean`), and the boundedness result rests on the finite-maximum
branch of the real-valued maximum.
-/

open Homogenization.HighContrast (CoeffSpace blockSub coarseBlock normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The positive-definiteness condition at the route's own binder bundle. -/

/-! ## The boundedness of the real-valued maximum. -/

omit [NeZero d] in
/-- The boundedness.  An envelope constant bounding every weighted spectral excess makes the
defining set of `respAllScaleMax` (`AdaptedDefs.lean`) bounded above.  The hypothesis holds
almost everywhere: it is the third component of `b130_pathwise_envelope`
(`AdaptedWeakRoute.lean`).  This is the content, on a real-valued carrier, of the
finiteness hypothesis `hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤` that an earlier statement
carried: without it `sSup` takes the junk value `0`. -/
theorem h6a_respAllScaleMax_bddAbove_of_envelope (P : Measure (CoeffSpace d)) (γ : ℝ)
    (jStar : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d) {C : ℝ}
    (hterms : ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
      (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockSpecBound (blockSub (normalizedBlock (coarseBlock
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a) (respMean P jStar F t))
          (Book.Ch02.blockIdentity d)) ≤ C) :
    BddAbove {y : ℝ | ∃ n : ℕ, ∃ z ∈ triadicIndexBox d n, y =
      (3 : ℝ) ^ (-(respRho γ * (n : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))} := by
  refine ⟨C, ?_⟩
  rintro y ⟨n, z, hz, rfl⟩
  exact hterms n z hz

/-! ## The `weakCellSum` half, on the quantity the printed statement uses. -/

omit [NeZero d] in
/-- The key equality.  On positive definite `N` and `M` the spectral positive part of
`normalizedBlock N M` is all of `normalizedBlock N M`, so the two quantities
`blockSpecBound (normalizedBlock Ê M₀)` and `‖toFullBlockMat (normalizedBlock Ê M₀)‖` coincide.
`Annealed.normalizedBlock_posDef` is `HCPoly/Entry/Annealed/Normalization.lean`; the hard half of the
equality is `h6a_blockSpecBound_eq_norm_of_posSemidef`
(`HC2b_DiagonalWeakRecentSupport2.lean`). -/
theorem h6a_blockSpecBound_normalizedBlock_eq_norm (N M : BlockMat d)
    (hN : (toFullBlockMat N).PosDef) (hM : (toFullBlockMat M).PosDef) :
    blockSpecBound (normalizedBlock N M) = ‖toFullBlockMat (normalizedBlock N M)‖ :=
  h6a_blockSpecBound_eq_norm_of_posSemidef _
    (Annealed.normalizedBlock_posDef N M hN hM).posSemidef

omit [NeZero d] in
/-- The metric factor.  The same equality at the carriers of `diagonalWeakNorm_primal_le`: the
`K₀` of `p.response.transfer` as it is printed equals the `K₀` used by the `weakCellSum` half. -/
theorem h6a_respK0_specBound_eq_norm (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d)
    (t : ℤ) (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef) :
    blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)) =
      ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ :=
  h6a_blockSpecBound_normalizedBlock_eq_norm _ _ hE hM0

/-- The `weakCellSum` half on the printed quantity.  `h6a_weakCellSum_half_le`
(`HC2b_DiagonalWeakRecentCellSum.lean`) with its conclusion moved from the two-sided
operator norm to the one-sided `blockSpecBound` used in `HC2b_DiagonalWeakRecent.lean`.  The
statement of `diagonalWeakNorm_primal_le` is untouched; the change is licensed exactly by the
positive-definiteness condition, which is discharged above.  Constant `1` against the printed
`16`. -/
theorem h6a_weakCellSum_half_specBound_le
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (H : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u))))
        ≤ Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqMinus P jStar F t e) *
            weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
              (respCoeffMinus F a) := by
  obtain ⟨V, hV⟩ := h6a_weakCellSum_half_le P jStar F t e hgrid a H u hu hE
  exact ⟨V, by rwa [h6a_respK0_specBound_eq_norm P jStar F t hE hM0]⟩

/-! ## Composition of the two halves into the first printed summand. -/

/-- The composition of the two halves, with the child-maximizer family produced before the
per-scale family.  The earlier composition statement binds the per-scale family `A` and its
constraint `hscale` before producing the child-maximizer family `V`.  The recent-scale
decomposition of the head term into the child term plus the average-defect family exhibits the
intended `A` — the average-defect family — and that family depends on `V`, so it cannot be
supplied to that statement at all: the `∃ V` is under the `∀ A`.

This declaration is that statement with `∃ V` moved outside `∀ A`.  It is strictly stronger than
the earlier statement (the same `V` now serves every `A`), nothing is weakened, and the proof is
the earlier statement's own, since it already obtains `V` from the `weakCellSum` half
independently of `A`. -/
theorem h6a_recentHead_halves_forall_le
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      ∀ A : ℕ → ℝ,
    (hscale : ∀ n : ℕ, A n ≤
      Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqMinus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))) + A n)
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqMinus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
                (respCoeffMinus F a) +
              weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by
  classical
  set K : ℝ :=
    Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) with hK
  set L : ℝ := Real.sqrt (respLsqMinus P jStar F t e) with hL
  have hK0 : (0 : ℝ) ≤ K := Real.sqrt_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Real.sqrt_nonneg _
  obtain ⟨V, hV⟩ := h6a_weakCellSum_half_specBound_le P jStar F t e hgrid a H u hu hE hM0
  refine ⟨V, fun A hscale => ?_⟩
  have hav := h6a_weakAverageSum_half_le (K := K) (L := L) P γ hγ jStar H F t a hK0 hL0 A hE
    hgood hscale
  have hcs0 : (0 : ℝ) ≤ weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
      (respCoeffMinus F a) := weakCellSum_nonneg _ _ _ _ _
  have has0 : (0 : ℝ) ≤ weakAverageSum (respGrid jStar F) t H (respRho γ)
      (respEhatMinus P jStar F t) (respCoeffMinus F a) := weakAverageSum_nonneg _ _ _ _ _ _
  have hsplit : ∀ n ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-((n : ℝ) / 2)) * (Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))) + A n)
        = (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                          (optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                        cellAverage (respCell jStar F t)
                          (optimizerField (respCoeffMinus F a) u))))
          + (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n := fun n _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  nlinarith [hV, hav, hcs0, has0, mul_nonneg hK0 hL0]

/-- The composition of the recent-scale decomposition with the preceding result: the head of the
left-hand side built from the actual parent optimizer `u` — the field supplied by
`h6a_besovSeminorm_recentred_eq` and `h6a_besovSeminorm_head_tail_le`
(`HC2b_DiagonalWeakRecentSupport2.lean`) — is bounded by the entire first printed
summand `16 K₀ L⁻ (weakCellSum + weakAverageSum)`.

The earlier composition statement bounded a sum over the child maximizers plus an abstract `A`;
here the child maximizers are gone from the left-hand side and `A` is no longer abstract — it is
the explicit average-defect family, produced by the recent-scale decomposition together with `V`.

The only thing still assumed is `hscale`, now asked of that explicit family rather than of an
abstract one.  This is precisely the analytic recent-average bound on the average-defect family,
which is not proved anywhere here.  The integrability side conditions are the same ones the
recent-scale support lemmas already carry. -/
theorem h6a_recentHead_actual_le
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n : ℕ, Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
                ∑ w ∈ triadicIndexBox d n,
                  blockVecDot
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (fun x => optimizerField (respCoeffMinus F a) u x -
                          optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
                    (blockMatVecMul (blockSqrt (respM0 F))
                      (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (fun x => optimizerField (respCoeffMinus F a) u x -
                          optimizerField (respCoeffMinus F a)
                            ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))) ≤
      Real.sqrt 2 *
          Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
            (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2)) *
          Real.sqrt (respLsqMinus P jStar F t e) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u))))
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqMinus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
                (respCoeffMinus F a) +
              weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by
  classical
  obtain ⟨V, hV⟩ := h6a_recentHead_halves_forall_le P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood
  refine ⟨V, fun h1v h2v hscale => ?_⟩
  refine le_trans ?_ (hV _ hscale)
  exact h6a_recentHead_scale_decomposition_box_le (respGrid jStar F) t H (blockSqrt (respM0 F))
    (optimizerField (respCoeffMinus F a) u)
    (fun n w => optimizerField (respCoeffMinus F a)
      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction))
    (cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))
    h1u h2u h1v h2v

/-- The composition of the preceding result with its remaining hypothesis replaced by the two
analytic facts it rests on.  Its single remaining hypothesis `hscale` is replaced by a per-depth
per-cell energy family `G` satisfying:

* `hcell`: the recent-difference metric-norm-squared bound, composed with the all-scale-maximum
  response bound; and
* `henergy`: the recent-difference energy bound.

The reduction is `h6a_scaleInput_of_analytic` (`HC2b_DiagonalWeakRecentScaleInput.lean`).
Neither analytic fact is proved here: their root `energy_map_metric_le`
(`…/Provider/Response/EnergyMap.lean`) rests on a doubled-response / `blockSharp` sublayer
absent from both `HCPoly/Entry/` and the `CoarseGraining` dependency.  What this result establishes is that
nothing else is missing between them and the entire first printed summand.

A side hypothesis `hLsq : 0 ≤ respLsqMinus …` is not needed: it is exactly the nonnegativity of
the quadratic form of the positive-definite `respEhatMinus` at `respxMinus`, supplied from `hE` by
`h6a_blockVecDot_nonneg_of_posSemidef` (`HC2b_DiagonalWeakRecentLoewner.lean`).  Dropping a
hypothesis is a strengthening; nothing in the conclusion moved. -/
theorem h6a_recentHead_actual_of_analytic
    (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (h1u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).1 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w))
    (h2u : ∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
      IntegrableOn (fun x => (optimizerField (respCoeffMinus F a) u x).2 j)
        (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).1 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n ∈ Finset.range (H + 1), ∀ w ∈ triadicIndexBox d n, ∀ j : Fin d,
        IntegrableOn (fun x => (optimizerField (respCoeffMinus F a)
          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x).2 j)
          (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)) →
      (∀ n : ℕ, ∃ G : (Fin d → ℤ) → ℝ,
        (∀ w ∈ triadicIndexBox d n,
          blockVecDot
              (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (fun x => optimizerField (respCoeffMinus F a) u x -
                    optimizerField (respCoeffMinus F a)
                      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
              (blockMatVecMul (blockSqrt (respM0 F))
                (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (fun x => optimizerField (respCoeffMinus F a) u x -
                    optimizerField (respCoeffMinus F a)
                      ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)))
            ≤ (Real.sqrt
                  (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))
                * (1 + Real.sqrt (respAllScaleMax P γ jStar F t a)
                    * (3 : ℝ) ^ (respRho γ * (n : ℝ) / 2))) ^ 2 * G w) ∧
        ((triadicIndexBox d n).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d n, G w
          ≤ 2 * respLsqMinus P jStar F t e
              * ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
                  (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) →
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a) u) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u))))
        ≤ 16 *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
            Real.sqrt (respLsqMinus P jStar F t e) *
            (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
                (respCoeffMinus F a) +
              weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by
  classical
  -- The former hypothesis `hLsq`, discharged from `hE`.
  have hLsq : 0 ≤ respLsqMinus P jStar F t e := by
    rw [respLsqMinus]
    exact h6a_blockVecDot_nonneg_of_posSemidef _ hE.posSemidef _
  obtain ⟨V, hV⟩ := h6a_recentHead_actual_le P γ hγ jStar H F t e hgrid a u hu hE hM0 hgood h1u h2u
  refine ⟨V, fun h1v h2v hin => hV h1v h2v (fun n => ?_)⟩
  obtain ⟨G, hcell, henergy⟩ := hin n
  exact h6a_scaleInput_of_analytic P γ jStar F t e a n
    (fun w x => optimizerField (respCoeffMinus F a) u x -
      optimizerField (respCoeffMinus F a)
        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) x)
    G hLsq hcell henergy

end

end Homogenization.HighContrast.Multiscale
