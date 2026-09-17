import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentAssembly
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakTailRoute
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakHeadRoute
import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakHeadBranchfree

/-!
# HC bridge II: the diagonal weak-norm primal bound (Lemma 2.16)

Split out of `HC2_WeakSeminorm.lean` to stay under the 800-line guard.  Paper
`p.response.transfer`.  The supporting lemmas now live in
`HC2b_DiagonalWeakRecentSupport.lean`,
`HC2b_DiagonalWeakRecentDegenerate.lean`,
`HC2b_DiagonalWeakRecentSupport2.lean` and
`HC2b_DiagonalWeakRecentCellSum.lean`; this file carries the target only.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock blockSub coarseBlock
  normalizedBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## AK.HC Lemma 2.16 on the selected grid, pathwise (the weak-norm kernel).
The earlier statement `diagonalWeakNorm_primal_le`
used the carriers of `DiagonalWeakNormCarriers.lean`.  Paper
`p.response.transfer`.

The right-hand side below is now the TRANSCRIBED old right-hand side, not a shape.  The
earlier placeholder (`∃ C, 0 < C ∧ C * K₀ * L⁻ * (3^{-αH}√(1+ℳ) + √ℳ)`) omitted the two finite
Step-5 sums and was flagged as possibly false as stated; it is replaced here.

SPECIALIZATION.  The old statement is stated for general `(rho, s, delta)`; this instance is
AK.HC Lemma 2.16 "with exponent 1/2, decay exponent rho, cutoff delta = 1, and window H"
(`p.response.transfer`), i.e. `s = 1/2`, `rho = respRho γ = (1+γ)/2`, `delta = 1`.
Arithmetic of the old side conditions under `_hγ : γ ∈ Set.Ico 0 1`, verified here:
* `0 < rho`   : `rho = (1+γ)/2 ≥ 1/2 > 0`                              ✓
* `rho < 2`   : `γ < 1` gives `rho < 1 < 2`                            ✓
* `rho/2 < s` : `(1+γ)/4 < 1/2 ⇔ γ < 1`                                ✓ (it is exactly `γ < 1`)
* `s ≤ 1`     : `1/2 ≤ 1`                                              ✓
* `0 < delta`, `delta ≤ 1` : `delta = 1`                               ✓
Two consequent simplifications are performed in the printed constants:
`(Real.sqrt delta)⁻¹ = (Real.sqrt 1)⁻¹ = 1`, and `2*s - rho = 1 - respRho γ` (`= (1-γ)/2
= 2 * respAlpha γ > 0`).  Also `s - rho/2 = 1/2 - (1+γ)/4 = (1-γ)/4 = respAlpha γ`, which is why
the tail weight is printed as `3^{-(respAlpha γ * H)}`.

CARRIER MAP (old ↦ current):
* `adaptedWeakSeminorm q t (1/2) F ↦ besovSeminorm t (cellAverageFamily q t F)` — real-valued;
  the statement is therefore an inequality in `ℝ`, not in `ℝ≥0∞`, and the outer
  `ENNReal.ofReal` on both sides disappears.
* `diagonalWeakMaximum rho q t E a ↦ respAllScaleMax P γ jStar F t a` (`AdaptedDefs.lean`) —
  REAL-valued, so the old `if … = ⊤ then ⊤ else …` guard VANISHES: there is no `⊤` branch left to
  state, and the `ℳ.toReal` of the old cutoff test is just `respAllScaleMax …`.
* `diagonalWeakMetricFactor m E ↦ Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P
  jStar F t) (respM0 F)))` — the `K₀` of `p.response.transfer`.  The old `(S, m)` binders
  (`S*S = m`, `S` symmetric) are absorbed into `respM0 F` and `blockSqrt`, so no `S`/`m` binders
  are added.
* `diagonalWeakLoadMinus E p r ↦ Real.sqrt (respLsqMinus P jStar F t e)` (`AdaptedDefs.lean`) —
  the loads `(p, r)` are the response coordinates of `e`, so no `p r` binders are added.
* `diagonalWeakCellDefect q (t-n) t ↦ weakCellDefect q t n`, `diagonalWeakAverageDefect ↦
  weakAverageDefect`, `diagonalWeakCellSum ↦ weakCellSum`, `diagonalWeakAverageSum ↦
  weakAverageSum`, `diagonalWeakEnergy ↦ weakOptimizerEnergy` — the five new `def`s above, each
  with its own note (`blockSize ↦ blockSpecBound ∘ normalizedBlock`, `avsum` spelled
  out, `variationEnergyValue` re-typed on `optimizerField`).
* `diagonalWeakState hq t a p r - blockCellAverage (adaptedCell q t) … ↦` the LEFT-hand side as it
  already stands (`cellAverageFamily … - cellAverage (respCell jStar F t) …`), kept byte-identical.
The `∃ C : ℝ, 0 < C ∧` wrapper of the placeholder is DROPPED: the old right-hand side carries the
explicit constants `16` and `16 * (√delta)⁻¹ / (2s - rho)`, and they are printed here. -/

/-- AK.HC Lemma 2.16 on the selected grid, pathwise: the scale-average seminorm of
the recentred doubled optimizer state is bounded by the two finite recent-scale sums plus the
older-scale energy term.  Transcribed at `s = 1/2`, `rho = respRho γ`,
`delta = 1`; see the section docstring for the carrier map.

The statement adds the binder `hgrid : IsUnit (respGrid
jStar F)`, which `cellAverage_optimizerField_eq_blockResponseMean` needs and which the
earlier binders did not supply, and the two defect sums now take the RECENTRED field
`respCoeffMinus F a` so that numerator and denominator are congruenced alike; the two defect
carriers themselves were repaired to the two-sided norm because a counterexample rules out the
one-sided version (see their docstrings). -/
theorem diagonalWeakNorm_primal_le (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F))
    (hint : HasIntegrableCoarseBlock P (respCell jStar F t))
    (a : CoeffSpace d)
    (hbdd : BddAbove {y : ℝ | ∃ m : ℕ, ∃ z ∈ triadicIndexBox d m, y =
      (3 : ℝ) ^ (-(respRho γ * (m : ℝ))) *
        blockSpecBound (blockSub
          (normalizedBlock (coarseBlock (adaptedCellAtCenter (respGrid jStar F) (t - (m : ℤ)) z) a)
            (respMean P jStar F t)) (Book.Ch02.blockIdentity d))})
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u) :
    (3 : ℝ) ^ (-((t : ℝ) / 2)) *
        besovSeminorm t (fun n w =>
          blockMatVecMul (blockSqrt (respM0 F))
            (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))) ≤
      16 * Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) *
          Real.sqrt (respLsqMinus P jStar F t e) *
          (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
              (respCoeffMinus F a) +
            weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatMinus P jStar F t)
              (respCoeffMinus F a)) +
        (16 / (1 - respRho γ) *
            Real.sqrt
              (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F)))) *
          (if 1 < respAllScaleMax P γ jStar F t a then
              Real.sqrt (respAllScaleMax P γ jStar F t a)
            else
              (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ)))) *
          weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u := by
  classical
  have hrho : respRho γ < 1 := by
    have := _hγ.2
    rw [respRho]
    linarith only [this]
  have hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef :=
    h6a_respEhatMinus_posDef_of_integrable hgrid t hint
  have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
    h6a_respM0_posDef_of_isUnit_respGrid hgrid
  have hm : (explicitCanonicalMetric F).PosDef :=
    h6a_explicitCanonicalMetric_posDef_of_isUnit_respGrid hgrid
  have hEmean : (toFullBlockMat (respMean P jStar F t)).PosDef :=
    h6a_respMean_posDef_of_integrable hgrid t hint
  obtain ⟨hbad, hgood⟩ :=
    h6a_tailBranches_minus P γ _hγ jStar H F t hgrid a u hm hEmean hE hM0 hbdd
  set K : ℝ :=
    Real.sqrt (blockSpecBound (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))) with hKdef
  set L : ℝ := Real.sqrt (respLsqMinus P jStar F t e) with hLdef
  set Ene : ℝ := weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) u with hEnedef
  set Sums : ℝ := 16 * K * L *
    (weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t) (respCoeffMinus F a) +
      weakAverageSum (respGrid jStar F) t H (respRho γ) (respEhatMinus P jStar F t)
        (respCoeffMinus F a)) with hSumsdef
  set c : ℝ := 16 / (1 - respRho γ) * K with hcdef
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hEne0 : 0 ≤ Ene := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := by
    have : 0 < 1 - respRho γ := by linarith only [hrho]
    rw [hcdef]
    positivity
  have hSums0 : 0 ≤ Sums := by
    have h1 : 0 ≤ weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
        (respCoeffMinus F a) := weakCellSum_nonneg _ _ _ _ _
    have h2 : 0 ≤ weakAverageSum (respGrid jStar F) t H (respRho γ)
        (respEhatMinus P jStar F t) (respCoeffMinus F a) := weakAverageSum_nonneg _ _ _ _ _ _
    rw [hSumsdef]
    have : 0 ≤ 16 * K * L := by positivity
    exact mul_nonneg this (by linarith only [h1, h2])
  have hMnn : 0 ≤ respAllScaleMax P γ jStar F t a := by
    have hSpecBound_nonneg : ∀ Hb : BlockMat d, 0 ≤ blockSpecBound Hb :=
      fun _ => Real.sInf_nonneg fun _ hx => hx.1
    refine Real.sSup_nonneg ?_
    rintro y ⟨m, z, _hz, rfl⟩
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hSpecBound_nonneg _)
  have hgood' : respAllScaleMax P γ jStar F t a ≤ 1 →
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n w =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
        ≤ Sums + c * (3 : ℝ) ^ (-(respAlpha γ * (H : ℝ))) * Ene := by
    intro hMle
    have hhead := h6a_recentHead_carrier_minus P γ _hγ jStar H F t e hgrid hint a hbdd u hu hMle
    have hhead' : (∑ n ∈ Finset.range (H + 1),
        (3 : ℝ) ^ (-((n : ℝ) / 2)) * Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverageFamily (respGrid jStar F) t
                      (optimizerField (respCoeffMinus F a) u) n w -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffMinus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverageFamily (respGrid jStar F) t
                      (optimizerField (respCoeffMinus F a) u) n w -
                    cellAverage (respCell jStar F t)
                      (optimizerField (respCoeffMinus F a) u))))) ≤ Sums := hhead
    have := hgood hMle
    linarith only [this, hhead']
  have hbad' : 1 < respAllScaleMax P γ jStar F t a →
      (3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n w =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
        ≤ c * Real.sqrt (respAllScaleMax P γ jStar F t a) * Ene := by
    intro hMgt
    have := hbad hMgt
    linarith only [this]
  have hkey := h6a_head_branchfree _hγ H hMnn
    ((3 : ℝ) ^ (-((t : ℝ) / 2)) *
      besovSeminorm t (fun n w =>
        blockMatVecMul (blockSqrt (respM0 F))
          (cellAverageFamily (respGrid jStar F) t (optimizerField (respCoeffMinus F a) u) n w -
            cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
    Sums Ene c c hc0 hc0 hSums0 hEne0 hgood' hbad'
  rwa [max_self] at hkey
end

end Homogenization.HighContrast.Multiscale
