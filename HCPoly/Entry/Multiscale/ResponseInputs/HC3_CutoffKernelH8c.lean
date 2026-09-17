import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffKernelH8b
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsMeanRowClean
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsRow1Car
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsRowMono
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsPairSigned
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsHalfEnergyInt

/-!
# HC3_CutoffKernel, part 3 of 3

Continuation of `HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffKernel`, split at declaration boundaries so that
no module exceeds the 800-line isolation cap of
`scripts/check_isolation.py`.  Declaration statements, bodies and names
are unchanged; `private` is dropped only where a declaration is used from
a later part of the chain, since module privacy does not survive an import.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]
/-! ## The variational calculation of AK.HC (3.45)-(3.54) with the cutoff decomposition
(3.46) and the mean cancellation of `p.response.transfer`.

The two cutoff-mean terms `e2` below are exactly the two rows re-typed here onto the current
carriers `respTauMinus/Plus` (`AdaptedDefs.lean`), `respEJMinus/Plus`,
`respLsMinus/Plus`, the paper's `𝓛_s^±`, built from `respSourceLoad`).

The three error terms of `p.response.transfer` are, in order:

* `e1` — replacing the terminal optimizer by its scale-`s` cell optimizers:
  `C (τ^± + (τ^± E[J_t^±])^{1/2} + 3^{-H} E[J_t^±])`;
* `e2` — the two cutoff-mean terms, after subtracting the cell average of `φ`.  The constant cell
  means cancel after expectation because the scale-`s` translations are integral and
  `(φ)_{U_t} = 1`; what is left costs `C (τ^± 𝓛_s^±)^{1/2}`;
* `e3` — pairing the within-cell oscillations with the gradient and the flux and summing the
  descendants with weights `3^{3(k-s)/2}`: `C 3^{-H} (E[J_t^±] 𝓛_s^±)^{1/2}`.

The fourth summand on the right is the cutoff pairing term `e4`, bounded by `C W^±`; the
mean-cancellation assertion is exactly that NO further term (the difference between
the inserted means `P^±, Q^±` and the actual annealed means) appears in this decomposition. -/

/-- **Cutoff rows** (`p.response.transfer`; AK.HC (3.45)-(3.54) and (3.46)).  The cutoff
decomposition of the centred response, before Young's inequality: `|Jtilde^±(e)|` is bounded by
the three error rows `e1 + e2 + e3` plus the cutoff pairing term `e4`.

The original formulation of `IsResponseCutoff` was vacuous: it asked a function supported in a
cube of side `3^t` to have mean one while its pullback was only `3⁻ᵗ`-Lipschitz, and such a
function is at most `1 / 2` everywhere.  With the cutoff constant `32 * d ^ 2 * 3 ^ (-t)`,
`exists_isResponseCutoff` above constructs a member of the class, and what remains is the genuine
variational calculation of AK.HC (3.45)-(3.54).

Without the additional integrability hypotheses the theorem is false: three of the
four summands on each right-hand side are Bochner integrals whose integrands have no
sample-uniform bound (`respJ` is an `sSup` over an uncountable admissible class, and a point of
`CoeffSpace d` is only QUALITATIVELY elliptic -- see the collapse diagnostics above), so on a law
where they fail to be `P`-integrable the junk value `0` zeroes every error row and the statement
forces `Jtilde^±(e) = 0`, which the purely algebraic left-hand side does not satisfy.  That
implication is machine-checked above by `hc3_h8c_minus_row_forces_centeredJ_eq_zero`.

The CONCLUSION is unchanged, character for character.  Eight premises are ADDED, all of them
`raw`-derivable at the sole call site `response_cutoff_estimate` (`AdaptedCutoff.lean`), and every
one of them is discharged there:

| new premise | discharged at the call site from |
|---|---|
| `IsStationaryLaw P` | `raw.stat` |
| `IsUnit (respGrid jStar F)` | `raw.hj`, `raw.symm`, `raw.pos` (the existing `hq`) |
| `(jStar : ℤ) ≤ s` | `raw.hs_lo` **plus** the two range hypotheses `ε ∈ (0, S.eps0]`, `σ ∈ (0, ε]`, which `response_cutoff_estimate` now carries -- see below |
| the two `Summable (respSourceLoadSummand...)` | `hLB`, i.e. `RespLoadBound`, which now carries the summability of the source-load family as two further conjuncts.  Without them `respSourceLoad` is the junk value `0` of a divergent `tsum` and the two cutoff-mean rows assert that the centred cutoff mean vanishes |
| `HasIntegrableCoarseBlock P (respCell jStar F k)` on `[jStar, t]` | `Annealed.hasIntegrableCoarseBlock_adapted` from `raw.stat`, `raw.ell`, `raw.hj` |
| `(toFullBlockMat (respMean P jStar F k)).PosDef` on `[jStar, t]` | `Annealed.adaptedMean_posDef` from the same three fields |
| the four `Integrable (fun a => respJ... u... (respCoeff± F a)) P`, `u ∈ {s, t}` | the `raw`-consuming lemma `integrable_respJ_respCell` above |
| the two `Integrable (fun a => |hc3CutoffPairingOnCell...|) P` | the `raw`-consuming lemma `integrable_abs_hc3CutoffPairingOnCell` above |

`IsStationaryLaw P` is not decoration.  The mean-cancellation sentence this decomposition rests on
(`p.response.transfer`, "The constant cell means cancel after expectation, BECAUSE the
scale-`s` translations are integral and `(φ)_{U_t} = 1`") is a stationarity argument:
`E[(X)_{z+U_s}]` is independent of the translation `z` only for a stationary law, which in this
checkout is `Annealed.annealedBlock_adaptedCellAtCenter` (`HCPoly/Entry/Annealed/MeanOrder.lean`, whose
hypotheses are exactly `hstat`, `raw.hj` and `(jStar : ℤ) ≤ j` -- hence also the third premise
above).  Without it the `e2` row has no reason to close.

`hjs : jStar ≤ s` is not directly available in `raw` as `raw.hs_lo`: as `respAllScale_window`
(`AdaptedSwarm.lean`) records, `raw.hs_lo` reads
`jStar + ⌈B log_3(2 + Pi)⌉ ≤ s` and is VACUOUS unless `1 ≤ B`, which comes only from
`SelectionData.one_le_B0`, which is stated only for `ε ∈ (0, S.eps0]` and `σ ∈ (0, ε]`.
`response_cutoff_estimate` did not carry those two ranges.  They have therefore been ADDED to it,
in the same position and with the same names as its siblings
`response_energy_and_defect` (`AdaptedSwarm.lean`) and `response_load_and_mean`, and the one
place that applies it (`AdaptedAssembly.lean`, inside `adapted_response_core_of_holes`) passes the
`hε`/`hσε` it already has in context.  No statement is changed: `adapted_response_core` is
untouched.

**Seven further premises complete the variational calculation.**  The
variational calculation `e1 + e2 + e3` is closed: the energy-defect row `e1` by
`HC3_RowsRow1Car`, the cutoff-mean rows `e2 + e3` by `HC3_RowsMeanRowClean`, and the assembly by
`HC3_RowsObligations`.  Seven premises are ADDED, all `raw`-derivable at the sole call site
`response_cutoff_estimate` and all discharged there:

| new premise | discharged at the call site from |
|---|---|
| `2 ≤ d` (on the theorem itself) | `_hd` |
| `2 * d ≤ 3 ^ jStar` | `raw.hj` (already used there for `hq`) |
| `(explicitCanonicalMetric F).PosDef` | `Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos` (already in scope as `hm`) |
| `(toFullBlockMat F).PosDef` | `Annealed.fullBlock_posDef_of_pos raw.symm raw.pos` |
| `∃ γ E Ψ Kg Src, CoarseEllipticityDagger P γ E Ψ Kg Src` | `raw.ell` |
| the two `∀ Y, Summable (respSourceLoadSummand … Y)` | `exists_summable_respSourceLoadSummand_all` (`HC3_DirectLoadAllY`) from `raw.stat`, `raw.ell`, `raw.hj`, `raw.hsrc`, `raw.cube`, `raw.hst` and `RespCalibrated` |
| the two `0 ≤ respTau∓` | `RespEnergyDefect` (`hED`), which `response_cutoff_estimate` already carries |

The `∀ Y` summability is what the `2d` coordinate instantiations of the oscillation half need:
`RespLoadBound` supplies the source-load convergence only at `Y = Y^∓`, and at `Y = (0, δ_i)` the
generation layer is not dominated by the `Y^∓` layer.  Supplying it forced
`response_cutoff_estimate` to EXPORT its own source threshold `Csrc`, in the sibling pattern of
`response_source_load_bound` and `response_weak_estimate`; `AdaptedAssembly` takes the maximum, so
nothing downstream sees the change.  The conclusion of this theorem is unchanged, character for
character, and `RespCutoffBound` is untouched. -/
theorem abs_respCenteredJ_le_cutoffRows (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
        (H : ℕ) (s t : ℤ) (e : Vec d) (φ : Vec d → ℝ),
        t = s + (H : ℤ) →
        IsResponseCutoff (respGrid jStar F) t φ →
        -- Every one of the eight premises below is
        -- discharged at the sole call site `response_cutoff_estimate` (`AdaptedCutoff.lean`); see
        -- the section docstring for the discharge table.
        IsStationaryLaw P →
        IsUnit (respGrid jStar F) →
        (jStar : ℤ) ≤ s →
        -- Seven further premises, all `raw`-derivable at the sole
        -- call site `response_cutoff_estimate` and all discharged there; see the docstring table.
        2 * d ≤ 3 ^ jStar →
        (explicitCanonicalMetric F).PosDef →
        (toFullBlockMat F).PosDef →
        (∃ (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ),
          CoarseEllipticityDagger P γ E Ψ Kg Src) →
        (∀ Y : BlockVec d,
          Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F) Y)) →
        (∀ Y : BlockVec d,
          Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F) Y)) →
        0 ≤ respTauMinus P jStar F s t e →
        0 ≤ respTauPlus P jStar F s t e →
        Summable (respSourceLoadSummand P jStar F s (respCoeffMinus F)
          (respYMinus P jStar F t e)) →
        Summable (respSourceLoadSummand P jStar F s (respCoeffPlus F)
          (respYPlus P jStar F t e)) →
        (∀ k : ℤ, (jStar : ℤ) ≤ k → k ≤ t → HasIntegrableCoarseBlock P (respCell jStar F k)) →
        -- The terminal-optimizer
        -- replacement row compares the terminal cell with EVERY aligned cell of the coarse
        -- scale, so the entrywise integrability of the sample's coarse block is needed at every
        -- aligned translate and not only at the cell through the origin.  Discharged at
        -- `response_cutoff_estimate` by `Annealed.hasIntegrableCoarseBlock_adapted`, whose last
        -- argument is the translate and which the origin discharge already calls at `0`.
        (∀ (k : ℤ) (w : Fin d → ℤ),
          HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w)) →
        (∀ k : ℤ, (jStar : ℤ) ≤ k → k ≤ t →
          (toFullBlockMat (respMean P jStar F k)).PosDef) →
        Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)) P →
        Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
          (respqMinus P jStar F t e) (respCoeffMinus F a)) P →
        Integrable (fun a => respJ (respGrid jStar F) t (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)) P →
        Integrable (fun a => respJ (respGrid jStar F) s (respP (respMean P jStar F t) e)
          (respqPlus P jStar F t e) (respCoeffPlus F a)) P →
        ∀ uM : (a : CoeffSpace d) →
            AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) →
          Integrable (fun a =>
            |hc3CutoffPairingOnCell (respCell jStar F t) φ (respYMinus P jStar F t e)
              (respCoeffMinus F a) (uM a)|) P →
        ∀ uP : (a : CoeffSpace d) →
            AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) →
          Integrable (fun a =>
            |hc3CutoffPairingOnCell (respCell jStar F t) φ (respYPlus P jStar F t e)
              (respCoeffPlus F a) (uP a)|) P →
        |respCenteredJMinus P jStar F t e| ≤
              C * (respTauMinus P jStar F s t e +
                  Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
                  (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) +
                C * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
                C * ((3 : ℝ) ^ (-(H : ℝ)) *
                  Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) +
                (∫ a, |hc3CutoffPairingOnCell (respCell jStar F t) φ (respYMinus P jStar F t e)
                  (respCoeffMinus F a) (uM a)| ∂P) ∧
          |respCenteredJPlus P jStar F t e| ≤
              C * (respTauPlus P jStar F s t e +
                  Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
                  (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) +
                C * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
                C * ((3 : ℝ) ^ (-(H : ℝ)) *
                  Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) +
                (∫ a, |hc3CutoffPairingOnCell (respCell jStar F t) φ (respYPlus P jStar F t e)
                  (respCoeffPlus F a) (uP a)| ∂P) := by
  classical
  refine ⟨max (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
      (max 1 (respCutoffOscConst d)), ?_, ?_⟩
  · have h3 : (3 : ℝ) ≤ max (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
        (max 1 (respCutoffOscConst d)) := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  intro P _ jStar F H s t e φ ht hφ hstat hq hjs hjStar hm hF hdagE hsummM hsummP hτM hτP
    _hsumM0 _hsumP0 hblkk hblkw _hpd hJMt hJMs hJPt hJPs uM hmaxM hpairM uP hmaxP hpairP
  obtain ⟨γ, E, Ψ, Kg, Src, hdag⟩ := hdagE
  have hjt : (jStar : ℤ) ≤ t := by omega
  have hblkt : HasIntegrableCoarseBlock P (respCell jStar F t) := hblkk t hjt le_rfl
  have hφc : Continuous φ := hφ.2.2.2.2.2.1.continuous
  have hUm : MeasurableSet (respCell jStar F t) :=
    (isOpen_adaptedCell_of_isUnit hq t).measurableSet
  have hφint : IntegrableOn φ (respCell jStar F t) := by
    have h := integrableOn_isResponseCutoff hq hφ t 0
    rw [b130_adaptedCellAtCenter_zero] at h
    exact h
  have hφb : ∀ x : Vec d, ‖φ x‖ ≤ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ.1 x)]
    exact hφ.2.1 x
  have hEJM : 0 ≤ respEJMinus P jStar F t e := zero_le_respEJMinus P jStar F t e hq
  have hEJP : 0 ≤ respEJPlus P jStar F t e := zero_le_respEJPlus P jStar F t e hq
  have hEintM : ∀ a : CoeffSpace d, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a)) (respCell jStar F t) :=
    fun a => integrableOn_energy_respCell_respCoeffMinus jStar hjStar F hm t uM a
  have hEintP : ∀ a : CoeffSpace d, IntegrableOn
      (scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a)) (respCell jStar F t) :=
    fun a => integrableOn_energy_respCell_respCoeffPlus jStar hjStar F hm t uP a
  have hptM : ∀ (a : CoeffSpace d) (x : Vec d),
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
          (optimizerField (respCoeffMinus F a) (uM a) x).2
        = scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x := by
    intro a x
    simp only [scalarVariationEnergyIntegrand, optimizerField]
    exact (vecDot_matVecMul_symmPart (respCoeffMinus F a x) ((uM a).toH1.grad x)).symm
  have hptP : ∀ (a : CoeffSpace d) (x : Vec d),
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
          (optimizerField (respCoeffPlus F a) (uP a) x).2
        = scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x := by
    intro a x
    simp only [scalarVariationEnergyIntegrand, optimizerField]
    exact (vecDot_matVecMul_symmPart (respCoeffPlus F a x) ((uP a).toH1.grad x)).symm
  have hEcellM : ∀ a : CoeffSpace d, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
        (optimizerField (respCoeffMinus F a) (uM a) x).2) (respCell jStar F t) := by
    intro a
    refine ((hEintM a).bdd_mul (c := 2) hφc.measurable.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hφb)).congr (Filter.Eventually.of_forall fun x => ?_)
    show φ x * scalarVariationEnergyIntegrand (respCoeffMinus F a) (uM a) x
      = φ x * vecDot (optimizerField (respCoeffMinus F a) (uM a) x).1
          (optimizerField (respCoeffMinus F a) (uM a) x).2
    rw [hptM a x]
  have hEcellP : ∀ a : CoeffSpace d, IntegrableOn (fun x => φ x *
      vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
        (optimizerField (respCoeffPlus F a) (uP a) x).2) (respCell jStar F t) := by
    intro a
    refine ((hEintP a).bdd_mul (c := 2) hφc.measurable.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall hφb)).congr (Filter.Eventually.of_forall fun x => ?_)
    show φ x * scalarVariationEnergyIntegrand (respCoeffPlus F a) (uP a) x
      = φ x * vecDot (optimizerField (respCoeffPlus F a) (uP a) x).1
          (optimizerField (respCoeffPlus F a) (uP a) x).2
    rw [hptP a x]
  obtain ⟨-, -, -, -, hM1M, hM2M, -, -⟩ :=
    integrable_cutoffMeanDefect_coords_respCoeffMinus hd P hstat γ E Ψ Kg Src hdag jStar hjStar
      F hm H s t ht hjs e φ hφ uM hmaxM hEintM hJMt hsummM
  obtain ⟨-, -, -, -, hM1P, hM2P, -, -⟩ :=
    integrable_cutoffMeanDefect_coords_respCoeffPlus hd P hstat γ E Ψ Kg Src hdag jStar hjStar
      F hm H s t ht hjs e φ hφ uP hmaxP hEintP hJPt hsummP
  have hrow1M := cutoffEnergyDefectRowMinus_of_carriers_clean P hstat jStar hjStar F hm H s t ht
    hjs e φ hφ uM hmaxM hblkw hJMt hJMs
  have hrow1P := cutoffEnergyDefectRowPlus_of_carriers_clean P hstat jStar hjStar F hm H s t ht
    hjs e φ hφ uP hmaxP hblkw hJPt hJPs
  have hrow2M := cutoffMeanRowMinus_of_carriers hd P hstat γ E Ψ Kg Src hdag jStar hjStar F hm hF
    H s t ht hjs e φ hφ uM hmaxM hblkw hblkt hJMt hJMs hsummM hτM
  have hrow2P := cutoffMeanRowPlus_of_carriers hd P hstat γ E Ψ Kg Src hdag jStar hjStar F hm hF
    H s t ht hjs e φ hφ uP hmaxP hblkw hblkt hJPt hJPs hsummP hτP
  refine ⟨?_, ?_⟩
  · exact abs_respCenteredJMinus_le_cutoffRows_of_obligations P jStar F t e φ uM hq hblkt hJMt
      (integrable_half_hc3CutoffPairingOnCellAux_respCoeffMinus P jStar F t hjStar hm φ hφ
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
        (respYMinus P jStar F t e) uM hmaxM hpairM)
      (integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffMinus P jStar hjStar F hm t e φ hφ uM
        hmaxM hJMt)
      hM1M hM2M hφ hφint hEcellM
      (fun a i => (integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm
        t uM hUm (fun x hx => hx) hφc a i).1)
      (fun a i => (integrableOn_weighted_optimizerField_respCell_respCoeffMinus jStar hjStar F hm
        t uM hUm (fun x hx => hx) hφc a i).2)
      (max (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
        (max 1 (respCutoffOscConst d))) H s
      (cutoffEnergyDefectRowMinus_mono P jStar F H s t e φ uM hτM hEJM
        (le_max_left _ _) hrow1M)
      (cutoffMeanRowMinus_mono P jStar F H s t e φ uM (le_max_right _ _) hrow2M)
  · exact abs_respCenteredJPlus_le_cutoffRows_of_obligations P jStar F t e φ uP hq hblkt hJPt
      (integrable_half_hc3CutoffPairingOnCellAux_respCoeffPlus P jStar F t hjStar hm φ hφ
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
        (respYPlus P jStar F t e) uP hmaxP hpairP)
      (integrable_cutoffHalfEnergyAux_sub_respJ_respCoeffPlus P jStar hjStar F hm t e φ hφ uP
        hmaxP hJPt)
      hM1P hM2P hφ hφint hEcellP
      (fun a i => (integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm
        t uP hUm (fun x hx => hx) hφc a i).1)
      (fun a i => (integrableOn_weighted_optimizerField_respCell_respCoeffPlus jStar hjStar F hm
        t uP hUm (fun x hx => hx) hφc a i).2)
      (max (max 3 (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst))
        (max 1 (respCutoffOscConst d))) H s
      (cutoffEnergyDefectRowPlus_mono P jStar F H s t e φ uP hτP hEJP
        (le_max_left _ _) hrow1P)
      (cutoffMeanRowPlus_mono P jStar F H s t e φ uP (le_max_right _ _) hrow2P)

/-! ## The final combination of the cutoff rows and the weak pairing.

The two branches combine the primal and adjoint rows of the cutoff decomposition against the
weak quantity under one common constant.  The conclusion is LITERALLY `RespCutoffBound`
(`AdaptedAlgebra.lean`), i.e. exactly the payload of `response_cutoff_estimate`
(`AdaptedCutoff.lean`). -/

omit [NeZero d] in
/-- **Cutoff bound from the rows and the weak pairing** (`p.response.transfer`,
`e.response.cutoff.estimate`).  The three error rows of the cutoff decomposition plus the bound
on the cutoff pairing term combine, under the common constant `max C₁ C₂`, into
`RespCutoffBound`.

`eM`/`eP` stand for the two expected cutoff pairing terms `e4^∓`, so that `hrowsMinus`/`hrowsPlus`
are the cutoff-row conclusions and `hweakMinus`/`hweakPlus` the weak-pairing conclusions.  The
nonnegativity hypotheses are the ones needed to collect the rows under a single constant; each is
available in the calling context (`RespLoadBound` `AdaptedAlgebra.lean` and `RespWeakBound`
 already assert nonnegativity of `𝓛_s^±` and of `W^±`). -/
theorem respCutoffBound_of_cutoffRows_of_weakPairing
    (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ) (s t : ℤ) (e : Vec d)
    (eM eP : ℝ)
    (hτM : 0 ≤ respTauMinus P jStar F s t e) (hτP : 0 ≤ respTauPlus P jStar F s t e)
    (hEJM : 0 ≤ respEJMinus P jStar F t e) (hEJP : 0 ≤ respEJPlus P jStar F t e)
    (hLM : 0 ≤ respLsMinus P jStar F s t e) (hLP : 0 ≤ respLsPlus P jStar F s t e)
    (hWM : 0 ≤ respWMinus P jStar F t e) (hWP : 0 ≤ respWPlus P jStar F t e)
    (hrowsMinus : |respCenteredJMinus P jStar F t e| ≤
      C₁ * (respTauMinus P jStar F s t e +
          Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
          (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) +
        C₁ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
        C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) + eM)
    (hrowsPlus : |respCenteredJPlus P jStar F t e| ≤
      C₁ * (respTauPlus P jStar F s t e +
          Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
          (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) +
        C₁ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
        C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) + eP)
    (hweakMinus : eM ≤ C₂ * respWMinus P jStar F t e)
    (hweakPlus : eP ≤ C₂ * respWPlus P jStar F t e) :
    RespCutoffBound (max C₁ C₂) P jStar F H s t e := by
  -- The first four `have` statements are no-op uses of the binders the `unusedVariables` linter
  -- flags; the two strict positivities are part of the contract with `response_cutoff_estimate`
  -- but only `le_max_left`/`le_max_right` are needed below.
  have _ := hC₁
  have _ := hC₂
  have _ := hLM
  have _ := hLP
  have hle1 : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hle2 : C₂ ≤ max C₁ C₂ := le_max_right _ _
  have hp : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
  refine ⟨?_, ?_⟩
  · -- Minus row.
    have expand1 :
        C₁ * (respTauMinus P jStar F s t e +
            Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) +
          C₁ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
          C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) + eM
        = C₁ * respTauMinus P jStar F s t e
            + C₁ * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + C₁ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e)
            + C₁ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
            + C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
                Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))
            + eM := by ring
    rw [expand1] at hrowsMinus
    have expand2 :
        max C₁ C₂ * (respTauMinus P jStar F s t e +
            Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
            Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * (respEJMinus P jStar F t e +
              Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) +
            respWMinus P jStar F t e)
        = max C₁ C₂ * respTauMinus P jStar F s t e
            + max C₁ C₂ * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
            + max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e)
            + max C₁ C₂ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
            + max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
                Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e))
            + max C₁ C₂ * respWMinus P jStar F t e := by ring
    rw [expand2]
    have i1 : C₁ * respTauMinus P jStar F s t e ≤ max C₁ C₂ * respTauMinus P jStar F s t e :=
      mul_le_mul_of_nonneg_right hle1 hτM
    have i2 : C₁ * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) ≤
        max C₁ C₂ * Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) :=
      mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    have i3 : C₁ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) ≤
        max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJMinus P jStar F t e) :=
      mul_le_mul_of_nonneg_right hle1 (mul_nonneg hp hEJM)
    have i4 : C₁ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) ≤
        max C₁ C₂ * Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) :=
      mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    have i5 : C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) ≤
        max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) :=
      mul_le_mul_of_nonneg_right hle1 (mul_nonneg hp (Real.sqrt_nonneg _))
    have i6 : eM ≤ max C₁ C₂ * respWMinus P jStar F t e := by
      have h := mul_le_mul_of_nonneg_right hle2 hWM
      linarith [hweakMinus]
    linarith [hrowsMinus, i1, i2, i3, i4, i5, i6]
  · -- Plus row, symmetric.
    have expand1 :
        C₁ * (respTauPlus P jStar F s t e +
            Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) +
          C₁ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
          C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
            Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) + eP
        = C₁ * respTauPlus P jStar F s t e
            + C₁ * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + C₁ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e)
            + C₁ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
            + C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
                Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))
            + eP := by ring
    rw [expand1] at hrowsPlus
    have expand2 :
        max C₁ C₂ * (respTauPlus P jStar F s t e +
            Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
            Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
            (3 : ℝ) ^ (-(H : ℝ)) * (respEJPlus P jStar F t e +
              Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) +
            respWPlus P jStar F t e)
        = max C₁ C₂ * respTauPlus P jStar F s t e
            + max C₁ C₂ * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
            + max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e)
            + max C₁ C₂ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
            + max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
                Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e))
            + max C₁ C₂ * respWPlus P jStar F t e := by ring
    rw [expand2]
    have i1 : C₁ * respTauPlus P jStar F s t e ≤ max C₁ C₂ * respTauPlus P jStar F s t e :=
      mul_le_mul_of_nonneg_right hle1 hτP
    have i2 : C₁ * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) ≤
        max C₁ C₂ * Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) :=
      mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    have i3 : C₁ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) ≤
        max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) * respEJPlus P jStar F t e) :=
      mul_le_mul_of_nonneg_right hle1 (mul_nonneg hp hEJP)
    have i4 : C₁ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) ≤
        max C₁ C₂ * Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) :=
      mul_le_mul_of_nonneg_right hle1 (Real.sqrt_nonneg _)
    have i5 : C₁ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) ≤
        max C₁ C₂ * ((3 : ℝ) ^ (-(H : ℝ)) *
          Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) :=
      mul_le_mul_of_nonneg_right hle1 (mul_nonneg hp (Real.sqrt_nonneg _))
    have i6 : eP ≤ max C₁ C₂ * respWPlus P jStar F t e := by
      have h := mul_le_mul_of_nonneg_right hle2 hWP
      linarith [hweakPlus]
    linarith [hrowsPlus, i1, i2, i3, i4, i5, i6]


end

end Homogenization.HighContrast.Multiscale
