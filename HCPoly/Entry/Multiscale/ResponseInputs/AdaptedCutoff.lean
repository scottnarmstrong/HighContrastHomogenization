import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeak
import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffKernelH8c

/-!
# The cutoff estimate

The cutoff estimate `e.response.cutoff.estimate`, one part of the proof of
`adapted_response_core`.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  aspectRatio)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## The cutoff estimate -/

/-- **The cutoff estimate** (`e.response.cutoff.estimate`):
`|Jtilde^±(e)| <= C(tau^± + (tau^± E[J_t^±])^{1/2} + (tau^± L_s^±)^{1/2}
  + 3^{-H}(E[J_t^±] + (E[J_t^±] L_s^±)^{1/2}) + W^±)`.

-- KERNEL.  This is the second true analytic kernel: the variational calculation of
`\cite[(3.45)--(3.54)]{AK.HC}` before Young's inequality, with `\cite[(3.46)]{AK.HC}` and
`\cite[Lemma A.1, (A.4)]{AK.HC}`, is never reproved in the paper.

Route (`p.response.transfer`): choose a cutoff `phi` of the class `IsResponseCutoff`.  The
cutoff compares the terminal optimizer with its scale-`s` cell optimizers, and the
quadratic-response identity measures the mean energy of their difference by `2 tau^±`.  Insert
`P^±, Q^±` into the cutoff decomposition; the term containing the difference between these
means and the actual annealed means is zero.  Integration by parts and the direct
full-dual pairing give
`E[|avg_{U_t} phi (grad v - P).(a grad v - Q)|] <= C W^±`.  The rounded/unrounded
metric comparison costs only a dimensional constant, since
`|m^{-1/2}q||q^{-1}m^{1/2}| <= 3`.  Keeping the last product is essential.

The proof combines the pieces established in
`HCPoly/Entry/Multiscale/ResponseInputs/HC3_CutoffKernel.lean`: `exists_isResponseCutoff` discharges the
choice of cutoff at `p.response.transfer`, the maximizer-existence lemmas supply the two maximizer
families, the cutoff-rows estimate gives the three error rows, the weak-pairing estimate gives
the cutoff pairing term, and the two are collected under `max C₁ C₂`.  The invertibility of the
selected grid comes from `RawOutput.hj/symm/pos`, and `0 ≤ W^±` from the weak-pairing estimate
itself (its left-hand side is an integral of absolute values).

The proof invokes `abs_respCenteredJ_le_cutoffRows`,
`integral_abs_hc3CutoffPairingOnCell_le_respWeak`, and the two `raw`-consuming integrability
lemmas `integrable_besovSeminorm_sq_respCell` and `integrable_abs_hc3CutoffPairingOnCell`.  The
theorem is axiom-clean.

It exports its own source threshold `Csrc`, in the same pattern as
`response_source_load_bound` and `response_weak_estimate`.  Two inputs need one: the
measurability and `L^Q(P)`-integrability of the all-scale maximum, which the two
`raw`-consuming lemmas consume, and the convergence of the source-load series at every dual
vector, which the `2d` coordinate readouts need and which is a theorem of
`h7_annealedBlock_le_adaptedMean`, whose threshold on `j_*` is not implied by an arbitrary
`Csrc`.  The exported threshold is the maximum of the two.  `AdaptedAssembly` in turn takes the
maximum of the thresholds exported by the inputs it combines, so the interface seen by consumers
is unchanged; the extra binder `0 ≤ Cglob` matches `response_source_load_bound`'s. -/
theorem response_cutoff_estimate (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) (Cc Ce Cl Cld : ℝ) (_hCc : 0 < Cc)
    (_hCe : 0 < Ce) (_hCl : 0 < Cl) (_hCld : 0 < Cld) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ : ℝ) (_hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (_hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
        (Cglob Cprof Bresp : ℝ) (_hCglob : 0 ≤ Cglob) (H : ℕ) (P : Measure (CoeffSpace d))
        (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ)
        (F : BlockMat d) (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        RespCalibrated Cc P jStar F s t →
        ∀ e : Vec d, vecDot e e = 1 →
          RespEnergyDefect Ce P jStar F s t e →
          RespLoadMean Cl P jStar F s t e →
          RespLoadBound Cld P jStar F s t e →
          RespCutoffBound C P jStar F H s t e := by
  classical
  have : NeZero d := ⟨by omega⟩
  -- Two source thresholds are exported by the inputs this proof consumes: `CsrcM`, above which
  -- the all-scale maximum is measurable and `L^Q(P)`-integrable, and `Csrc0`, above which the
  -- source-load series converges at every dual vector.  This theorem exports their maximum;
  -- `AdaptedAssembly` takes the maximum of the exported thresholds, and
  -- `h612_rawOutput_le_csrc` lowers `raw` to each.
  obtain ⟨CsrcM, hCsrcM, hMdata⟩ :=
    respAllScaleMax_aestronglyMeasurable_integrable d _hd γ _hγ S _hS
  obtain ⟨Csrc0, hCsrc0, hloadAllY⟩ := exists_summable_respSourceLoadSummand_all d _hd γ _hγ
  obtain ⟨C₁, hC₁, h8c⟩ := abs_respCenteredJ_le_cutoffRows d _hd
  obtain ⟨C₂, hC₂, h8b⟩ := integral_abs_hc3CutoffPairingOnCell_le_respWeak d
  refine ⟨max CsrcM Csrc0, lt_of_lt_of_le hCsrcM (le_max_left _ _), max C₁ C₂,
    lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src Bb jStar F s t raw hcal e _he hED
    _hLMean hLB
  -- The all-scale maximum of `p.response.transfer` is measurable and lies in
  -- `L^Q(P)`; this is the input the weak-quantity integrability consumes.
  obtain ⟨hMmeas, hMint⟩ := hMdata ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src Bb jStar F
    s t (h612_rawOutput_le_csrc raw (le_max_left _ _))
  have := raw.prob
  -- The selected grid is invertible (`RawOutput.hj`, `RawOutput.symm`, `RawOutput.pos`).
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
  -- The weak-pairing estimate carries `2 * d ≤ 3 ^ jStar`, without which the selected grid
  -- need not be invertible and the change of variables `x = q y` of `p.response.transfer` is
  -- unavailable at any constant.  It is discharged here by `raw.hj`, the very hypothesis that
  -- already supplies `hq` on the line above.
  have hjStar : 2 * d ≤ 3 ^ jStar := raw.hj
  -- A cutoff of the class exists: the ``p.response.transfer`` choice, discharged by
  -- `exists_isResponseCutoff`.
  obtain ⟨φ, hφ⟩ := exists_isResponseCutoff hq t
  -- Maximizer families for both signs.
  have hMne : ∀ a : CoeffSpace d,
      Nonempty (ScalarCanonicalMaximizer (respCell jStar F t)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a)) :=
    fun a => nonempty_scalarCanonicalMaximizer_respCoeffMinus (respGrid jStar F) hq t F a _ _
  have hPne : ∀ a : CoeffSpace d,
      Nonempty (ScalarCanonicalMaximizer (respCell jStar F t)
        (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respCoeffPlus F a)) :=
    fun a => nonempty_scalarCanonicalMaximizer_respCoeffPlus (respGrid jStar F) hq t F a _ _
  set uM : (a : CoeffSpace d) → AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t) :=
    fun a => (hMne a).some.toAHarmonicFunctionMeanZero.toAHarmonicFunction with huMdef
  set uP : (a : CoeffSpace d) → AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t) :=
    fun a => (hPne a).some.toAHarmonicFunctionMeanZero.toAHarmonicFunction with huPdef
  have huM : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a) :=
    fun a => (hMne a).some.isResponseMaximizer
  have huP : ∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a) :=
    fun a => (hPne a).some.isResponseMaximizer
  -- The weak-pairing estimate carries, once per sign, the integrability of the Besov square
  -- of the family whose cutoff pairing it bounds -- without it `W^±` collapses to the Bochner
  -- junk value `0` and the estimate is false.  Nothing in this theorem's own premises discharges
  -- it, so it is supplied by `integrable_besovSeminorm_sq_respCell`, whose statement consumes
  -- exactly `raw`.
  have hiM := integrable_besovSeminorm_sq_respCell d _hd γ S ε σ Cglob Cprof (max CsrcM Csrc0)
    Bresp H P E Ψ Kg Src Bb jStar F s t raw hMmeas hMint (respCoeffMinus F) (Or.inl rfl)
    (respP (respMean P jStar F t) e)
    (respqMinus P jStar F t e) (respYMinus P jStar F t e) uM huM
  have hiP := integrable_besovSeminorm_sq_respCell d _hd γ S ε σ Cglob Cprof (max CsrcM Csrc0)
    Bresp H P E Ψ Kg Src Bb jStar F s t raw hMmeas hMint (respCoeffPlus F) (Or.inr rfl)
    (respP (respMean P jStar F t) e)
    (respqPlus P jStar F t e) (respYPlus P jStar F t e) uP huP
  -- The cutoff-rows estimate carries `raw`-derivable premises.  Its eight premises are
  -- discharged here, in the order they appear in its statement.
  --
  -- (1) stationarity of the law -- load-bearing for the `e2` mean cancellation of
  -- `p.response.transfer` ("the scale-`s` translations are integral"), which is a
  -- stationarity argument: `E[(X)_{z+U_s}]` is independent of `z` only for a stationary law.
  have hstat : IsStationaryLaw P := raw.stat
  -- (2) invertibility of the selected grid is `hq`, already in hand above.
  -- (3) the response window lies above `j_*`.  `raw.hs_lo` places `s` at least
  -- `B log_3(2 + Pi)` generations above `j_*`; it is USABLE only with `1 <= B`, which needs
  -- `S.one_le_B0 ε σ hε hσ`, i.e. the two range hypotheses this theorem now carries (same
  -- pattern, same placement, as its siblings `response_energy_and_defect` and
  -- `response_load_and_mean`).  See `AdaptedSwarm.respAllScale_window` for the same derivation.
  have hjs : (jStar : ℤ) ≤ s := by
    have hB : (1 : ℝ) ≤ Bb :=
      le_trans (S.one_le_B0 ε σ hε hσ) (le_trans (le_max_left _ _) raw.hB)
    have hA : (1 : ℝ) ≤ aspectRatio E := Annealed.one_le_aspectRatio raw.ell
    have h3 : (3 : ℝ) ≤ 2 + aspectRatio E := by linarith
    have hlog : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
      have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      have h2 : Real.log 3 ≤ Real.log (2 + aspectRatio E) := Real.log_le_log (by norm_num) h3
      rw [Real.logb, le_div_iff₀ hl3]
      linarith
    have hpos : (0 : ℝ) < Bb * Real.logb 3 (2 + aspectRatio E) := by nlinarith
    have hceil : (0 : ℤ) < ⌈Bb * Real.logb 3 (2 + aspectRatio E)⌉ :=
      Int.lt_ceil.mpr (by exact_mod_cast hpos)
    have h1 := raw.hs_lo
    omega
  -- (4)/(5) entrywise integrability and positive-definiteness of the annealed block at every
  -- scale of the window, from `raw.stat`/`raw.ell`/`raw.hj` and `hm`
  -- (`Annealed.hasIntegrableCoarseBlock_adapted`, `Annealed.adaptedMean_posDef`).  Both hold at
  -- EVERY scale, so the `[j_*, t]` restriction of the cutoff-rows estimate's premises is
  -- discharged a fortiori.
  have hblk : ∀ k : ℤ, (jStar : ℤ) ≤ k → k ≤ t →
      HasIntegrableCoarseBlock P (respCell jStar F k) := by
    intro k _ _
    simpa only [respCell, respGrid, HighContrast.adaptedCellTranslate, zero_add, Set.image_id'] using
      Annealed.hasIntegrableCoarseBlock_adapted d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
        (explicitCanonicalMetric F) hm k 0
  have hblkw : ∀ (k : ℤ) (w : Fin d → ℤ),
      HasIntegrableCoarseBlock P (adaptedCellAtCenter (respGrid jStar F) k w) := by
    intro k w
    simpa only [respGrid, adaptedCellAtCenter] using
      Annealed.hasIntegrableCoarseBlock_adapted d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
        (explicitCanonicalMetric F) hm k (adaptedCellCenter (respGrid jStar F) k w)
  have hpd : ∀ k : ℤ, (jStar : ℤ) ≤ k → k ≤ t →
      (toFullBlockMat (respMean P jStar F k)).PosDef := by
    intro k _ _
    simpa only [respMean, respGrid] using
      Annealed.adaptedMean_posDef d _hd P γ E Ψ Kg Src raw.stat raw.ell jStar raw.hj
        (explicitCanonicalMetric F) hm k
  -- (6) the four pathwise-response integrabilities, and (7)/(8) the two cutoff-pairing
  -- integrabilities.  These parallel the Besov-square integrability carried by the
  -- weak-pairing estimate: they are supplied by `integrable_respJ_respCell` and
  -- `integrable_abs_hc3CutoffPairingOnCell`, whose statements consume exactly `raw`.
  have hjM : ∀ u : ℤ, (jStar : ℤ) ≤ u → u ≤ t →
      Integrable (fun a => respJ (respGrid jStar F) u (respP (respMean P jStar F t) e)
        (respqMinus P jStar F t e) (respCoeffMinus F a)) P :=
    fun u hlo hhi => integrable_respJ_respCell d γ S ε σ Cglob Cprof (max CsrcM Csrc0) Bresp H P
      E Ψ Kg Src Bb jStar F s t raw (respCoeffMinus F) (Or.inl rfl) u hlo hhi _ _
  have hjP : ∀ u : ℤ, (jStar : ℤ) ≤ u → u ≤ t →
      Integrable (fun a => respJ (respGrid jStar F) u (respP (respMean P jStar F t) e)
        (respqPlus P jStar F t e) (respCoeffPlus F a)) P :=
    fun u hlo hhi => integrable_respJ_respCell d γ S ε σ Cglob Cprof (max CsrcM Csrc0) Bresp H P
      E Ψ Kg Src Bb jStar F s t raw (respCoeffPlus F) (Or.inr rfl) u hlo hhi _ _
  have hst : s ≤ t := raw.hst.le
  have hpairM := integrable_abs_hc3CutoffPairingOnCell d _hd γ S ε σ Cglob Cprof (max CsrcM Csrc0)
    Bresp H P E Ψ Kg Src Bb jStar F s t raw hMmeas hMint (respCoeffMinus F) (Or.inl rfl) φ hφ
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respYMinus P jStar F t e) uM huM
  have hpairP := integrable_abs_hc3CutoffPairingOnCell d _hd γ S ε σ Cglob Cprof (max CsrcM Csrc0)
    Bresp H P E Ψ Kg Src Bb jStar F s t raw hMmeas hMint (respCoeffPlus F) (Or.inr rfl) φ hφ
    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e) (respYPlus P jStar F t e) uP huP
  -- The weak-pairing estimate and the cutoff-rows estimate on that cutoff and those families.
  obtain ⟨hbM, hbP⟩ := h8b P jStar F t e φ hjStar hφ uM huM hiM uP huP hiP
  -- The cutoff-rows estimate carries seven further premises, all `raw`-derivable here.
  -- The rounded grid is invertible from `raw.hj`/`raw.symm`/`raw.pos`; the flattened reference
  -- block is positive definite by `Annealed.fullBlock_posDef_of_pos`; the coarse ellipticity of
  -- the law is `raw.ell`; the two scale defects are nonnegative by `RespEnergyDefect`; and the
  -- source-load series converges at EVERY dual vector -- not only at the annealed means `Y^∓`
  -- of `RespLoadBound` -- by `exists_summable_respSourceLoadSummand_all`, whose own source
  -- threshold `Csrc0` this theorem exports in the same pattern as `response_source_load_bound`
  -- and `response_weak_estimate`.
  have hFfull : (toFullBlockMat F).PosDef :=
    Annealed.fullBlock_posDef_of_pos raw.symm raw.pos
  have hKg : (1 : ℝ) < Kg := raw.ell.one_lt_growthWitness
  have hlogK : (0 : ℝ) ≤ Real.logb 3 (2 * Kg) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hB1 : (1 : ℝ) ≤ Bb :=
    le_trans (S.one_le_B0 ε σ hε hσ) (le_trans (le_max_left _ _) raw.hB)
  have hPi := Annealed.aspectRatio_pos_and_three_le raw.ell
  have hlogPi : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    refine (Real.le_logb_iff_rpow_le (by norm_num) (by linarith [hPi.2])).mpr ?_
    rw [Real.rpow_one]
    linarith [hPi.2]
  have hthr : ⌈Csrc0 * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) := by
    refine le_trans (Int.ceil_le_ceil ?_) raw.hsrc
    have h0 : (0 : ℝ) ≤ Cglob * (Bb + 1) * Real.logb 3 (2 + aspectRatio E) :=
      mul_nonneg (mul_nonneg hCglob (by linarith)) (by linarith)
    have hmax : Csrc0 * Real.logb 3 (2 * Kg) ≤ max CsrcM Csrc0 * Real.logb 3 (2 * Kg) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hlogK
    linarith
  have hwin : HighContrast.adaptedCell (respGrid jStar F) s ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)) :=
    subset_trans (h7_adaptedCell_subset (respGrid jStar F) (le_of_lt raw.hst)) raw.cube
  have hcM0 : (0 : ℝ) ≤ Cc * Real.sqrt (respKappa P jStar F s) :=
    mul_nonneg _hCc.le (Real.sqrt_nonneg _)
  have hloadY := hloadAllY P E Ψ Kg Src raw.stat raw.ell jStar raw.hj hthr F hFfull hm s hjs
    hwin (Cc * Real.sqrt (respKappa P jStar F s)) hcM0 hcal.2.2.2.2.1 hcal.2.2.2.2.2
  obtain ⟨hcM, hcP⟩ := h8c P jStar F H s t e φ raw.ht hφ hstat hq hjs
    hjStar hm hFfull ⟨γ, E, Ψ, Kg, Src, raw.ell⟩
    (fun Y => (hloadY Y).1) (fun Y => (hloadY Y).2)
    hED.2.2.2.2.2.2.1 hED.2.2.2.2.2.2.2.1
    hLB.2.2.2.2.1 hLB.2.2.2.2.2 hblk hblkw hpd
    (hjM t (hjs.trans hst) le_rfl) (hjM s hjs hst) (hjP t (hjs.trans hst) le_rfl)
    (hjP s hjs hst) uM huM hpairM uP huP hpairP
  -- `W^± ≥ 0`: the cutoff pairing term is an integral of absolute values, so the weak-pairing
  -- estimate forces it.
  have hWM : 0 ≤ respWMinus P jStar F t e := by
    have h0 : (0 : ℝ) ≤
        ∫ a, |hc3CutoffPairingOnCell (respCell jStar F t) φ (respYMinus P jStar F t e)
          (respCoeffMinus F a) (uM a)| ∂P :=
      integral_nonneg fun a => abs_nonneg _
    nlinarith [hbM, hC₂]
  have hWP : 0 ≤ respWPlus P jStar F t e := by
    have h0 : (0 : ℝ) ≤
        ∫ a, |hc3CutoffPairingOnCell (respCell jStar F t) φ (respYPlus P jStar F t e)
          (respCoeffPlus F a) (uP a)| ∂P :=
      integral_nonneg fun a => abs_nonneg _
    nlinarith [hbP, hC₂]
  -- The final assembly collects the four rows under the single constant `max C₁ C₂`.
  exact respCutoffBound_of_cutoffRows_of_weakPairing C₁ C₂ hC₁ hC₂ P jStar F H s t e _ _
    hED.2.2.2.2.2.2.1 hED.2.2.2.2.2.2.2.1 hED.1 hED.2.1 hLB.1 hLB.2.1 hWM hWP hcM hcP hbM hbP

end Homogenization.HighContrast.Multiscale
