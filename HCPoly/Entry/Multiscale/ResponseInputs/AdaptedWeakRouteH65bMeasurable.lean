import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65bCore

/-!
# AdaptedWeakRouteH65b, part 2 of 2

Continuation of `HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRouteH65b`, split at declaration boundaries so that
no module exceeds the 800-line isolation cap of
`scripts/check_isolation.py`.  Declaration statements, bodies and names
are unchanged; `private` is dropped only where a declaration is used from
a later part of the chain, since module privacy does not survive an import.
-/

open Homogenization.HighContrast (CoeffSpace aspectRatio)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}
/-- **Measurability and `L^Q`-integrability of `M` under `RawOutput`**.  NOTE: the
hypothesis `∫ M^Q ∂P ≤ C_m η` is a Bochner integral with no integrability side condition, so this
is genuinely needed to use it (else the integral is the junk `0`).  `M` is an `sSup` over the
countable family `(n, z)`, each term measurable in `a` through the coarse blocks (`RawOutput`
integrable-coarse-block fields); the bound comes from a.e. ellipticity.

FIRST CONJUNCT: proved by
`respAllScaleMax_measurable` above — the countable-`sSup` route, with `blockSpecBound` shown
continuous by an attained-infimum/Lipschitz argument that needs no semidefiniteness of its
(indefinite) argument `normalizedBlock A E_t − I`.

SECOND CONJUNCT: not derivable from the statement's previous binder set, in which `Csrc` was
universally quantified: every route to an integrable majorant for `M^Q` goes through the
deep scales `k < j_*`, and the only tools for those are
`Source.source_multiplier_and_adapted_bound` (`AdaptedBound.lean`) and
`Annealed.adaptedMean_refBlock_normalization` (`ReferenceNormalization.lean`), each of which
*produces* a positive `Csrc_i` and demands the threshold `⌈Csrc_i · logb 3 (2 K)⌉ ≤ j_*`.
`RawOutput.hsrc` supplies that threshold only for the `Csrc` of the binder, which under a `∀`
may be zero or negative, and `RawOutput.hj` gives only `2d ≤ 3^{j_*}`.  Three premises are
therefore carried, each of them forced and each of them already carried by the all-scale
maximum bound, whose machinery this proof reuses:

* `Csrc` is **produced** (`∃ Csrc, 0 < Csrc ∧ …`) rather than taken, exactly as
  `Source.source_multiplier` and every other Source consumer in the tree produces it.  The
  assembly consuming this statement reconciles its `Csrc` with that of the all-scale maximum
  bound and with those of the other estimates it combines by the tree's own `max`-ing idiom
  (`HCPoly/Entry/OneGridPropagation.lean`).
* `ε ∈ Ioc 0 S.eps0` and `σ ∈ Ioc 0 ε`: `SelectionData.one_le_B0` holds only on
  that range, and without it `respAllScale_window`'s `j_* < t` — needed even on the fluctuation
  side — is unavailable.
* `0 ≤ Cglob`: needed to drop the first summand of `raw.hsrc` when specialising
  it to the source threshold.

The strengthened statement's satisfiability is exhibited inside the proof itself —
the `∃ Csrc` witness is `max Csrc₁ Csrc₂ > 0`, and the source-smallness pair is chosen here as
`Cs := 1`, `η := (1 + Y)^Q`, so that the `RespSourceSmall` inequality holds **by construction**
(`Y ≤ 1 + Y`).  No `RespSourceSmall` premise and no `η ∈ Ioo 0 (1/2)` premise is added:
integrability, unlike the quantitative bound `∫ M^Q ≤ C η`, does not care about the constant.  No new
constraint is placed on `SelectionData` or on `Selects`, so no separate selection-satisfiability
obligation arises.

The helpers this proof needs were `private`; they are made available by dropping `private` from
three declarations of `AdaptedSwarm.lean` — `respAllScale_window`,
`h5rc_add3_pow_le` and `h5rc_pathwise_bound` — with no statement and no proof
changed there.  `h5ra_scale_index_le`, `h5rc_fluctuation_term_le`, `h5rc_source_term_le` and
`respAllScaleMax_le_of_forall` stay `private`; `AdaptedSwarm`'s `respAllScaleMax_nonneg` also
stays `private`, because this file already carries a public copy of it, which is the one used
here. -/
theorem respAllScaleMax_aestronglyMeasurable_integrable (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P ∧
              Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P := by
  obtain ⟨Csrc₁, C₀, hCsrc₁, hC₀, hsrcm⟩ :=
    Source.source_multiplier_and_adapted_bound d hd γ hγ
  obtain ⟨Csrc₂, Cn, hCsrc₂, hCn, hrefn⟩ :=
    Annealed.adaptedMean_refBlock_normalization d hd γ hγ
  refine ⟨max Csrc₁ Csrc₂, lt_max_of_lt_left hCsrc₁, ?_⟩
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw
  let : NeZero d := ⟨by omega⟩
  have := raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid raw.hj hm
  have hMmeas : Measurable (respAllScaleMax P γ jStar F t) :=
    respAllScaleMax_measurable P γ jStar F hq t
  refine ⟨hMmeas.aestronglyMeasurable, ?_⟩
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d hd γ hγ
  have hQ0 : bigQ d γ ≠ 0 := by omega
  have hwin := respAllScale_window d hd γ S ε σ Cglob Cprof (max Csrc₁ Csrc₂) Bresp H P E Ψ Kg
    Src B jStar F s t hε hσ raw
  have hjt : (jStar : ℤ) ≤ t := le_of_lt hwin.2
  have hB0 : (1 : ℝ) ≤ S.B0 ε σ := S.one_le_B0 ε σ hε hσ
  have hB : (1 : ℝ) ≤ B := hB0.trans ((le_max_left _ _).trans raw.hB)
  have hA1 : (1 : ℝ) ≤ aspectRatio E := Annealed.one_le_aspectRatio raw.ell
  have hlog : (1 : ℝ) ≤ Real.logb 3 (2 + aspectRatio E) := by
    have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
    have h2 : Real.log 3 ≤ Real.log (2 + aspectRatio E) :=
      Real.log_le_log (by norm_num) (by linarith)
    rw [Real.logb, le_div_iff₀ hl3]
    linarith
  have hlogK : (0 : ℝ) ≤ Real.logb 3 (2 * Kg) :=
    Real.logb_nonneg (by norm_num) (by linarith [raw.ell.one_lt_growthWitness])
  have hthr : ∀ c : ℝ, c ≤ max Csrc₁ Csrc₂ → ⌈c * Real.logb 3 (2 * Kg)⌉ ≤ (jStar : ℤ) := by
    intro c hc
    refine le_trans (Int.ceil_mono ?_) raw.hsrc
    have h1 : c * Real.logb 3 (2 * Kg) ≤ max Csrc₁ Csrc₂ * Real.logb 3 (2 * Kg) :=
      mul_le_mul_of_nonneg_right hc hlogK
    have h2 : (0 : ℝ) ≤ Cglob * (B + 1) * Real.logb 3 (2 + aspectRatio E) :=
      mul_nonneg (mul_nonneg hCglob (by linarith)) (by linarith)
    linarith
  obtain ⟨ell, X, hell, hXm, hform, hmin, hlp, hXint, hXmom, hXnorm, hpath⟩ :=
    hsrcm P E Ψ Kg Src raw.stat raw.ell jStar raw.hj (hthr Csrc₁ (le_max_left _ _))
  have hnormt := (hrefn P E Ψ Kg Src raw.stat raw.ell jStar raw.hj
    (hthr Csrc₂ (le_max_right _ _)) (explicitCanonicalMetric F) hm t hjt raw.cube).2
  have hX0 : ∀ a, (0 : ℝ) < X a := fun a => by rw [hform]; positivity
  obtain ⟨hfint, -⟩ := oneGrid_fluctuation_integrable_dominate d hd γ hγ P E Ψ Kg Src raw.stat
    raw.ell jStar raw.hj (explicitCanonicalMetric F) hm t
  set F0 : CoeffSpace d → ℝ := fun a => ⨆ j ∈ Set.Icc (jStar : ℤ) t,
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
      ⨆ z ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j ∩
          HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t,
        blockOpNorm (normalizedFluctuation P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
          j t z a) ^ bigQ d γ with hF0def
  have hF00 : ∀ a, (0 : ℝ) ≤ F0 a := fun a =>
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.iSup_nonneg fun z => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hDr0 : (0 : ℝ) ≤ determinantDrift P γ
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t :=
    determinantDrift_nonneg d hd γ hγ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm t
  -- The choice of the source-smallness pair `(Cs, η)`: only positivity and the one inequality
  -- of `h5rc_pathwise_bound` are needed, so take `Cs = 1` and `η = (1 + Y)^Q`.
  -- This is the explicit witness making the strengthened statement satisfiable.
  set Y : ℝ := aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
    (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) with hYdef
  have hPi : (0 : ℝ) < aspectRatio E := (Annealed.aspectRatio_pos_and_three_le raw.ell).1
  have hY0 : (0 : ℝ) ≤ Y := by
    rw [hYdef]; positivity
  set η : ℝ := (1 + Y) ^ bigQ d γ with hηdef
  have hη : (0 : ℝ) < η := by rw [hηdef]; exact pow_pos (by linarith) _
  have hηroot : η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) = 1 + Y := by
    rw [hηdef, one_div]
    exact Real.pow_rpow_inv_natCast (by linarith) hQ0
  have hsrcsmall : (1 : ℝ) * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) := by
    rw [hηroot, one_mul, ← hYdef]
    linarith
  set Kw : ℝ := C₀ * Cn / 1 with hKwdef
  have hKw : (0 : ℝ) < Kw := by rw [hKwdef]; positivity
  have hkey : ∀ᵐ a ∂P, respAllScaleMax P γ jStar F t a ^ bigQ d γ ≤
      (3 : ℝ) ^ bigQ d γ * (F0 a +
        (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t) ^
          bigQ d γ + (Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ) := by
    filter_upwards [hpath] with a ha
    have hu0 : (0 : ℝ) ≤ F0 a ^ ((bigQ d γ : ℝ)⁻¹) := Real.rpow_nonneg (hF00 a) _
    have hw0 : (0 : ℝ) ≤ Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a :=
      mul_nonneg (mul_nonneg hKw.le (Real.rpow_nonneg hη.le _)) (hX0 a).le
    have hMle : respAllScaleMax P γ jStar F t a ≤
        F0 a ^ ((bigQ d γ : ℝ)⁻¹) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t +
          Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a :=
      h5rc_pathwise_bound d hd γ hγ P E Ψ Kg Src raw.stat raw.unit raw.ell jStar raw.hj F hm
        t hjt raw.cube C₀ Cn 1 η hC₀ hCn one_pos hη X a (hX0 a) ha.2 hnormt hsrcsmall
    calc respAllScaleMax P γ jStar F t a ^ bigQ d γ
        ≤ (F0 a ^ ((bigQ d γ : ℝ)⁻¹) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t +
            Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a) ^ bigQ d γ :=
          pow_le_pow_left₀ (respAllScaleMax_nonneg P γ jStar F t a) hMle _
      _ ≤ (3 : ℝ) ^ bigQ d γ * ((F0 a ^ ((bigQ d γ : ℝ)⁻¹)) ^ bigQ d γ +
            (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
              jStar t) ^ bigQ d γ +
            (Kw * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a) ^ bigQ d γ) :=
          h5rc_add3_pow_le _ _ _ _ hu0 hDr0 hw0
      _ = (3 : ℝ) ^ bigQ d γ * (F0 a +
            (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
              jStar t) ^ bigQ d γ + (Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ) := by
          rw [Real.rpow_inv_natCast_pow (hF00 a) hQ0, hηroot, mul_pow]
  have hi1 : Integrable (fun a => F0 a +
      (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t) ^
        bigQ d γ) P := hfint.add (integrable_const _)
  have hi2 : Integrable (fun a => (Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ) P :=
    hXint.const_mul _
  have hgint : Integrable (fun a => (3 : ℝ) ^ bigQ d γ * (F0 a +
      (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t) ^
        bigQ d γ + (Kw * (1 + Y)) ^ bigQ d γ * X a ^ bigQ d γ)) P :=
    (hi1.add hi2).const_mul _
  refine hgint.mono' ((hMmeas.pow_const _).aestronglyMeasurable) ?_
  filter_upwards [hkey] with a ha
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (respAllScaleMax_nonneg P γ jStar F t a) _)]
  exact ha



end

end Homogenization.HighContrast.Multiscale
