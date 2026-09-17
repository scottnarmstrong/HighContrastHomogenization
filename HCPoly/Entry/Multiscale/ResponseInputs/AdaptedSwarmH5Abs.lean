import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedSwarmH5

/-!
# AdaptedSwarm, part 9 of 11

Continuation of `HCPoly.Entry.Multiscale.ResponseInputs.AdaptedSwarm`, split at declaration boundaries so that
no module exceeds the 800-line isolation cap of
`scripts/check_isolation.py`.  Declaration statements, bodies and names
are unchanged; `private` is dropped only where a declaration is used from
a later part of the chain, since module privacy does not survive an import.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedMean annealedBlock
  aspectRatio blockScale coarseBlock matSqrt matSqrt_spec)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open scoped Matrix MatrixOrder

variable {d : ℕ}
/-- Two-term form of `h5rc_add3_pow_le`. -/
private theorem h5abs_add2_pow_le (Q : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u + v) ^ Q ≤ 3 ^ Q * (u ^ Q + v ^ Q + v ^ Q) := by
  refine le_trans (pow_le_pow_left₀ (by linarith) (show u + v ≤ u + v + v by linarith) Q) ?_
  exact h5rc_add3_pow_le Q u v v hu hv hv

/-- Four-term form of `h5rc_add3_pow_le`, needed because the two-sided pathwise bound has the
extra source summand. -/
theorem h5abs_add4_pow_le (Q : ℕ) (u v w x : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hx : 0 ≤ x) :
    (u + v + w + x) ^ Q ≤ 3 ^ Q * (u ^ Q + v ^ Q + 3 ^ Q * (w ^ Q + x ^ Q + x ^ Q)) := by
  have h1 : (u + v + (w + x)) ^ Q ≤ 3 ^ Q * (u ^ Q + v ^ Q + (w + x) ^ Q) :=
    h5rc_add3_pow_le Q u v (w + x) hu hv (by linarith)
  have h2 : (w + x) ^ Q ≤ 3 ^ Q * (w ^ Q + x ^ Q + x ^ Q) := h5abs_add2_pow_le Q w x hw hx
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ Q := by positivity
  have h4 : u + v + w + x = u + v + (w + x) := by ring
  rw [h4]
  calc (u + v + (w + x)) ^ Q ≤ 3 ^ Q * (u ^ Q + v ^ Q + (w + x) ^ Q) := h1
    _ ≤ 3 ^ Q * (u ^ Q + v ^ Q + 3 ^ Q * (w ^ Q + x ^ Q + x ^ Q)) :=
        mul_le_mul_of_nonneg_left (by linarith) h3

/-- **The pathwise two-sided all-scale bound**: the two branches combined through
`respAllScaleAbs_le_of_forall`.  `respAllScaleAbs_aestronglyMeasurable_integrable`
(`AdaptedWeakRoute.lean`) needs the same pathwise majorant this gives.  It is
`h5rc_pathwise_bound` with one extra summand, `eta^{1/Q} / C_s`, which is the whole cost of the
lower Loewner side. -/
theorem h5abs_pathwise_bound (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hunit : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ Kg Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (F : BlockMat d)
    (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ) (ht : (jStar : ℤ) ≤ t)
    (hcube : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)))
    (C₀ Cn Cs η : ℝ) (hC₀ : 0 < C₀) (hCn : 0 < Cn) (hCs : 0 < Cs) (hη : 0 < η)
    (X : CoeffSpace d → ℝ) (a : CoeffSpace d) (hXa : 0 < X a)
    (hpath : ∀ (mm : Mat d), mm.PosDef → ∀ (j : ℤ) (y : Vec d),
      HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar mm) j y ⊆
          HighContrast.centeredCube d (2 * (jStar : ℤ)) →
        BlockMatLoewnerLE (coarseBlock (HighContrast.adaptedCellTranslate
            (Geometry.explicitRoundedGrid jStar mm) j y) a)
          (blockScale (C₀ * Real.sqrt (‖mm‖ * ‖mm⁻¹‖) * X a *
            (3 : ℝ) ^ (γ * max ((jStar : ℝ) - (j : ℝ)) 0)) E))
    (hnormt : BlockMatLoewnerLE E (blockScale (Cn * aspectRatio E *
      Real.sqrt (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t)))
    (hsrcsmall : Cs * aspectRatio E * (‖explicitCanonicalMetric F‖ * ‖(explicitCanonicalMetric F)⁻¹‖) *
      (3 : ℝ) ^ (-(rhoMax d γ * ((t : ℝ) - (jStar : ℝ)))) ≤
      η ^ ((1 : ℝ) / (bigQ d γ : ℝ))) :
    respAllScaleAbs P γ jStar F t a ≤
      (⨆ j ∈ Set.Icc (jStar : ℤ) t,
        (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
          ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j ∩
              HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t,
            blockOpNorm (normalizedFluctuation P
              (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j t y a) ^ bigQ d γ) ^
          ((bigQ d γ : ℝ)⁻¹) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t +
        C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a +
        η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs := by
  let : NeZero d := ⟨by omega⟩
  have hF00 : (0 : ℝ) ≤ ⨆ j ∈ Set.Icc (jStar : ℤ) t,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
        ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j ∩
            HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t,
          blockOpNorm (normalizedFluctuation P
            (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j t y a) ^ bigQ d γ :=
    Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.iSup_nonneg fun y => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hu0 : (0 : ℝ) ≤ (⨆ j ∈ Set.Icc (jStar : ℤ) t,
      (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((t : ℝ) - (j : ℝ))) *
        ⨆ y ∈ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j ∩
            HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) t,
          blockOpNorm (normalizedFluctuation P
            (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) j t y a) ^ bigQ d γ) ^
      ((bigQ d γ : ℝ)⁻¹) := Real.rpow_nonneg hF00 _
  have hv0 : (0 : ℝ) ≤
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t :=
    determinantDrift_nonneg d hd γ hγ P E Ψ Kg Src inferInstance hstat hunit hdag jStar hj
      (explicitCanonicalMetric F) hm t
  have hw0 : (0 : ℝ) ≤ C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a :=
    mul_nonneg (mul_nonneg (div_pos (mul_pos hC₀ hCn) hCs).le
      (Real.rpow_nonneg hη.le _)) hXa.le
  have hx0 : (0 : ℝ) ≤ η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs :=
    div_nonneg (Real.rpow_nonneg hη.le _) hCs.le
  refine respAllScaleAbs_le_of_forall P γ jStar F t a _ (by linarith) ?_
  intro n z hz
  simp only [respMean, respGrid]
  by_cases hn : n ≤ (t - (jStar : ℤ)).toNat
  · have h := h5abs_fluctuation_term_le d hd γ hγ P E Ψ Kg Src hstat hdag jStar hj
      (explicitCanonicalMetric F) hm t ht a n ⟨Nat.zero_le _, hn⟩ z hz
    linarith [h, hw0, hx0]
  · push Not at hn
    have h := h5abs_source_term_le d hd γ hγ P E Ψ Kg Src hstat hdag jStar hj F hm t ht hcube
      C₀ Cn Cs η hC₀ hCn hCs X a hXa hpath hnormt hsrcsmall n hn z hz
    linarith [h, hu0, hv0]

/-- **The two-sided carrier bound** `response_allscale_abs`: `E[A^Q] <= C eta` for the
TWO-SIDED all-scale maximum `A = respAllScaleAbs` (`AdaptedDefs.lean`).

The estimate is the two-sided analogue of the one-sided all-scale maximum bound: it carries
`respAllScaleAbs` in place of `respAllScaleMax`, with the same binders, the same `RawOutput`,
the same `RespSourceSmall`, and the same `∃ Csrc, 0 < Csrc ∧ ∃ C, 0 < C ∧ …` shape.

Constant: `C = 3^Q (2 + 3^Q ((C_0 C_n / C_s)^Q 2^Q + 2 / C_s^Q))`, positive because `C_0`,
`C_n`, `C_s` are.  The extra `2 / C_s^Q` over the one-sided constant is the whole
price of the lower Loewner side (`h5abs_source_term_le`). -/
theorem response_allscale_abs (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (_hS : S.Selects d γ) (Cs : ℝ) (_hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (ε σ : ℝ) (_hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (_hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
        (Cglob Cprof Bresp : ℝ) (_hCglob : 0 ≤ Cglob) (H : ℕ) (P : Measure (CoeffSpace d))
        (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ)
        (F : BlockMat d) (s t : ℤ),
        RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
        ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
          Cprof * σ ^ ((1 - γ) / 8) ≤ η →
          RespSourceSmall d γ Cs η E F jStar s t →
          ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ C * η := by
  obtain ⟨Csrc₁, C₀, hCsrc₁, hC₀, hsrcm⟩ :=
    Source.source_multiplier_and_adapted_bound d _hd γ _hγ
  obtain ⟨Csrc₂, Cn, hCsrc₂, hCn, hrefn⟩ :=
    Annealed.adaptedMean_refBlock_normalization d _hd γ _hγ
  have hKsrc : (0 : ℝ) < C₀ * Cn / Cs := div_pos (mul_pos hC₀ hCn) _hCs
  refine ⟨max Csrc₁ Csrc₂, lt_max_of_lt_left hCsrc₁, ?_⟩
  refine ⟨3 ^ bigQ d γ * (2 + 3 ^ bigQ d γ *
    ((C₀ * Cn / Cs) ^ bigQ d γ * 2 ^ bigQ d γ + 2 / Cs ^ bigQ d γ)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 3 ^ bigQ d γ := pow_pos (by norm_num) _
    have h2 : (0 : ℝ) < (C₀ * Cn / Cs) ^ bigQ d γ := pow_pos hKsrc _
    have h3 : (0 : ℝ) < (2 : ℝ) ^ bigQ d γ := pow_pos (by norm_num) _
    have h4 : (0 : ℝ) < Cs ^ bigQ d γ := pow_pos _hCs _
    have h5 : (0 : ℝ) < 2 / Cs ^ bigQ d γ := div_pos (by norm_num) h4
    have h23 : (0 : ℝ) < (C₀ * Cn / Cs) ^ bigQ d γ * 2 ^ bigQ d γ := mul_pos h2 h3
    have h6 : (0 : ℝ) < 3 ^ bigQ d γ *
        ((C₀ * Cn / Cs) ^ bigQ d γ * 2 ^ bigQ d γ + 2 / Cs ^ bigQ d γ) :=
      mul_pos h1 (by linarith)
    exact mul_pos h1 (by linarith)
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw η hη hprof hsrcsmall
  let : NeZero d := ⟨by omega⟩
  have := raw.prob
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d _hd γ _hγ
  have hQ0 : bigQ d γ ≠ 0 := by omega
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef raw.symm raw.pos
  have hwin := respAllScale_window d _hd γ S ε σ Cglob Cprof (max Csrc₁ Csrc₂) Bresp H P E Ψ Kg
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
  have hfhle : fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t
      ≤ η := by
    have h1 := fluctuationHistory_le_profile d _hd γ _hγ P E Ψ Kg Src raw.prob raw.stat raw.unit
      raw.ell jStar raw.hj (explicitCanonicalMetric F) hm t t hjt le_rfl
    have h2 := h5ra_profile_self_le_eta d _hd γ _hγ S ε σ Cglob Cprof (max Csrc₁ Csrc₂) Bresp H
      P E Ψ Kg Src B jStar F s t raw η hprof
    simp only [respGrid] at h2
    linarith
  obtain ⟨hfint, -⟩ := oneGrid_fluctuation_integrable_dominate d _hd γ _hγ P E Ψ Kg Src raw.stat
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
  have hF0eq : ∫ a, F0 a ∂P =
      fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t := rfl
  have hDr0 : (0 : ℝ) ≤ determinantDrift P γ
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t :=
    determinantDrift_nonneg d _hd γ _hγ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm t
  have hDs0 : (0 : ℝ) ≤ determinantDrift P γ
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s :=
    determinantDrift_nonneg d _hd γ _hγ P E Ψ Kg Src raw.prob raw.stat raw.unit raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm s
  have hfh0 : (0 : ℝ) ≤ fluctuationHistory P γ
      (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t := by
    refine integral_nonneg fun a => ?_
    refine Real.iSup_nonneg fun j => Real.iSup_nonneg fun _ => ?_
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.iSup_nonneg fun z => Real.iSup_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
  have hptt : (0 : ℝ) ≤
      profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t t := by
    refine hfh0.trans ?_
    exact fluctuationHistory_le_profile d _hd γ _hγ P E Ψ Kg Src raw.prob raw.stat raw.unit
      raw.ell jStar raw.hj (explicitCanonicalMetric F) hm t t hjt le_rfl
  have hDr : determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t
      ≤ η := by
    have hmax := le_max_right
      (max (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s s)
        (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar s t))
      (profile P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t t)
    have hraw := raw.prof
    linarith
  have hCsQ : (0 : ℝ) < Cs ^ bigQ d γ := pow_pos _hCs _
  -- the pathwise bound
  have hkey : ∀ᵐ a ∂P, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ≤
      (3 : ℝ) ^ bigQ d γ * F0 a +
        (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
          X a ^ bigQ d γ +
        ((3 : ℝ) ^ bigQ d γ * η ^ bigQ d γ +
          2 * ((3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ) * (η / Cs ^ bigQ d γ)) := by
    filter_upwards [hpath] with a ha
    have hu0 : (0 : ℝ) ≤ F0 a ^ ((bigQ d γ : ℝ)⁻¹) := Real.rpow_nonneg (hF00 a) _
    have hη1 : (0 : ℝ) ≤ η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) := Real.rpow_nonneg hη.1.le _
    have hw0 : (0 : ℝ) ≤ C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a :=
      mul_nonneg (mul_nonneg hKsrc.le hη1) (hX0 a).le
    have hx0 : (0 : ℝ) ≤ η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs := div_nonneg hη1 _hCs.le
    have hMle : respAllScaleAbs P γ jStar F t a ≤
        F0 a ^ ((bigQ d γ : ℝ)⁻¹) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t +
          C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a +
          η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs :=
      h5abs_pathwise_bound d _hd γ _hγ P E Ψ Kg Src raw.stat raw.unit raw.ell jStar raw.hj F hm
        t hjt raw.cube C₀ Cn Cs η hC₀ hCn _hCs hη.1 X a (hX0 a) ha.2 hnormt hsrcsmall.1
    have e1 : (F0 a ^ ((bigQ d γ : ℝ)⁻¹)) ^ bigQ d γ = F0 a :=
      Real.rpow_inv_natCast_pow (hF00 a) hQ0
    have e2 : (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
        jStar t) ^ bigQ d γ ≤ η ^ bigQ d γ := pow_le_pow_left₀ hDr0 hDr _
    have e4 : (η ^ ((1 : ℝ) / (bigQ d γ : ℝ))) ^ bigQ d γ = η := by
      rw [one_div]
      exact Real.rpow_inv_natCast_pow hη.1.le hQ0
    have e3 : (C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a) ^ bigQ d γ =
        (C₀ * Cn / Cs) ^ bigQ d γ * η * X a ^ bigQ d γ := by
      rw [mul_pow, mul_pow, e4]
    have e5 : (η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs) ^ bigQ d γ = η / Cs ^ bigQ d γ := by
      rw [div_pow, e4]
    have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ bigQ d γ := by positivity
    calc respAllScaleAbs P γ jStar F t a ^ bigQ d γ
        ≤ (F0 a ^ ((bigQ d γ : ℝ)⁻¹) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F)) jStar t +
            C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a +
            η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs) ^ bigQ d γ :=
          pow_le_pow_left₀ (respAllScaleAbs_nonneg P γ jStar F t a) hMle _
      _ ≤ (3 : ℝ) ^ bigQ d γ * ((F0 a ^ ((bigQ d γ : ℝ)⁻¹)) ^ bigQ d γ +
            (determinantDrift P γ (Geometry.explicitRoundedGrid jStar (explicitCanonicalMetric F))
              jStar t) ^ bigQ d γ +
            (3 : ℝ) ^ bigQ d γ *
              ((C₀ * Cn / Cs * η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) * X a) ^ bigQ d γ +
                (η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs) ^ bigQ d γ +
                (η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) / Cs) ^ bigQ d γ)) :=
          h5abs_add4_pow_le _ _ _ _ _ hu0 hDr0 hw0 hx0
      _ ≤ (3 : ℝ) ^ bigQ d γ * F0 a +
            (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
              X a ^ bigQ d γ +
            ((3 : ℝ) ^ bigQ d γ * η ^ bigQ d γ +
              2 * ((3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ) * (η / Cs ^ bigQ d γ)) := by
          rw [e1, e3, e5]
          nlinarith [e2, h3]
  -- integrate
  have hi1 : Integrable (fun a => (3 : ℝ) ^ bigQ d γ * F0 a) P := hfint.const_mul _
  have hi2 : Integrable (fun a => (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ *
      ((C₀ * Cn / Cs) ^ bigQ d γ * η) * X a ^ bigQ d γ) P := hXint.const_mul _
  have hi12 : Integrable (fun a => (3 : ℝ) ^ bigQ d γ * F0 a +
      (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
        X a ^ bigQ d γ) P := hi1.add hi2
  have hi3 : Integrable (fun _ : CoeffSpace d =>
      (3 : ℝ) ^ bigQ d γ * η ^ bigQ d γ +
        2 * ((3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ) * (η / Cs ^ bigQ d γ)) P :=
    integrable_const _
  have hgint : Integrable (fun a => (3 : ℝ) ^ bigQ d γ * F0 a +
      (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
        X a ^ bigQ d γ +
      ((3 : ℝ) ^ bigQ d γ * η ^ bigQ d γ +
        2 * ((3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ) * (η / Cs ^ bigQ d γ))) P :=
    hi12.add hi3
  have hgval : ∫ a, ((3 : ℝ) ^ bigQ d γ * F0 a +
      (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
        X a ^ bigQ d γ +
      ((3 : ℝ) ^ bigQ d γ * η ^ bigQ d γ +
        2 * ((3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ) * (η / Cs ^ bigQ d γ))) ∂P =
      (3 : ℝ) ^ bigQ d γ * (∫ a, F0 a ∂P) +
      (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
        (∫ a, X a ^ bigQ d γ ∂P) +
      ((3 : ℝ) ^ bigQ d γ * η ^ bigQ d γ +
        2 * ((3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ) * (η / Cs ^ bigQ d γ)) := by
    rw [integral_add hi12 hi3, integral_add hi1 hi2, integral_const_mul, integral_const_mul]
    simp
  have hmain := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun a => pow_nonneg (respAllScaleAbs_nonneg P γ jStar F t a)
      (bigQ d γ)) hgint hkey
  rw [hgval] at hmain
  refine hmain.trans ?_
  have hF0i : ∫ a, F0 a ∂P ≤ η := by rw [hF0eq]; exact hfhle
  have hetaQ : η ^ bigQ d γ ≤ η := by
    have h1 := pow_le_pow_of_le_one hη.1.le (by linarith [hη.2]) (show 1 ≤ bigQ d γ by omega)
    simpa using h1
  have h3Q : (0 : ℝ) < (3 : ℝ) ^ bigQ d γ := pow_pos (by norm_num) _
  have hKpow : (0 : ℝ) < (C₀ * Cn / Cs) ^ bigQ d γ := pow_pos hKsrc _
  have t1 : (3 : ℝ) ^ bigQ d γ * (∫ a, F0 a ∂P) ≤ (3 : ℝ) ^ bigQ d γ * η :=
    mul_le_mul_of_nonneg_left hF0i h3Q.le
  have t2 : (3 : ℝ) ^ bigQ d γ * η ^ bigQ d γ ≤ (3 : ℝ) ^ bigQ d γ * η :=
    mul_le_mul_of_nonneg_left hetaQ h3Q.le
  have hcoef : (0 : ℝ) ≤ (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ *
      ((C₀ * Cn / Cs) ^ bigQ d γ * η) :=
    mul_nonneg (mul_nonneg h3Q.le h3Q.le) (mul_nonneg hKpow.le hη.1.le)
  have t3 : (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
      (∫ a, X a ^ bigQ d γ ∂P) ≤
      (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
        2 ^ bigQ d γ := mul_le_mul_of_nonneg_left hXmom hcoef
  have hfin : (3 : ℝ) ^ bigQ d γ * η +
      (3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ * ((C₀ * Cn / Cs) ^ bigQ d γ * η) *
        2 ^ bigQ d γ +
      ((3 : ℝ) ^ bigQ d γ * η +
        2 * ((3 : ℝ) ^ bigQ d γ * (3 : ℝ) ^ bigQ d γ) * (η / Cs ^ bigQ d γ)) =
      3 ^ bigQ d γ * (2 + 3 ^ bigQ d γ *
        ((C₀ * Cn / Cs) ^ bigQ d γ * 2 ^ bigQ d γ + 2 / Cs ^ bigQ d γ)) * η := by
    field_simp
    ring
  linarith [t1, t2, t3, hfin]

/-! ## Helpers for the source load bound

These lemmas support `response_source_load_bound`
(`p.response.transfer`).  They carry the whole of the printed argument that is
*downstream* of the per-cell annealed-block estimate: nonnegativity of the source load, the
split of the series at a scale-wise bound, the geometric summation (`3/2 > 0`), and the
passage from a Loewner bound `Ē(z+U_k; b) ≤ c M_0` to the two printed quadratic forms
`|b_{k,z}^{1/2}P|^2` and `|(S_{*,k,z})^{-1/2}Q|^2`.  All are `private`. -/

/-- `matVecMul` kills the zero vector.  Bookkeeping for the coordinate projections `P^±`, `Q^±`
of `Y^±` (`p.response.transfer`). -/
private theorem h7_matVecMul_zero (A : Mat d) : matVecMul A (0 : Vec d) = 0 := by
  funext i; simp [matVecMul]

/-- `vecDot` with a zero left argument.  Bookkeeping for the coordinate projections of `Y^±`. -/
private theorem h7_vecDot_zero_left (y : Vec d) : vecDot (0 : Vec d) y = 0 := by
  simp [vecDot]

/-- The upper-left diagonal block inherits the Loewner order: testing `A ≤ B` on `(x, 0)`
isolates `x · A_{11} x ≤ x · B_{11} x`.  This is the first of the two printed quadratic forms
of the source load (`p.response.transfer`, `|b_{k,z}^{1/2}P|^2 = P · b_{k,z} P`). -/
theorem h7_qform_fst {A B : BlockMat d} (h : BlockMatLoewnerLE A B) (x : Vec d) :
    vecDot x (matVecMul A.upperLeft x) ≤ vecDot x (matVecMul B.upperLeft x) := by
  have h2 := h (x, 0)
  simp only [blockVecDot, blockMatVecMul, h7_matVecMul_zero, add_zero,
    h7_vecDot_zero_left] at h2
  linarith

/-- The lower-right diagonal block inherits the Loewner order: testing `A ≤ B` on `(0, x)`.
This is the second printed quadratic form, `|(S_{*,k,z})^{-1/2}Q|^2 = Q · S_{*,k,z}^{-1} Q`
(`p.response.transfer`). -/
theorem h7_qform_snd {A B : BlockMat d} (h : BlockMatLoewnerLE A B) (x : Vec d) :
    vecDot x (matVecMul A.lowerRight x) ≤ vecDot x (matVecMul B.lowerRight x) := by
  have h2 := h (0, x)
  simp only [blockVecDot, blockMatVecMul, h7_matVecMul_zero, zero_add,
    h7_vecDot_zero_left] at h2
  linarith

/-- A scalar dilation scales the upper-left quadratic form. -/
theorem h7_blockScale_qform_upperLeft (c : ℝ) (B : BlockMat d) (x : Vec d) :
    vecDot x (matVecMul (blockScale c B).upperLeft x) =
      c * vecDot x (matVecMul B.upperLeft x) := by
  simp only [blockScale, matVecMul, vecDot, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A scalar dilation scales the lower-right quadratic form. -/
theorem h7_blockScale_qform_lowerRight (c : ℝ) (B : BlockMat d) (x : Vec d) :
    vecDot x (matVecMul (blockScale c B).lowerRight x) =
      c * vecDot x (matVecMul B.lowerRight x) := by
  simp only [blockScale, matVecMul, vecDot, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `M_0^{1/2}` is a genuine square root of `M_0` on the quadratic forms: this is what turns
the printed mean bound `|M_0^{1/2}Y^±|^2 ≤ C κ_s` of `e.response.load.and.mean`
(`e.response.load.and.mean`, the shape carried by `RespLoadMean`) into a bound on
`Y · M_0 Y`. -/
theorem h7_blockSqrt_qform {A : BlockMat d} (hA : (toFullBlockMat A).PosSemidef)
    (Y : BlockVec d) :
    blockVecDot (blockMatVecMul (blockSqrt A) Y) (blockMatVecMul (blockSqrt A) Y) =
      blockVecDot Y (blockMatVecMul A Y) := by
  obtain ⟨hS, hSS⟩ := matSqrt_spec hA
  have hfull : toFullBlockMat (blockSqrt A) = matSqrt (toFullBlockMat A) := by
    simp only [blockSqrt, toFullBlockMat_ofFullBlockMat]
  have hT : (matSqrt (toFullBlockMat A))ᵀ = matSqrt (toFullBlockMat A) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hS.isHermitian.eq
  rw [← dotProduct_toFullBlockVec, ← dotProduct_toFullBlockVec,
    toFullBlockVec_blockMatVecMul, toFullBlockVec_blockMatVecMul, hfull]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT,
    Matrix.mulVec_mulVec, hSS]
  exact dotProduct_comm _ _

/-- `M_0 = diag(m, m^{-1})` splits the quadratic form into its two printed pieces
(`p.response.transfer`). -/
theorem h7_respM0_qform (F : BlockMat d) (Y : BlockVec d) :
    blockVecDot Y (blockMatVecMul (respM0 F) Y) =
      vecDot Y.1 (matVecMul (explicitCanonicalMetric F) Y.1) +
        vecDot Y.2 (matVecMul (explicitCanonicalMetric F)⁻¹ Y.2) := by
  simp [respM0, blockVecDot, blockMatVecMul, matVecMul, vecDot]

/-- Every summand of `L_s` is a square, so `L_s ≥ 0` — including the junk value `0` of the
`tsum` on a non-summable family.  This is the first half of `RespLoadBound`
(`p.response.transfer`). -/
theorem h7_respSourceLoad_nonneg (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) :
    0 ≤ respSourceLoad P jStar F s b Y := by
  refine tsum_nonneg fun n => ?_
  refine mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ?_
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun z _ => sq_nonneg _)

/-- The weight of `L_s` at scale `k = s - n` is the `n`-th power of `3^{-3/2}`. -/
theorem h7_weight_eq (n : ℕ) :
    (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) = ((3 : ℝ) ^ (-((3 : ℝ) / 2))) ^ n := by
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast]

/-- A finite average is bounded by any pointwise bound, the empty index set included.  This is
the `avg_z` of the source load (`p.response.transfer`). -/
private theorem h7_avg_le {ι : Type*} (T : Finset ι) (f : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ z ∈ T, f z ≤ M) :
    ((T.card : ℝ))⁻¹ * ∑ z ∈ T, f z ≤ M := by
  have hsum : ∑ z ∈ T, f z ≤ (T.card : ℝ) * M := by
    have := Finset.sum_le_card_nsmul T f M h
    simpa [nsmul_eq_mul] using this
  rcases Nat.eq_zero_or_pos T.card with hc | hc
  · have : T = ∅ := Finset.card_eq_zero.mp hc
    simp [this, hM]
  · have hcpos : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast hc
    calc ((T.card : ℝ))⁻¹ * ∑ z ∈ T, f z
        ≤ ((T.card : ℝ))⁻¹ * ((T.card : ℝ) * M) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = M := by field_simp

/-- `(√u + √v)^2 ≤ 4K` whenever `u, v ≤ K` and `0 ≤ K`: the printed square
`(|b^{1/2}P| + |(S_*)^{-1/2}Q|)^2` of `p.response.transfer`, in the form in which the
two diagonal-block bounds are fed to it. -/
private theorem h7_sqrt_add_sq_le {u v K : ℝ} (hK : 0 ≤ K) (hu : u ≤ K) (hv : v ≤ K) :
    (Real.sqrt u + Real.sqrt v) ^ 2 ≤ 4 * K := by
  have h1 : Real.sqrt u ≤ Real.sqrt K := Real.sqrt_le_sqrt hu
  have h2 : Real.sqrt v ≤ Real.sqrt K := Real.sqrt_le_sqrt hv
  have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK
  nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v, Real.sqrt_nonneg K]

/-- **The scale-wise reduction of `L_s`** (`p.response.transfer`).  A bound `K n`
on the two printed quadratic forms of the annealed block at every cell of generation
`k = s - n` bounds the whole source load by the weighted series `∑ 3^{-3n/2} · 4 K n`, as soon
as that series converges.  This is the exact form in which the printed split at `k = j_*`
 is meant to be used: `K n` need not be bounded in `n`, only summable against
the weight.  The same hypotheses make the generation summands of `L_s` summable, so that the
`tsum` defining `L_s` is a genuine sum rather than the junk value of a divergent series; both
conclusions are recorded. -/
theorem h7_respSourceLoad_le_scalewise (P : Measure (CoeffSpace d)) (jStar : ℕ)
    (F : BlockMat d) (s : ℤ) (b : CoeffSpace d → CoeffField d) (Y : BlockVec d) (K : ℕ → ℝ)
    (hK : ∀ n, 0 ≤ K n)
    (hsum : Summable fun n : ℕ => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * K n))
    (hb : ∀ n : ℕ, ∀ z ∈ triadicIndexBox d n,
      vecDot Y.1 (matVecMul (annealedBlockOf P
          (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft Y.1) ≤ K n ∧
      vecDot Y.2 (matVecMul (annealedBlockOf P
          (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight Y.2) ≤ K n) :
    Summable (respSourceLoadSummand P jStar F s b Y) ∧
      respSourceLoad P jStar F s b Y ≤
        ∑' n : ℕ, (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * K n) := by
  set f : ℕ → ℝ := fun n => (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) *
    ((((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ z ∈ triadicIndexBox d n,
        (Real.sqrt (vecDot Y.1 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).upperLeft
              Y.1)) +
          Real.sqrt (vecDot Y.2 (matVecMul
              (annealedBlockOf P (adaptedCellAtCenter (respGrid jStar F) (s - (n : ℤ)) z) b).lowerRight
              Y.2))) ^ 2) with hf
  have hfnn : ∀ n, 0 ≤ f n := by
    intro n
    refine mul_nonneg (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)) ?_
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun z _ => sq_nonneg _)
  have hfle : ∀ n, f n ≤ (3 : ℝ) ^ (-((3 : ℝ) / 2) * (n : ℝ)) * (4 * K n) := by
    intro n
    rw [hf]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine h7_avg_le _ _ _ (by linarith [hK n]) ?_
    intro z hz
    exact h7_sqrt_add_sq_le (hK n) (hb n z hz).1 (hb n z hz).2
  have hfsum : Summable f := hsum.of_nonneg_of_le hfnn hfle
  have hrw : respSourceLoad P jStar F s b Y = ∑' n : ℕ, f n := rfl
  refine ⟨hfsum, ?_⟩
  rw [hrw]
  exact hfsum.tsum_le_tsum hfle hsum

/-! ### The annealed shear bridge at a general adapted cell.

`h7_coarseBlockMatrix_sub_skew_eq_blockCongr` is pathwise and carries the hypothesis
`HasQuadraticMu U a`.  The block below (i) discharges that hypothesis on every adapted cell,
(ii) ports the finite-dimensional matrix-integration lemmas so that a *constant* block
congruence passes through the entrywise integrals of `annealedBlockOf`, and (iii) assembles
`E[A(V; a ∓ g)] = G^t E[A(V; a)] G` for an arbitrary adapted cell `V`, which is
`p.response.transfer` at every subcell rather than only at `U_t`. -/

/-- `HasQuadraticMu` holds on every adapted cell for the qualitative coefficient carrier:
the cell is a bounded open convex domain (affine image of an open cube), the sample has a
pointwise elliptic a.e. representative there, and CG's convex-domain recovery package realizes
the `Mu` infimum; `Mu_congr_of_ae_eq` returns the conclusion to the original representative. -/
theorem h7_hasQuadraticMu_adaptedCellTranslate [NeZero d]
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d) (a : CoeffSpace d) :
    HasQuadraticMu (HighContrast.adaptedCellTranslate q j y) (⇑a.1 : CoeffField d) := by
  obtain ⟨lam, Lam, f, _, _, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq j y a
  have hConv : IsOpenBoundedConvexDomain (HighContrast.adaptedCellTranslate q j y) := by
    rw [Annealed.adaptedCellTranslate_eq_cg_affine]
    exact isOpenBoundedConvexDomain_affine_openCube q hq j y
  let : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCellTranslate q j y)) :=
    hConv.isFiniteMeasure_restrict_volume
  have hWfin : volume (HighContrast.adaptedCellTranslate q j y) ≠ ⊤ :=
    Geometry.volume_adaptedCellTranslate_ne_top q j y
  have hWpos : 0 < volume (HighContrast.adaptedCellTranslate q j y) := by
    rw [Geometry.volume_adaptedCellTranslate]
    have hdet : q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q).mp hq).ne_zero
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr hdet)).ne'
      (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity)) d).ne'
  have hvol : 0 < (volume (HighContrast.adaptedCellTranslate q j y)).toReal :=
    ENNReal.toReal_pos hWpos.ne' hWfin
  obtain ⟨R, ⟨compat⟩⟩ :=
    exists_recovery_compatibility_of_isOpenBoundedConvexDomain hConv hEll hvol
  obtain ⟨Q, hQ⟩ := R.hasQuadraticMuOfIsEllipticFieldOn hEll hvol compat
  exact ⟨Q, fun P => by rw [Mu_congr_of_ae_eq (ae_restrict_of_ae hae) P]; exact hQ P⟩

/-- Entrywise integral of a matrix-valued function. -/
private noncomputable def h7_matIntegral {ι : Type*} [Fintype ι] (P : Measure (CoeffSpace d))
    (f : CoeffSpace d → Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∫ a, f a i j ∂P

private theorem h7_integrable_entries_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    ∀ i j, Integrable (fun a => (c * f a) i j) P := by
  intro i j
  simp only [Matrix.mul_apply]
  exact integrable_finsetSum _ fun k _ => (hf k j).const_mul _

private theorem h7_matIntegral_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    h7_matIntegral P (fun a => f a * c) = h7_matIntegral P f * c := by
  ext i j
  simp only [h7_matIntegral, Matrix.of_apply, Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum _ fun k _ => (hf i k).mul_const (c k j)]
  exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_mul_const _ _

private theorem h7_matIntegral_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Measure (CoeffSpace d)} {f : CoeffSpace d → Matrix ι ι ℝ} (c : Matrix ι ι ℝ)
    (hf : ∀ i j, Integrable (fun a => f a i j) P) :
    h7_matIntegral P (fun a => c * f a) = c * h7_matIntegral P f := by
  ext i j
  simp only [h7_matIntegral, Matrix.of_apply, Matrix.mul_apply]
  rw [MeasureTheory.integral_finsetSum _ fun k _ => (hf k j).const_mul (c i k)]
  exact Finset.sum_congr rfl fun k _ => MeasureTheory.integral_const_mul _ _

private theorem h7_blockMatEntry_eq_toFullBlockMat (A : BlockMat d) (α β : BlockCoord d) :
    blockMatEntry A α β = toFullBlockMat A α β := by
  cases α <;> cases β <;> rfl

/-- **The annealing step.**  A *constant* block congruence passes through the entrywise
integrals of `annealedBlockOf`, so a pathwise congruence identity for the recentred field
becomes the same congruence of the annealed block. -/
theorem h7_annealedBlockOf_eq_blockCongr {P : Measure (CoeffSpace d)} {V : Set (Vec d)}
    (G : BlockMat d) (b : CoeffSpace d → CoeffField d)
    (hint : HasIntegrableCoarseBlock P V)
    (hb : ∀ a : CoeffSpace d, coarseBlockMatrix V (b a) = blockCongr G (coarseBlock V a)) :
    annealedBlockOf P V b = blockCongr G (annealedBlock P V) := by
  have hint' : ∀ α β, Integrable (fun a => toFullBlockMat (coarseBlock V a) α β) P := by
    intro α β
    have h := hint α β
    simpa only [h7_blockMatEntry_eq_toFullBlockMat] using h
  have hfull : (fun a => toFullBlockMat (coarseBlockMatrix V (b a)))
      = fun a => (toFullBlockMat G)ᵀ * toFullBlockMat (coarseBlock V a) * toFullBlockMat G := by
    funext a
    rw [hb a]
    simp only [blockCongr, toFullBlockMat_ofFullBlockMat]
  have hL : annealedBlockOf P V b
      = ofFullBlockMat (h7_matIntegral P
          (fun a => toFullBlockMat (coarseBlockMatrix V (b a)))) := by
    refine blockMat_ext ?_ ?_ ?_ ?_ <;> rfl
  have hR : annealedBlock P V
      = ofFullBlockMat (h7_matIntegral P (fun a => toFullBlockMat (coarseBlock V a))) := by
    refine blockMat_ext ?_ ?_ ?_ ?_ <;> rfl
  rw [hL, hR, hfull,
    h7_matIntegral_mul_right _ (h7_integrable_entries_mul_left _ hint'),
    h7_matIntegral_mul_left _ hint']
  simp only [blockCongr, toFullBlockMat_ofFullBlockMat]

theorem h7_toFullBlockMat_eq_fromBlocks (M : BlockMat d) :
    toFullBlockMat M =
      Matrix.fromBlocks M.upperLeft M.upperRight M.lowerLeft M.lowerRight := by
  ext (i | i) (j | j) <;> rfl

theorem h7_ofFullBlockMat_fromBlocks (A B C D : Mat d) :
    ofFullBlockMat (Matrix.fromBlocks A B C D) = ⟨A, B, C, D⟩ := rfl

theorem h7_matTranspose_neg_skew {g : Mat d} (hg : matTranspose g = -g) :
    matTranspose (-g) = -(-g) := by
  show (-g : Mat d)ᵀ = -(-g)
  rw [Matrix.transpose_neg]
  exact congrArg Neg.neg hg

/-- Congruences compose: `G₂ᵀ (G₁ᵀ A G₁) G₂ = (G₁ G₂)ᵀ A (G₁ G₂)`. -/
theorem h7_blockCongr_blockCongr (G₁ G₂ A : BlockMat d) :
    blockCongr G₂ (blockCongr G₁ A)
      = blockCongr (ofFullBlockMat (toFullBlockMat G₁ * toFullBlockMat G₂)) A := by
  simp only [blockCongr, toFullBlockMat_ofFullBlockMat, Matrix.transpose_mul, Matrix.mul_assoc]

end Homogenization.HighContrast.Multiscale
