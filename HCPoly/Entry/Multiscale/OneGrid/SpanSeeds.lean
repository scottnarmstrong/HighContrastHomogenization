import HCPoly.Entry.Multiscale.OneGrid.SynchronizedPropagation

/-!
# Step 4 — the seeds of the span-`2Q` induction

Group G of the printed proof (`p.fixed.geometry.one.grid.propagation`), first part: the seed moments of
the span-`2Q` induction and the bound `e^{QΔ} - 1 ≤ C 𝒫` on the seed window.

Part of the proof of the statement in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of the group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
source-facing module `HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.
-/

open Homogenization.HighContrast (CoeffSpace blockSub blockTrace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-! ## Group G. Step 4 — an arbitrary advance (`p.fixed.geometry.one.grid.propagation`) -/

/-- The seed moments of the span-`2Q` induction (`p.fixed.geometry.one.grid.propagation`): for
`m+1-2Q ≤ r ≤ m` one has `r ≥ n+1` and `m-r < 2Q`, so the scale-`r` term of `𝒫_q(m;n)`
controls `e^{QΔ^q_{r,m}}E[|V^q_r|_{S_Q}^Q]`. -/
theorem moment_seed_le_profile (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ∀ (metric : Mat d), metric.PosDef →
              ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                ∀ r : ℤ, m + 1 - 2 * (bigQ d γ : ℤ) ≤ r → r ≤ m →
                  Real.exp ((bigQ d γ : ℝ) *
                        logDetLoss P (Geometry.explicitRoundedGrid jStar metric) r m) *
                      (∫ a, absSchattenNorm (bigQ d γ : ℝ)
                        (normalizedFluctuationSelf P
                          (Geometry.explicitRoundedGrid jStar metric) r a) ^ bigQ d γ ∂P) ≤
                    C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m := by
  refine ⟨(3 : ℝ) ^ (bigQ d γ : ℝ), Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric n m hn hnm r hr hrm
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  have hnm' : n ≤ m := by omega
  have hrn : n + 1 ≤ r := by omega
  have hmean := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric n m hn hnm'
  have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
  have hfluc : 0 ≤ fluctuationHistory P γ q jStar n := by
    apply integral_nonneg
    intro a
    apply Real.iSup_nonneg
    intro j
    apply Real.iSup_nonneg
    intro _hj
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro _hz
    exact (bigQ_even d γ).pow_nonneg _
  have hhistory : 0 ≤ history P γ q jStar n := add_nonneg hfluc hmean0
  have hpen := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n m hn hnm').2.2.2.2.2
  have hfirst : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
      (1 + meanPenalty (bigQ d γ) (normalizedMean P q n m)) * history P γ q jStar n :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith only [hpen])) hhistory
  have hmom (j : ℤ) : 0 ≤ ∫ a, absSchattenNorm (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P :=
    integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _
  have hsingle := Finset.single_le_sum (s := Finset.Icc (n + 1) m)
    (f := fun (j : ℤ) => (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
      Real.exp ((bigQ d γ : ℝ) * logDetLoss P q j m) *
      ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P)
    (fun j _ => mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.exp_nonneg _)) (hmom j)) (Finset.mem_Icc.mpr ⟨hrn, hrm⟩)
  have hweighted : (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (r : ℝ))) *
      (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) *
      ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r a) ^ bigQ d γ ∂P) ≤
      profile P γ q jStar n m := by
    unfold profile
    rw [← mul_assoc]
    linarith only [hsingle, hfirst, hmean]
  have hdiff : (m : ℝ) - (r : ℝ) ≤ 2 * (bigQ d γ : ℝ) := by
    have : m - r ≤ 2 * (bigQ d γ : ℤ) := by omega
    exact_mod_cast this
  have hdiff0 : 0 ≤ (m : ℝ) - (r : ℝ) := sub_nonneg.mpr (Int.cast_le.mpr hrm)
  have hweight : 1 ≤ (3 : ℝ) ^ (bigQ d γ : ℝ) *
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (r : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.one_le_rpow (by norm_num)
    have hγ0 := hγ.1
    nlinarith only [hdiff, hdiff0, hγ0, (Nat.cast_nonneg (bigQ d γ) : (0 : ℝ) ≤ (bigQ d γ : ℝ))]
  have hf : 0 ≤ Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) *
      ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r a) ^ bigQ d γ ∂P :=
    mul_nonneg (Real.exp_nonneg _) (hmom r)
  calc
    _ ≤ ((3 : ℝ) ^ (bigQ d γ : ℝ) *
        (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (r : ℝ)))) *
        (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q r a) ^ bigQ d γ ∂P) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight hf
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hweighted (Real.rpow_nonneg (by norm_num) _)

/-- `e^{QΔ^q_{r,m}} - 1 ≤ C 𝒫_q(m;n)` for `r < m` in the seed window (`p.fixed.geometry.one.grid.propagation`), from
`Δ^q_{r,m} ≤ tr(P^q_{r,m} - I_{2d})`, the comparison of `e^{Qt}-1` with `(1+t)^Q-1` and the
scale-`r` term of `ℋ^mean_q(m;n)`.  The premise `𝒫_q(m;n) ≤ 1` is the printed one. -/
theorem exp_logDetLoss_sub_one_le_profile (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
          ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
            ∀ (metric : Mat d), metric.PosDef →
              ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 →
                  ∀ r : ℤ, m + 1 - 2 * (bigQ d γ : ℤ) ≤ r → r < m →
                    Real.exp ((bigQ d γ : ℝ) *
                        logDetLoss P (Geometry.explicitRoundedGrid jStar metric) r m) - 1 ≤
                      C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m := by
  let A : ℝ := (3 : ℝ) ^ (bigQ d γ : ℝ)
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hQ : 0 < bigQ d γ := lt_of_lt_of_le (by norm_num) (bigQ_two_le d hd γ hγ)
  have hQR : (0 : ℝ) < (bigQ d γ : ℝ) := Nat.cast_pos.mpr hQ
  refine ⟨(bigQ d γ : ℝ) * Real.exp ((bigQ d γ : ℝ) * A) * A,
    mul_pos (mul_pos hQR (Real.exp_pos _)) hA, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric n m hn hnm hprof r hr hrm
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric
  have hnm' : n ≤ m := by omega
  have hrn : n ≤ r := by omega
  have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
  have hfluc : 0 ≤ fluctuationHistory P γ q jStar n := by
    apply integral_nonneg
    intro a
    apply Real.iSup_nonneg
    intro j
    apply Real.iSup_nonneg
    intro _hj
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro _hz
    exact (bigQ_even d γ).pow_nonneg _
  have hhistory : 0 ≤ history P γ q jStar n := add_nonneg hfluc hmean0
  have hpen := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n m hn hnm').2.2.2.2.2
  have hfirst : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
      (1 + meanPenalty (bigQ d γ) (normalizedMean P q n m)) * history P γ q jStar n :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith only [hpen])) hhistory
  have hsum : 0 ≤ ∑ j ∈ Finset.Icc (n + 1) m,
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
      Real.exp ((bigQ d γ : ℝ) * logDetLoss P q j m) *
      ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P :=
    Finset.sum_nonneg fun j _ => mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _))
      (integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _)
  have hmean_le : meanHistory P γ q n m ≤ profile P γ q jStar n m := by
    unfold profile
    linarith only [hfirst, hsum]
  have hnonneg (j : ℤ) (hj : j ∈ Finset.Ico n m) :
      0 ≤ meanPenalty (bigQ d γ) (normalizedMean P q j m) :=
    (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric j m (hn.trans (Finset.mem_Ico.mp hj).1)
      (Finset.mem_Ico.mp hj).2.le).2.2.2.2.2
  have hsingle := Finset.single_le_sum (s := Finset.Ico n m)
    (f := fun (j : ℤ) => (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
      meanPenalty (bigQ d γ) (normalizedMean P q j m))
    (fun j hj => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hnonneg j hj))
    (Finset.mem_Ico.mpr ⟨hrn, hrm⟩)
  have hweighted : (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (r : ℝ))) *
      meanPenalty (bigQ d γ) (normalizedMean P q r m) ≤ profile P γ q jStar n m :=
    hsingle.trans hmean_le
  have hdiff : (m : ℝ) - 1 - (r : ℝ) ≤ 2 * (bigQ d γ : ℝ) := by
    have : m - 1 - r ≤ 2 * (bigQ d γ : ℤ) := by omega
    exact_mod_cast this
  have hdiff0 : 0 ≤ (m : ℝ) - 1 - (r : ℝ) := by
    have : (0 : ℤ) ≤ m - 1 - r := by omega
    exact_mod_cast this
  have hweight : 1 ≤ A * (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (r : ℝ))) := by
    dsimp only [A]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    apply Real.one_le_rpow (by norm_num)
    nlinarith only [hdiff, hdiff0, hγ.1, hQR]
  have hpsi0 := hnonneg r (Finset.mem_Ico.mpr ⟨hrn, hrm⟩)
  have hpsi : meanPenalty (bigQ d γ) (normalizedMean P q r m) ≤
      A * profile P γ q jStar n m := by
    calc
      _ ≤ (A * (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (r : ℝ)))) *
          meanPenalty (bigQ d γ) (normalizedMean P q r m) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight hpsi0
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hweighted hA.le
  have hpos := Annealed.normalizedBlock_posDef _ _
    (Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric r)
    (Annealed.adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric m)
  have hp := Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric r m (hn.trans hrn) hrm.le
  let t := blockTrace (blockSub (normalizedMean P q r m) (Book.Ch02.blockIdentity d))
  have ht : 0 ≤ t := Analysis.blockTrace_identity_sub_nonneg _
    ((Analysis.toFullBlockMat_isHermitian_iff _).mp hpos.isHermitian) hp.1
  have htpsi : t ≤ meanPenalty (bigQ d γ) (normalizedMean P q r m) := by
    have hpow := le_self_pow₀ (by linarith only [ht] : 1 ≤ 1 + t) (Nat.ne_of_gt hQ)
    change t ≤ (1 + t) ^ bigQ d γ - 1
    linarith only [hpow]
  have htrace := logDetLoss_le_blockTrace_normalizedMean d hd γ hγ P E Ψ K S hP hstat
    hunit hdag jStar hjStar metric hmetric r m (hn.trans hrn) hrm.le
  have hx0 : 0 ≤ (bigQ d γ : ℝ) * logDetLoss P q r m := mul_nonneg hQR.le hp.2.1
  have hxpsi : (bigQ d γ : ℝ) * logDetLoss P q r m ≤
      (bigQ d γ : ℝ) * meanPenalty (bigQ d γ) (normalizedMean P q r m) :=
    mul_le_mul_of_nonneg_left (htrace.trans htpsi) hQR.le
  have hxA : (bigQ d γ : ℝ) * logDetLoss P q r m ≤ (bigQ d γ : ℝ) * A := by
    have hpa := hpsi.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hprof hA.le)
    exact hxpsi.trans (mul_le_mul_of_nonneg_left hpa hQR.le)
  have hexp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_nonneg x)
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero x)] at h
    nlinarith only [h]
  calc
    _ ≤ ((bigQ d γ : ℝ) * logDetLoss P q r m) *
        Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) := hexp _
    _ ≤ ((bigQ d γ : ℝ) * meanPenalty (bigQ d γ) (normalizedMean P q r m)) *
        Real.exp ((bigQ d γ : ℝ) * A) :=
      mul_le_mul hxpsi (Real.exp_le_exp.mpr hxA) (Real.exp_nonneg _) (mul_nonneg hQR.le hpsi0)
    _ ≤ ((bigQ d γ : ℝ) * (A * profile P γ q jStar n m)) * Real.exp ((bigQ d γ : ℝ) * A) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpsi hQR.le) (Real.exp_nonneg _)
    _ = _ := by ring

end

end Homogenization.HighContrast.Multiscale
