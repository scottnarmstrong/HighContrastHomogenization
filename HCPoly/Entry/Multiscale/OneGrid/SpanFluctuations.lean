import HCPoly.Entry.Multiscale.OneGrid.SpanSeeds

/-!
# Step 4 — the new fluctuations of an arbitrary advance

Group G of the printed proof (`p.fixed.geometry.one.grid.propagation`), second part:
`e.fixed.geometry.new.fluctuations`, the span-`2Q` fluctuation estimate.

Part of the proof of the declaration in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
source-facing module `HCPoly/Entry/OneGridPropagation.lean`; the stronger internal
algebraic and history lemmas omit an unused threshold, and the generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- `e.fixed.geometry.new.fluctuations` (`p.fixed.geometry.one.grid.propagation`): the span-`2Q`
recurrence, the additivity splittings, and the induction in `s` over the new generations. -/
theorem new_fluctuations_span_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K S →
          ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
            ∀ L : ℤ, 1 ≤ L →
              ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
                ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                  ∀ (metric : Mat d), metric.PosDef →
                    ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 →
                        ∑ s ∈ Finset.Icc (m + 1) (m + L),
                            (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - (s : ℝ))) *
                                Real.exp ((bigQ d γ : ℝ) *
                                  logDetLoss P (Geometry.explicitRoundedGrid jStar metric) s (m + L)) *
                              ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                                  (normalizedFluctuationSelf P
                                    (Geometry.explicitRoundedGrid jStar metric) s a) ^ bigQ d γ ∂P ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              Real.exp ((bigQ d γ : ℝ) *
                                logDetLoss P (Geometry.explicitRoundedGrid jStar metric)
                                  m (m + L)) - 1) := by
  obtain ⟨Csrc, hCsrc, hpow⟩ := parent_child_powered d hd γ hγ
  obtain ⟨Cs, hCs, hseed⟩ := moment_seed_le_profile d hd γ hγ
  obtain ⟨Ce, hCe, hexp⟩ := exp_logDetLoss_sub_one_le_profile d hd γ hγ
  have hcoef := span_coefficient_le d hd γ hγ
  have hB0 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * bigQ d γ - 1) *
      (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ := by positivity
  refine ⟨Csrc, hCsrc,
    Cs / 8 + ((2 : ℝ) ^ (2 * bigQ d γ - 1) *
        (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ) * (Ce + 1) +
      8 * ((2 : ℝ) ^ (2 * bigQ d γ - 1) *
        (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ),
    by linarith only [hCs, hB0, mul_nonneg hB0 (by linarith only [hCe] : (0:ℝ) ≤ Ce + 1)], ?_⟩
  set Bc : ℝ := (2 : ℝ) ^ (2 * bigQ d γ - 1) *
      (1 + (d : ℝ) ^ (1 - ((bigQ d γ : ℝ))⁻¹)) ^ bigQ d γ with hBcdef
  clear_value Bc
  intro P E Ψ K S hP hstat hunit hdag h hh L hL jStar hjStar hsrc metric hmetric n m hn hnm hp1
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric with hqdef
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d hd γ hγ
  have hQpos : 0 < bigQ d γ := lt_of_lt_of_le (by norm_num) hQ2
  have hQR : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  have hQposZ : (1 : ℤ) ≤ (bigQ d γ : ℤ) := by exact_mod_cast hQpos
  have hnm0 : n ≤ m := by omega
  have hjm : (jStar : ℤ) ≤ m := hn.trans hnm0
  have hQZ : 2 * (bigQ d γ : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
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
    jStar hjStar metric hmetric n m hn hnm0).2.2.2.2.2
  have hw (t : ℝ) : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * t) := Real.rpow_nonneg (by norm_num) _
  have hmomP : ∀ j : ℤ, 0 ≤ ∫ a, absSchattenNorm (bigQ d γ : ℝ)
      (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P :=
    fun j => integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _
  have hprof0 : 0 ≤ profile P γ q jStar n m := by
    unfold profile
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (mul_nonneg (hw _) (by linarith only [hpen])) hhistory)
        (meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
          jStar hjStar metric hmetric n m hn hnm0)
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw _) (Real.exp_nonneg _))
        (hmomP j)
  set p := profile P γ q jStar n m with hpdef
  clear_value p
  have hp1raw : profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 := by
    rw [← hqdef, ← hpdef]; exact hp1
  have hlogx0 : 0 ≤ logDetLoss P q m (m + L) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      m (m + L) hjm (by omega)
  set x : ℝ := (bigQ d γ : ℝ) * logDetLoss P q m (m + L) with hxdef
  have hx0 : 0 ≤ x := mul_nonneg hQR hlogx0
  clear_value x
  set R : ℝ := p + Real.exp x - 1 with hRdef
  clear_value R
  have hR0 : 0 ≤ R := by
    have hex1 := Real.one_le_exp hx0
    rw [hRdef]; linarith only [hprof0, hex1]
  set C : ℝ := Cs / 8 + Bc * (Ce + 1) + 8 * Bc with hCdef
  clear_value C
  have key : ∀ k : ℕ, ∀ s : ℤ, m < s → s ≤ m + L → s ≤ m + (k : ℤ) →
      Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) *
        (∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P) ≤ C * R := by
    intro k
    induction k with
    | zero => intro s h1 _h2 h3; omega
    | succ k ih =>
      intro s hs1 hs2 hs3
      push_cast at hs3
      set r : ℤ := s - 2 * (bigQ d γ : ℤ) with hrdef
      clear_value r
      have hrs : r + 2 * (bigQ d γ : ℤ) = s := by rw [hrdef]; ring
      have hrjStar : (jStar : ℤ) ≤ r := by omega
      have hh'pos : (1 : ℤ) ≤ 2 * (bigQ d γ : ℤ) := by omega
      set Es : ℝ := Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) with hEsdef
      set Ms : ℝ := ∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P with hMsdef
      set Ers : ℝ := Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r s) with hErsdef
      set Mr : ℝ := ∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q r a) ^ bigQ d γ ∂P with hMrdef
      set Er : ℝ := Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r (m + L)) with hErdef
      set Cf : ℝ := (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
          (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) *
            ((2 * (bigQ d γ : ℤ) : ℤ) : ℝ)) with hCfdef
      clear_value Es Ms Ers Mr Er Cf
      have hpow_inst : Ms ≤ Cf * Ers * Mr + Bc * (Ers - 1) := by
        rw [hMsdef, hCfdef, hErsdef, hMrdef]
        have hraw := hpow P E Ψ K S hP hstat hunit hdag jStar hjStar hsrc metric hmetric
          r (2 * (bigQ d γ : ℤ)) hrjStar hh'pos
        rwa [hrs] at hraw
      have hexps0 : 0 ≤ Es := by rw [hEsdef]; exact Real.exp_nonneg _
      have hstep1 : Es * Ms ≤ Es * (Cf * Ers * Mr + Bc * (Ers - 1)) :=
        mul_le_mul_of_nonneg_left hpow_inst hexps0
      have hadd : logDetLoss P q r s + logDetLoss P q s (m + L) = logDetLoss P q r (m + L) :=
        logDetLoss_add P q r s (m + L)
      have hexp_comb : Es * Ers = Er := by
        rw [hEsdef, hErsdef, hErdef, ← Real.exp_add, ← hadd]
        congr 1
        ring
      have hjs : (jStar : ℤ) ≤ s := by omega
      have hlogDs : 0 ≤ logDetLoss P q s (m + L) :=
        Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
          s (m + L) hjs hs2
      have hexps1 : 1 ≤ Es := by
        rw [hEsdef]; exact Real.one_le_exp (mul_nonneg hQR hlogDs)
      have hexp_sub_le : Es * (Ers - 1) ≤ Er - 1 := by
        have heq : Es * (Ers - 1) = Es * Ers - Es := by ring
        rw [heq, hexp_comb]
        linarith only [hexps1]
      have hcoefle : Cf ≤ 1 / 8 := by
        rw [hCfdef]
        have hexpeq : (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * ((2 * (bigQ d γ : ℤ) : ℤ) : ℝ)) =
            -(d : ℝ) * (bigQ d γ : ℝ) ^ 2 := by push_cast; ring
        rw [hexpeq]
        exact hcoef
      have hMr0 : 0 ≤ Mr := by rw [hMrdef]; exact hmomP r
      have hEr0 : 0 ≤ Er := by rw [hErdef]; exact Real.exp_nonneg _
      have hcommon : Es * Ms ≤ (1 / 8) * (Er * Mr) + Bc * (Er - 1) :=
        calc
          Es * Ms ≤ Es * (Cf * Ers * Mr + Bc * (Ers - 1)) := hstep1
          _ = Cf * Mr * (Es * Ers) + Bc * (Es * (Ers - 1)) := by ring
          _ = Cf * Mr * Er + Bc * (Es * (Ers - 1)) := by rw [hexp_comb]
          _ ≤ Cf * Mr * Er + Bc * (Er - 1) := by
              linarith only [mul_le_mul_of_nonneg_left hexp_sub_le hB0]
          _ ≤ (1 / 8) * Mr * Er + Bc * (Er - 1) := by
              linarith only [mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoefle hMr0) hEr0]
          _ = (1 / 8) * (Er * Mr) + Bc * (Er - 1) := by ring
      by_cases hcaseA : r ≤ m
      · have hseed_inst : Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) * Mr ≤ Cs * p := by
          rw [hMrdef, hpdef]
          exact hseed P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric
            n m hn hnm r (by omega) hcaseA
        have hexpm1_le : Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) - 1 ≤ Ce * p := by
          rcases eq_or_lt_of_le hcaseA with heq | hlt
          · have hzero : logDetLoss P q r m = 0 := by
              rw [heq]; unfold logDetLoss; exact sub_self _
            rw [hzero, mul_zero, Real.exp_zero]
            nlinarith only [mul_nonneg hCe.le hprof0]
          · rw [hpdef]
            exact hexp P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric
              n m hn hnm hp1raw r (by omega) hlt
        have hErm_eq : Er = Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) * Real.exp x := by
          rw [hErdef, hxdef, ← Real.exp_add, ← mul_add, logDetLoss_add P q r m (m + L)]
        have hExpX : Real.exp x * p ≤ R := by
          rw [hRdef]
          linarith only [exp_mul_le_add_exp_sub_one x p hx0 hprof0 hp1]
        have hcaseA_bound : (1 / 8) * (Er * Mr) + Bc * (Er - 1) ≤ C * R := by
          have hErmMr : Er * Mr =
              Real.exp x * (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) * Mr) := by
            rw [hErm_eq]; ring
          have hpart1 : Er * Mr ≤ Real.exp x * (Cs * p) := by
            rw [hErmMr]
            exact mul_le_mul_of_nonneg_left hseed_inst (Real.exp_nonneg _)
          have hpart1' : Er * Mr ≤ Cs * R := by
            have heq3 : Real.exp x * (Cs * p) = Cs * (Real.exp x * p) := by ring
            rw [heq3] at hpart1
            calc Er * Mr ≤ Cs * (Real.exp x * p) := hpart1
              _ ≤ Cs * R := mul_le_mul_of_nonneg_left hExpX hCs.le
          have hpart2 : Er - 1 ≤ (Ce + 1) * R := by
            have heq2 : Er - 1 = Real.exp x *
                (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) - 1) + (Real.exp x - 1) := by
              rw [hErm_eq]; ring
            rw [heq2]
            have hb1 : Real.exp x * (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) - 1) ≤
                Ce * (Real.exp x * p) := by
              have hb0 := mul_le_mul_of_nonneg_left hexpm1_le (Real.exp_nonneg x)
              calc Real.exp x * (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) - 1) ≤
                  Real.exp x * (Ce * p) := hb0
                _ = Ce * (Real.exp x * p) := by ring
            have hb1' : Real.exp x * (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q r m) - 1) ≤
                Ce * R := hb1.trans (mul_le_mul_of_nonneg_left hExpX hCe.le)
            have hb2 : Real.exp x - 1 ≤ R := by rw [hRdef]; linarith only [hprof0]
            linarith only [hb1', hb2]
          have hCbig : Cs / 8 + Bc * (Ce + 1) ≤ C := by
            rw [hCdef]; linarith only [hB0]
          calc (1 / 8) * (Er * Mr) + Bc * (Er - 1) ≤
              (1 / 8) * (Cs * R) + Bc * ((Ce + 1) * R) := by
                have h1 := mul_le_mul_of_nonneg_left hpart1' (by norm_num : (0:ℝ) ≤ 1 / 8)
                have h2 := mul_le_mul_of_nonneg_left hpart2 hB0
                linarith only [h1, h2]
            _ = (Cs / 8 + Bc * (Ce + 1)) * R := by ring
            _ ≤ C * R := mul_le_mul_of_nonneg_right hCbig hR0
        linarith only [hcommon, hcaseA_bound]
      · have hcaseB : m < r := lt_of_not_ge hcaseA
        have hihpre : r ≤ m + L := by omega
        have hihk : r ≤ m + (k : ℤ) := by omega
        have hih : Er * Mr ≤ C * R := by
          rw [hErdef, hMrdef]
          exact ih r hcaseB hihpre hihk
        have hDrm : 0 ≤ logDetLoss P q m r :=
          Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
            m r hjm hcaseB.le
        have hDadd2 : logDetLoss P q m r + logDetLoss P q r (m + L) =
            logDetLoss P q m (m + L) := logDetLoss_add P q m r (m + L)
        have hΔle : logDetLoss P q r (m + L) ≤ logDetLoss P q m (m + L) := by
          linarith only [hDrm, hDadd2]
        have hQΔle : (bigQ d γ : ℝ) * logDetLoss P q r (m + L) ≤
            (bigQ d γ : ℝ) * logDetLoss P q m (m + L) :=
          mul_le_mul_of_nonneg_left hΔle hQR
        have hErlex : Er ≤ Real.exp x := by
          rw [hErdef, hxdef]; exact Real.exp_le_exp.mpr hQΔle
        have hErm1 : Er - 1 ≤ R := by rw [hRdef]; linarith only [hprof0, hErlex]
        have hcaseB_bound : (1 / 8) * (Er * Mr) + Bc * (Er - 1) ≤ C * R := by
          have h1 : (1 / 8) * (Er * Mr) ≤ (1 / 8) * (C * R) :=
            mul_le_mul_of_nonneg_left hih (by norm_num)
          have h2 : Bc * (Er - 1) ≤ Bc * R := mul_le_mul_of_nonneg_left hErm1 hB0
          have hCbound : (1 / 8) * (C * R) + Bc * R ≤ C * R := by
            have hexpand2 : (1 / 8) * (C * R) + Bc * R = ((1 / 8) * C + Bc) * R := by ring
            rw [hexpand2]
            apply mul_le_mul_of_nonneg_right _ hR0
            rw [hCdef]
            linarith only [hCs.le, hB0, mul_nonneg hB0 (by linarith only [hCe] : (0:ℝ) ≤ Ce + 1)]
          linarith only [h1, h2, hCbound]
        linarith only [hcommon, hcaseB_bound]
  have hterm : ∀ s ∈ Finset.Icc (m + 1) (m + L),
      (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - (s : ℝ))) *
          Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P ≤ C * R := by
    intro s hs
    have hs' := Finset.mem_Icc.mp hs
    have hw1 : (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - (s : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith only [hγ.2])
      have hle : (0 : ℤ) ≤ m + L - s := by omega
      exact_mod_cast hle
    have hL0 : (0 : ℤ) ≤ L := by omega
    have htoNat : (L.toNat : ℤ) = L := Int.toNat_of_nonneg hL0
    have hkey := key L.toNat s (by omega) (by omega) (by omega)
    have hMS0 : 0 ≤ Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P :=
      mul_nonneg (Real.exp_nonneg _) (hmomP s)
    calc
      (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - (s : ℝ))) *
          Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ)
          (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P
        = (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - (s : ℝ))) *
            (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) *
              ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P) := by ring
      _ ≤ 1 * (Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) *
              ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P) :=
        mul_le_mul_of_nonneg_right hw1 hMS0
      _ = Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) *
              ∫ a, absSchattenNorm (bigQ d γ : ℝ)
                (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P := one_mul _
      _ ≤ C * R := hkey
  have hcard : ((Finset.Icc (m + 1) (m + L)).card : ℝ) = (L : ℝ) := by
    rw [Int.card_Icc, show m + L + 1 - (m + 1) = L by ring]
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ L)
  calc
    ∑ s ∈ Finset.Icc (m + 1) (m + L),
        (3 : ℝ) ^ (-((1 - γ) / 4) * (((m + L : ℤ) : ℝ) - (s : ℝ))) *
            Real.exp ((bigQ d γ : ℝ) * logDetLoss P q s (m + L)) *
          ∫ a, absSchattenNorm (bigQ d γ : ℝ)
              (normalizedFluctuationSelf P q s a) ^ bigQ d γ ∂P
      ≤ ∑ _s ∈ Finset.Icc (m + 1) (m + L), C * R := Finset.sum_le_sum hterm
    _ = ((Finset.Icc (m + 1) (m + L)).card : ℝ) * (C * R) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (L : ℝ) * (C * R) := by rw [hcard]
    _ = C * (L : ℝ) * R := by ring

end

end Homogenization.HighContrast.Multiscale
