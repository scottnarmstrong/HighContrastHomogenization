/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.InitialData
import HCPoly.Provider.Selection.InitialHitting
/-!
# The initial identity-grid checkpoint
The initial provider law constructs the first identity-grid checkpoint.
-/
namespace Homogenization
namespace HighContrast
namespace Selection
open MeasureTheory
open scoped ENNReal MatrixOrder Matrix
noncomputable section
/-- The exact Phase-1 checkpoint conclusion, bundled with its pre-law hitting
coefficient. -/
structure InitialProviderData {d H Ltr : ℕ}
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr)
    (eta Chit : ℝ) where
  Chit_pos : 0 < Chit
  law : ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ)
      (K : ℝ) (S : CoeffSpace d → ℝ),
    IsProbabilityMeasure P → HCPoly.Frozen.IsStationaryLaw P →
    HCPoly.Frozen.IsUnitRangeLaw P →
    HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
    ∀ jStar M : ℤ, IsCoupledWindow d (initExpQ d g : ℝ) K jStar M →
    ∀ Y : CoeffSpace d → ℝ, IsWindowMultiplier P g E Ψ K Cd jStar M Y →
    ∀ R : ℤ, jStar ≤ R →
      R + ⌈Chit * Real.logb 3 (2 + aspectRatio E)⌉ ≤ M →
      ∃ r0 : ℤ, R ≤ r0 ∧
        (r0 : ℝ) ≤ (R : ℝ) + Chit * Real.logb 3 (2 + aspectRatio E) ∧
        r0 ≤ M ∧
        portableHistory P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
            (1 : Mat d) jStar r0 ≤ ENNReal.ofReal (c.Cinit * eta) ∧
        linearDrift P (initExpRhoDr g) (1 : Mat d) jStar r0 ≤ eta
/-- The explicit bounded-window seed is a fixed power of the aspect-ratio
base. -/
private theorem initialSeedBound_le_mul_rpow {dR h Q CdQ Pi I L : ℝ}
    (hdR : 0 ≤ dR) (hh : 1 ≤ h) (hQ : 1 ≤ Q) (hCdQ : 0 < CdQ)
    (hPi : 1 ≤ Pi) (hI : 0 ≤ I) (hIup : I ≤ 24 * Pi)
    (hLup : L ≤ 2 * h) :
    (1 + L) * (1 + (CdQ * I) ^ Q) * Real.exp (Q * (CdQ * Real.log (2 + Pi))) +
        2 * dR * (Real.exp (CdQ * Real.log (2 + Pi)) - 1) ≤
      ((1 + 2 * h) * (1 + (24 * CdQ) ^ Q) + 2 * dR) *
        (2 + Pi) ^ (Q * (CdQ + 1) + CdQ + 1) := by
  let x : ℝ := 2 + Pi
  let p : ℝ := Q * (CdQ + 1) + CdQ + 1
  have hx3 : 3 ≤ x := by dsimp [x]; linarith only [hPi]
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx3
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 3).trans hx3
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hV0 : 0 ≤ 24 * CdQ := by positivity
  have hCI : CdQ * I ≤ (24 * CdQ) * x := by
    have hPix : Pi ≤ x := by dsimp [x]; norm_num
    have hm := mul_le_mul_of_nonneg_left
      (hIup.trans (mul_le_mul_of_nonneg_left hPix (by norm_num))) hCdQ.le
    nlinarith only [hm]
  have hV : (CdQ * I) ^ Q ≤ (24 * CdQ) ^ Q * x ^ Q := by
    calc
      (CdQ * I) ^ Q ≤ ((24 * CdQ) * x) ^ Q :=
        Real.rpow_le_rpow (mul_nonneg hCdQ.le hI) hCI hQ0
      _ = (24 * CdQ) ^ Q * x ^ Q := Real.mul_rpow hV0 hx0.le
  have hxQ : 1 ≤ x ^ Q := Real.one_le_rpow hx1 hQ0
  have hOneV : 1 + (CdQ * I) ^ Q ≤ (1 + (24 * CdQ) ^ Q) * x ^ Q := by
    nlinarith only [hV, hxQ, Real.rpow_nonneg hV0 Q]
  have hExpQ : Real.exp (Q * (CdQ * Real.log x)) = x ^ (Q * CdQ) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hExp : Real.exp (CdQ * Real.log x) = x ^ CdQ := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hp1 : Q * (CdQ + 1) ≤ p := by dsimp [p]; linarith only [hCdQ]
  have hp2 : CdQ ≤ p := by
    dsimp [p]
    have : 0 ≤ Q * (CdQ + 1) := by positivity
    linarith only [this]
  have hpow1 : x ^ (Q * (CdQ + 1)) ≤ x ^ p :=
    Real.rpow_le_rpow_of_exponent_le hx1 hp1
  have hpow2 : x ^ CdQ ≤ x ^ p := Real.rpow_le_rpow_of_exponent_le hx1 hp2
  have hfirst : (1 + L) * (1 + (CdQ * I) ^ Q) * Real.exp (Q * (CdQ * Real.log x)) ≤
      (1 + 2 * h) * (1 + (24 * CdQ) ^ Q) * x ^ p := by
    rw [hExpQ]
    calc
      _ ≤ (1 + 2 * h) * ((1 + (24 * CdQ) ^ Q) * x ^ Q) * x ^ (Q * CdQ) := by gcongr
      _ = (1 + 2 * h) * (1 + (24 * CdQ) ^ Q) * x ^ (Q * (CdQ + 1)) := by
        have he : x ^ Q * x ^ (Q * CdQ) = x ^ (Q * (CdQ + 1)) := by
          rw [← Real.rpow_add hx0]
          congr 1
          ring
        linear_combination (1 + 2 * h) * (1 + (24 * CdQ) ^ Q) * he
      _ ≤ (1 + 2 * h) * (1 + (24 * CdQ) ^ Q) * x ^ p := by gcongr
  have hsecond : 2 * dR * (Real.exp (CdQ * Real.log x) - 1) ≤ 2 * dR * x ^ p := by
    rw [hExp]
    have : x ^ CdQ - 1 ≤ x ^ p := by
      linarith only [hpow2, Real.rpow_nonneg hx0.le p]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg (by norm_num) hdR)
  dsimp [x, p] at hfirst hsecond ⊢
  nlinarith only [hfirst, hsecond]
/-- The inlined initial datum exists for every positive target.  No additional
source hypothesis is introduced: the law reads only the stationary unit-range
law, coarse ellipticity, and the coupled identity window. -/
theorem exists_initialProviderData {d H Ltr : ℕ} (hd : 2 ≤ d)
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ Chit : ℝ, InitialProviderData c eta Chit := by
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨CdQ, hCdQ, hmomentC, hlogC⟩ := Initialization.exists_initialization_constant d hd g
  have hhR : 1 ≤ (c.h : ℝ) := by exact_mod_cast c.one_le_h
  have hQone : 1 ≤ (initExpQ d g : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (two_le_initExpQ hg))
  let target : ℝ := min eta (c.Cinit * eta / c.CportRaw)
  have htarget : 0 < target := by
    dsimp [target]; exact lt_min heta (div_pos (mul_pos c.Cinit_pos heta) c.CportRaw_pos)
  let Cwork : ℝ := c.Csvc + 2 * (d : ℝ)
  have hCwork : 0 ≤ Cwork := by dsimp [Cwork]; exact add_nonneg c.Csvc_pos.le (by positivity)
  obtain ⟨A, c0, hA, hc0, hamort⟩ := exists_initialLogAmortization
    (lambda := (1 / 4 : ℝ)) (C := Cwork) (Q := (initExpQ d g : ℝ))
    (eta := target) (by norm_num) (by norm_num) (by positivity) htarget
  let Cseed : ℝ := (1 + 2 * (c.h : ℝ)) * (1 + (24 * CdQ) ^ (initExpQ d g : ℝ)) +
    2 * (d : ℝ)
  let pseed : ℝ := (initExpQ d g : ℝ) * (CdQ + 1) + CdQ + 1
  let Aseed : ℝ := Real.log (1 + Cseed) + (pseed + 1) * Real.log 3
  let Dcoef : ℝ := (c.h : ℝ) * CdQ * Real.log 3
  let Ncoef : ℝ := (Aseed + A * Dcoef) / c0 + 1
  let Chit : ℝ := (c.h : ℝ) * (Ncoef + 3)
  have hCseed : 0 < Cseed := by dsimp [Cseed]; positivity
  have hpseed : 0 < pseed := by dsimp [pseed]; positivity
  have hAseed : 0 < Aseed := by
    dsimp [Aseed]
    have := Real.log_pos (by linarith only [hCseed] : 1 < 1 + Cseed)
    positivity
  have hDcoef : 0 < Dcoef := by dsimp [Dcoef]; positivity
  have hNcoef : 1 < Ncoef := by
    dsimp [Ncoef]; have := div_pos (add_pos_of_pos_of_nonneg hAseed (mul_nonneg hA hDcoef.le)) hc0
    linarith only [this]
  have hChit : 0 < Chit := by dsimp [Chit]; positivity
  refine ⟨Chit, ⟨hChit, ?_⟩⟩
  intro P E Ψ K S hprob hstat hunit hdag jStar M hw Y hY R hjR hwindow
  letI : IsProbabilityMeasure P := hprob
  let Pi : ℝ := aspectRatio E
  let base : ℝ := 2 + Pi
  let Lam : ℝ := Real.logb 3 base
  have hPi : 1 ≤ Pi := one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hbase : 3 ≤ base := by dsimp [base, Pi]; linarith only [hPi]
  have hLam : 1 ≤ Lam := by
    dsimp [Lam, base, Pi]
    exact ShortHop.one_le_logb_two_add_aspectRatio hPi
  have hIup : initIdentityConst E ≤ 24 * aspectRatio E :=
    Initialization.initIdentityConst_le (Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag)
  obtain ⟨hqone, hI1, -, hdetBudget, hraw⟩ :=
    Initialization.identity_clause_of_initIdentityConst_le hstat hg hdag hw hY hIup hmomentC hlogC
  have hq : IsRoundedGrid jStar (1 : Mat d) := by
    simpa only [hqone] using
      (Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hw Matrix.PosDef.one)
  have hfin : ∀ j : ℤ, jStar ≤ j → j ≤ M → HasFiniteAdaptedMean P (1 : Mat d) j := by
    intro j hj hM
    simpa only [hqone] using
      (Initialization.finite_and_posDef_of_admissible hw hY Matrix.PosDef.one
        (Initialization.identity_admissible_index hw hj hM)).1
  have hpos : ∀ j : ℤ, jStar ≤ j → j ≤ M →
      Book.Ch02.BlockPosDef (adaptedMean P (1 : Mat d) j) := by
    intro j hj hM
    simpa only [hqone] using
      (Initialization.finite_and_posDef_of_admissible hw hY Matrix.PosDef.one
        (Initialization.identity_admissible_index hw hj hM)).2
  have hmom : ∀ j : ℤ, jStar ≤ j → j ≤ M →
      centeredMoment P (initExpQ d g : ℝ) (1 : Mat d) j ≠ ⊤ := by
    intro j hj hM
    have hm := (hraw j j hj le_rfl hM).2.2.1
    rw [hqone] at hm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm
  obtain ⟨hmean, hdetnn, hrel, hself, hmajor, hservice, hmultiplicity, -, -⟩ :=
    c.portableData.law P hprob hstat hunit jStar (1 : Mat d) hq jStar jStar M
      le_rfl le_rfl (le_trans (by omega : jStar ≤ jStar + 1) hw.2.1) hfin hpos hmom
  have hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ M →
      toFullBlockMat (adaptedMean P (1 : Mat d) t) ≤
        toFullBlockMat (adaptedMean P (1 : Mat d) s) := by
    intro s t hs hst ht
    exact le_of_blockMatLoewnerLE (Recurrence.isSymmetricBlockMat_adaptedMean P _ t)
      (Recurrence.isSymmetricBlockMat_adaptedMean P _ s) (hmean s t hs hst ht)
  obtain ⟨L, m, hLlow, hLhigh, halign⟩ := exists_initialAlignment hjR c.one_le_h
  let Tseed : ℤ := jStar + L
  let Ksteps : ℕ := ⌈Ncoef * Lam⌉₊ + 1
  have hKpos : 1 ≤ Ksteps := by dsimp [Ksteps]; omega
  have hceil := Nat.ceil_lt_add_one (mul_nonneg (le_trans zero_le_one hNcoef.le)
    (le_trans zero_le_one hLam))
  have hKupper : (Ksteps : ℝ) < Ncoef * Lam + 2 := by
    dsimp [Ksteps]
    push_cast
    linarith only [hceil]
  have hspan : ((c.h : ℝ) + (Ksteps : ℝ) * (c.h : ℝ)) ≤ Chit * Lam := by
    dsimp [Chit]
    have hh0 : 0 ≤ (c.h : ℝ) := by exact_mod_cast le_trans zero_le_one c.one_le_h
    have hkh := mul_le_mul_of_nonneg_right hKupper.le hh0
    have hthree : 3 * (c.h : ℝ) ≤ 3 * (c.h : ℝ) * Lam := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hLam (mul_nonneg (by norm_num) hh0)
    nlinarith only [hkh, hthree]
  have hlast : Tseed + ((m + Ksteps : ℕ) : ℤ) * c.h ≤ M := by
    have halign' : Tseed + (m : ℤ) * c.h = R + c.h := by simpa only [Tseed] using halign
    exact initialProgression_last_le halign' hspan (by simpa only [Lam] using hwindow)
  have hseedTop : Tseed ≤ M := by
    have hnonneg : (0 : ℤ) ≤ ((m + Ksteps : ℕ) : ℤ) * c.h :=
      mul_nonneg (by positivity) (by omega)
    exact le_trans (by linarith only [hnonneg]) hlast
  let V : ℝ := (CdQ * initIdentityConst E) ^ (initExpQ d g : ℝ)
  let D : ℝ := CdQ * Real.log base
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hD : 0 ≤ D := by
    dsimp [D, base, Pi]
    exact mul_nonneg hCdQ.le (Real.log_nonneg (by linarith only [hPi]))
  have hbaseHist := portableHistory_lowerEndpoint_le_centeredMoment_rpow
    (P := P) (a := initExpA g) (rhoMax := initExpRhoMax d g)
    (lt_of_lt_of_le zero_lt_one hQone) Matrix.PosDef.one (hpos jStar le_rfl (by omega))
  have hpowMoment : ∀ j : ℤ, jStar ≤ j → j ≤ Tseed →
      centeredMoment P (initExpQ d g : ℝ) (1 : Mat d) j ^ (initExpQ d g : ℝ) ≤
        ENNReal.ofReal V := by
    intro j hj hT
    have hm := (hraw j j hj le_rfl (hT.trans hseedTop)).2.2.1
    rw [hqone] at hm
    refine (ENNReal.rpow_le_rpow hm (le_trans zero_le_one hQone)).trans_eq ?_
    dsimp [V]
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hCdQ.le (le_trans zero_le_one hI1))
      (le_trans zero_le_one hQone)]
  have hseed := initialWork_seed_le (P := P) (Q := (initExpQ d g : ℝ))
    (a := initExpA g) (rhoMax := initExpRhoMax d g) (rhoDr := initExpRhoDr g)
    (V := V) (D := D) hQone (initExpA_pos hg) (initExpRhoDr_pos hg).le hV hD
    hstat hq le_rfl hfin hpos (by omega) le_rfl rfl hseedTop
    (hbaseHist.trans (hpowMoment jStar le_rfl (by omega)))
    (fun j hj hT => hpowMoment j (by omega) hT) (by
      simpa only [D, Tseed, hqone, base, Pi] using
        (hraw jStar (jStar + L) le_rfl (by omega) hseedTop).2.2.2.2.2.2.trans hdetBudget)
  have hseedPoly : initialWork P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
      (initExpRhoDr g) (1 : Mat d) jStar jStar Tseed ≤
      ENNReal.ofReal (Cseed * base ^ pseed) := by
    refine hseed.trans (ENNReal.ofReal_le_ofReal ?_)
    exact initialSeedBound_le_mul_rpow (dR := (d : ℝ)) (h := (c.h : ℝ))
      (Q := (initExpQ d g : ℝ)) (CdQ := CdQ) (Pi := Pi)
      (I := initIdentityConst E) (L := (L : ℝ)) (Nat.cast_nonneg _) (by exact_mod_cast c.one_le_h)
      hQone hCdQ hPi (le_trans zero_le_one hI1)
      (by simpa only [Pi] using hIup) (by exact_mod_cast hLhigh.le)
  let W : ℕ → ℝ≥0∞ := fun n => initialWork P (initExpQ d g : ℝ) (initExpA g)
    (initExpRhoMax d g) (initExpRhoDr g) (1 : Mat d) jStar jStar
      (Tseed + (n : ℤ) * c.h)
  let charge : ℕ → ℝ := fun n => synchCharge P (1 : Mat d) c.h
    (Tseed + (n : ℤ) * c.h)
  have hgridLower (n : ℕ) : jStar + c.h ≤ Tseed + (n : ℤ) * c.h := by
    have hn0 : (0 : ℤ) ≤ (n : ℤ) * c.h := mul_nonneg (by positivity) (by omega)
    dsimp [Tseed]; omega
  have hgridUpper (n : ℕ) (hn : n < m + Ksteps) :
      Tseed + (n : ℤ) * c.h + c.h ≤ M := by
    have hnle : ((n + 1 : ℕ) : ℤ) ≤ ((m + Ksteps : ℕ) : ℤ) := by exact_mod_cast (show n + 1 ≤ m + Ksteps by omega)
    have hmul := mul_le_mul_of_nonneg_right hnle (by omega : (0 : ℤ) ≤ c.h)
    rw [show Tseed + (n : ℤ) * c.h + c.h = Tseed + ((n + 1 : ℕ) : ℤ) * c.h by push_cast; ring]
    exact le_trans (by simpa only [add_comm] using add_le_add_left hmul Tseed) hlast
  have hrec : ∀ n : ℕ, n < m + Ksteps → W (n + 1) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) * Real.exp ((initExpQ d g : ℝ) * charge n)) * W n +
        ENNReal.ofReal (Cwork * (Real.exp ((initExpQ d g : ℝ) * charge n) - 1)) := by
    intro n hn
    have hT := hgridLower n; have hTh := hgridUpper n hn
    have hTM : Tseed + (n : ℤ) * c.h ≤ M := by omega
    have hcharge0 := PortableHistory.synchCharge_nonneg hstat hq le_rfl hfin c.one_le_h (by omega) hTh
    have hD0 : 0 ≤ linearDrift P (initExpRhoDr g) (1 : Mat d) jStar (Tseed + (n : ℤ) * c.h) := ShortHop.linearDrift_nonneg (rhoDr := initExpRhoDr g) (b := jStar)
      (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P (1 : Mat d) _)
        (hpos _ (by omega) hTM))
      (fun r hr1 hr2 => hmono (r - 1) r (show jStar ≤ r - 1 by omega) (show r - 1 ≤ r by omega) (hr2.trans hTM))
    have hprofile := hservice _ hT hTh
    have hdrift := linearDrift_service hQone (initExpRhoDr_pos hg).le hstat hq le_rfl hfin hpos hmono c.one_le_h (by omega) hTh
    have hstep := initialWork_service_of_bounds (d := d) (P := P) (Q := (initExpQ d g : ℝ)) (a := initExpA g) (rhoMax := initExpRhoMax d g) (rhoDr := initExpRhoDr g) (q := (1 : Mat d)) (jStar := jStar) (b := jStar) (h := c.h) (T := Tseed + (n : ℤ) * c.h) (lambda := lambdaPort d (initExpQ d g : ℝ) (initExpA g) c.Crec c.h) (Csvc := c.Csvc) (le_trans zero_le_one hQone) c.service_le c.Csvc_pos.le c.drift_service_le hcharge0 hD0 hprofile hdrift
    simpa only [W, charge, Cwork, Nat.cast_add, Nat.cast_one, one_mul, add_mul, add_assoc] using hstep
  have hcharge0 : ∀ n : ℕ, n < m + Ksteps → 0 ≤ charge n := by
    intro n hn
    exact PortableHistory.synchCharge_nonneg hstat hq le_rfl hfin c.one_le_h
      (by have := hgridLower n; omega) (hgridUpper n hn)
  have hbudget : ∑ n ∈ Finset.range (m + Ksteps), charge n ≤ Dcoef * Lam := by
    have hmK : 1 ≤ m + Ksteps := by omega
    have hmul := hmultiplicity Tseed (m + Ksteps) (by dsimp [Tseed]; omega) hmK hlast
    refine hmul.trans ?_
    have hdet := (hraw (Tseed + 1 - c.h)
      (Tseed + ((m + Ksteps : ℕ) : ℤ) * c.h) (by dsimp [Tseed]; omega) (by have hp := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ ((m + Ksteps : ℕ) : ℤ) by exact_mod_cast hmK) (by omega : (0 : ℤ) ≤ c.h); omega) hlast).2.2.2.2.2.2
    calc
      (c.h : ℝ) * detIncrement P (1 : Mat d) (Tseed + 1 - c.h)
          (Tseed + ((m + Ksteps : ℕ) : ℤ) * c.h)
        ≤ (c.h : ℝ) * (CdQ * Real.log base) := by rw [hqone] at hdet; exact mul_le_mul_of_nonneg_left (hdet.trans (by simpa only [base, Pi] using hdetBudget)) (le_trans zero_le_one hhR)
      _ = Dcoef * Lam := by dsimp [Dcoef, Lam, base, Pi, Real.logb]; field_simp
  have hlog0 : Real.log (1 + Cseed * base ^ pseed) ≤ Aseed * Lam := by
    exact log_one_add_mul_rpow_le_logb hCseed.le hpseed.le hbase
  have hlength : Aseed * Lam + A * (Dcoef * Lam) < (Ksteps : ℝ) * c0 := by
    have hceilLow : Ncoef * Lam ≤ (⌈Ncoef * Lam⌉₊ : ℝ) := Nat.le_ceil _
    dsimp [Ksteps]
    push_cast
    calc
      Aseed * Lam + A * (Dcoef * Lam) = (Aseed + A * Dcoef) * Lam := by ring
      _ < Ncoef * Lam * c0 := by
        have hNbase : Aseed + A * Dcoef < Ncoef * c0 := by dsimp [Ncoef]; rw [add_mul, div_mul_cancel₀ _ hc0.ne', one_mul]; linarith only [hc0]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_lt_mul_of_pos_right hNbase (lt_of_lt_of_le zero_lt_one hLam)
      _ ≤ (⌈Ncoef * Lam⌉₊ : ℝ) * c0 := mul_le_mul_of_nonneg_right hceilLow hc0.le
      _ < ((⌈Ncoef * Lam⌉₊ : ℝ) + 1) * c0 := by nlinarith only [hc0]
  obtain ⟨n, hnK, hhit⟩ := exists_initialWork_le_of_budget
    (W := W) (charge := charge) (lambda := (1 / 4 : ℝ)) (C := Cwork)
    (Q := (initExpQ d g : ℝ)) (eta := target) (x0 := Cseed * base ^ pseed)
    (A := A) (c0 := c0) (D := Dcoef * Lam) (L0 := Aseed * Lam)
    (m := m) (K := Ksteps) (by norm_num) hCwork (le_trans zero_le_one hQone) htarget
    (mul_nonneg hCseed.le (Real.rpow_nonneg (by positivity) _)) (by simpa only [W, Nat.cast_zero, zero_mul, add_zero] using hseedPoly)
    hcharge0 hbudget hrec hlog0 ⟨hA, hc0, hamort⟩ hlength
  let r0 : ℤ := Tseed + ((m + n : ℕ) : ℤ) * c.h
  have hr0M : r0 ≤ M := by dsimp [r0]; exact le_trans (by gcongr <;> omega) hlast
  have hr0R : R ≤ r0 := by
    dsimp [r0]
    have halign' : Tseed + (m : ℤ) * c.h = R + c.h := by simpa only [Tseed] using halign
    calc
      R ≤ R + c.h := by omega
      _ = Tseed + (m : ℤ) * c.h := halign'.symm
      _ ≤ Tseed + (m : ℤ) * c.h + (n : ℤ) * c.h := le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg n) (by omega))
      _ = Tseed + ((m + n : ℕ) : ℤ) * c.h := by push_cast; ring
  have hr0Real : (r0 : ℝ) ≤ (R : ℝ) + Chit * Lam := by
    dsimp [r0]
    push_cast
    have halignR : (Tseed : ℝ) + (m : ℝ) * (c.h : ℝ) = (R : ℝ) + (c.h : ℝ) := by exact_mod_cast (show Tseed + (m : ℤ) * c.h = R + c.h by simpa only [Tseed] using halign)
    rw [add_mul, ← add_assoc, halignR]
    have hn : (n : ℝ) ≤ (Ksteps : ℝ) := by exact_mod_cast hnK.le
    have hmul := mul_le_mul_of_nonneg_right hn (le_trans zero_le_one hhR)
    linarith only [hspan, hmul]
  have hprof : portableProfile P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
      (1 : Mat d) jStar jStar r0 ≤ ENNReal.ofReal target := by
    exact le_trans (le_add_right le_rfl) (by simpa only [W, r0, add_assoc, initialWork_eq] using hhit)
  have hhist := hmajor r0 (by omega) hr0M
  have htargetHist : c.CportRaw * target ≤ c.Cinit * eta := by
    calc
      c.CportRaw * target ≤ c.CportRaw * (c.Cinit * eta / c.CportRaw) :=
        mul_le_mul_of_nonneg_left (by exact min_le_right _ _) c.CportRaw_pos.le
      _ = c.Cinit * eta := by field_simp [c.CportRaw_pos.ne']
  have hhist' : portableHistory P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
      (1 : Mat d) jStar r0 ≤ ENNReal.ofReal (c.Cinit * eta) := by
    refine hhist.trans ((mul_le_mul' le_rfl hprof).trans ?_)
    rw [← ENNReal.ofReal_mul c.CportRaw_pos.le]
    exact ENNReal.ofReal_le_ofReal htargetHist
  have hdrift : linearDrift P (initExpRhoDr g) (1 : Mat d) jStar r0 ≤ eta := by
    have hof : ENNReal.ofReal (linearDrift P (initExpRhoDr g) (1 : Mat d) jStar r0) ≤
        ENNReal.ofReal target := le_trans (le_add_left le_rfl) (by simpa only [W, r0, add_assoc, initialWork_eq] using hhit)
    exact ((ENNReal.ofReal_le_ofReal_iff htarget.le).mp hof).trans (min_le_left _ _)
  exact ⟨r0, hr0R, by simpa only [Lam] using hr0Real, hr0M, hhist', hdrift⟩
end
end Selection
end HighContrast
end Homogenization
