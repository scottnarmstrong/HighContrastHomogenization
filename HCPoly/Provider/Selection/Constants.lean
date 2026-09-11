/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Frozen.RandomSourceBridgeShortHop
import HCPoly.Provider.Selection.ChoiceData

/-!
# The ordered pre-law constants of the global selection

The recurrence and portable-history constants are obtained first, followed by
profile tolerances, terminal tolerances, bridge tolerance, short-hop data, and
the remaining startup tolerances.  Every choice is made before the law.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

noncomputable section

/-! ## Ordered existence -/

/-- The full pre-law package exists once the rounded-hop constant and the two
transport constants have been supplied.  The rounded-hop conclusion is inlined
exactly as in the proved short-hop proposition. -/
theorem exists_selConstants (d : ℕ) (hd : 2 ≤ d) {g : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) {epsCal etaDr etaProfBar deltaDetBar : ℝ}
    (hepsCal : 0 < epsCal) (hetaDr : 0 < etaDr) (hetaProf : 0 < etaProfBar)
    (hdeltaDet : 0 < deltaDetBar) (H : ℕ) (hH : 4 ≤ H)
    (Cd : ℝ) (hCd : 1 ≤ Cd) (chop : ℝ) (hchop : 0 < chop)
    (Khop : ℝ) (hKhop : 1 ≤ Khop)
    (hhop : ∀ l : ℤ, (kZero d : ℤ) ≤ l → ∀ m₀ m₁ : Mat d,
      m₀.PosDef → m₁.PosDef → projDist m₀ m₁ ≤ chop →
      gridRatio (roundedGrid l m₀) (roundedGrid l m₁) ≤ Khop)
    (Ltr : ℕ) (Ctr : ℝ)
    (transportData : TransportProviderData d g (initExpQ d g) (initExpRhoMax d g)
      (initExpA g) Khop Ctr Ltr)
    (Cinit : ℝ) (hCinit : 0 < Cinit) :
    ∃ c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr,
      c.chop = chop := by
  have hCtr : 0 < Ctr := transportData.Ctr_pos
  have hLtr : 1 ≤ Ltr := transportData.one_le_Ltr
  obtain ⟨Crec, hCrec, hrec⟩ := HCPoly.Frozen.fixed_grid_recurrence d hd
    (initExpQ d g) (two_le_initExpQ hg) (initExpQ_even d g)
  obtain ⟨h, hh, hlam, hdrift⟩ := exists_serviceLength d hd hg hCrec
  obtain ⟨C0, Csvc, hC0, hCsvc, AL, hAL, hportable⟩ :=
    HCPoly.Frozen.portable_history d hd
    (initExpQ d g) (two_le_initExpQ hg) (initExpQ_even d g)
    (initExpA g) (initExpRhoMax d g) (initExpA_pos hg)
    (lt_of_le_of_lt hg.1 (initExpRhoMax_gt hg))
    (initExp_portable_admissible hg) Crec hCrec hrec h hh hlam
  let Cport : ℝ := max 1 C0
  have hCport1 : 1 ≤ Cport := le_max_left _ _
  have hC0port : C0 ≤ Cport := le_max_right _ _
  have hCport : 0 < Cport := lt_of_lt_of_le zero_lt_one hCport1
  have hH1 : (1 : ℤ) ≤ (H : ℤ) := by exact_mod_cast (le_trans (by norm_num) hH)
  have hAH : 0 < AL (H : ℤ) := hAL (H : ℤ) hH1
  let epsSt : ℝ := etaProfBar / 2
  let etaOut : ℝ := min (etaProfBar / 2) (epsSt / (2 * Cport))
  let etaIn : ℝ := min (etaProfBar / 2) (etaOut / (8 * AL (H : ℤ)))
  have hepsSt : 0 < epsSt := by dsimp [epsSt]; positivity
  have hetaOut : 0 < etaOut := by dsimp [etaOut]; positivity
  have hetaIn : 0 < etaIn := by dsimp [etaIn]; positivity
  have hetaInCap : etaIn ≤ etaProfBar / 2 := by
    dsimp [etaIn]
    exact min_le_left _ _
  have hetaOutCap : etaOut ≤ etaProfBar / 2 := by
    dsimp [etaOut]
    exact min_le_left _ _
  have hcaps : max (max etaIn etaOut) epsSt ≤ etaProfBar := by
    apply max_le
    · apply max_le
      · exact hetaInCap.trans (by linarith only [hetaProf])
      · exact hetaOutCap.trans (by linarith only [hetaProf])
    · dsimp [epsSt]
      linarith only [hetaProf]
  have hportableShare : Cport * etaOut ≤ epsSt := by
    have hout : etaOut ≤ epsSt / (2 * Cport) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hout hCport.le
    have heq : Cport * (epsSt / (2 * Cport)) = epsSt / 2 := by field_simp
    rw [heq] at hmul
    linarith only [hmul, hepsSt]
  have hstartupShare : AL (H : ℤ) * etaIn ≤ etaOut / 4 := by
    have hin : etaIn ≤ etaOut / (8 * AL (H : ℤ)) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hin hAH.le
    have heq : AL (H : ℤ) * (etaOut / (8 * AL (H : ℤ))) = etaOut / 8 := by
      field_simp
    rw [heq] at hmul
    linarith only [hmul, hetaOut]
  let driftFactor : ℝ := 1 + (3 : ℝ) ^ (-initExpRhoDr g * (H : ℝ))
  have hdriftFactor : 0 < driftFactor := by dsimp [driftFactor]; positivity
  let etaNew : ℝ := min (1 / 2) (etaDr / (2 * driftFactor))
  have hetaNew : 0 < etaNew := by dsimp [etaNew]; positivity
  have hetaNew1 : etaNew < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hnewDrift : driftFactor * etaNew < etaDr := by
    have hle : etaNew ≤ etaDr / (2 * driftFactor) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hle hdriftFactor.le
    have heq : driftFactor * (etaDr / (2 * driftFactor)) = etaDr / 2 := by field_simp
    rw [heq] at hmul
    linarith only [hmul, hetaDr]
  obtain ⟨deltaTerm, hdeltaTerm, hdeltaCal, hdeltaTermDet, hterminalProfile,
      hterminalDrift⟩ := exists_deltaTerm d H (g := g) (AH := AL (H : ℤ))
    (by simpa [driftFactor] using hnewDrift) hetaOut hepsCal hdeltaDet
  let Cphi : ℝ := max 1 Csvc
  let Cdir : ℝ := max ((initExpQ d g : ℝ) * (d : ℝ))
    (max (Cphi * (initExpQ d g : ℝ) * (d : ℝ)) ((d : ℝ) / Real.log 2))
  let CdetBar : ℝ := 4 * max Cdir (max ((d : ℝ) / 2) 1)
  have hCdet : 0 < CdetBar := by
    dsimp [CdetBar]
    have : (1 : ℝ) ≤ max Cdir (max ((d : ℝ) / 2) 1) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    positivity
  have hlogDelta : 0 < Real.log (1 + deltaTerm) :=
    Real.log_pos (by linarith only [hdeltaTerm])
  let Fpr : ℝ → ℝ := fun x => 1 / 2 * Real.log ((1 + x) / (1 - x))
  let Ftr : ℝ → ℝ := fun x => Ctr * x
  let Fbridge : ℝ → ℝ := fun x =>
    2 * CdetBar * ((h : ℝ) + 2) * Real.log (1 + x)
  let Fterminal : ℝ → ℝ := fun x => Fpr x + Fbridge x
  have hFpr : ContinuousAt Fpr 0 := by
    dsimp [Fpr]
    have hnum : ContinuousAt (fun x : ℝ => 1 + x) 0 :=
      continuousAt_const.add continuousAt_id
    have hden : ContinuousAt (fun x : ℝ => 1 - x) 0 :=
      continuousAt_const.sub continuousAt_id
    have hquot : ContinuousAt (fun x : ℝ => (1 + x) / (1 - x)) 0 :=
      hnum.div hden (by norm_num)
    exact continuousAt_const.mul (hquot.log (by norm_num))
  have hFtr : ContinuousAt Ftr 0 := by dsimp [Ftr]; fun_prop
  have hFbridge : ContinuousAt Fbridge 0 := by
    dsimp [Fbridge]
    have hlog : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 0 :=
      (continuousAt_const.add continuousAt_id).log (by norm_num)
    exact continuousAt_const.mul hlog
  have hFterminal : ContinuousAt Fterminal 0 := hFpr.add hFbridge
  obtain ⟨rPr, hrPr, hPr⟩ := exists_right_radius (A := chop / 4) hFpr
    (by dsimp [Fpr]; norm_num; linarith only [hchop])
  obtain ⟨rTr, hrTr, hTr⟩ := exists_right_radius (A := etaIn / 3) hFtr
    (by dsimp [Ftr]; linarith only [hetaIn])
  obtain ⟨rBridge, hrBridge, hBridge⟩ := exists_right_radius
    (A := min chop (Real.log (1 + deltaTerm)) / 4) hFbridge
    (by
      have hmin : 0 < min chop (Real.log (1 + deltaTerm)) := lt_min hchop hlogDelta
      have hquarter : 0 < min chop (Real.log (1 + deltaTerm)) / 4 :=
        div_pos hmin (by norm_num)
      simpa [Fbridge] using hquarter)
  obtain ⟨rTerminal, hrTerminal, hTerminal⟩ := exists_right_radius
    (A := CdetBar * Real.log (1 + deltaTerm) / 2) hFterminal
    (by dsimp [Fterminal, Fpr, Fbridge]; norm_num; positivity)
  let etaX : ℝ := min (1 / 4) (min epsCal (min rPr (min rTr (min rBridge rTerminal))))
  have hetaX : 0 < etaX := by dsimp [etaX]; positivity
  have hetaXquarter : etaX ≤ 1 / 4 := min_le_left _ _
  have hetaXcal : etaX ≤ epsCal := le_trans (min_le_right _ _) (min_le_left _ _)
  have hetaXPr : etaX ≤ rPr :=
    le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _)
  have hetaXTr : etaX ≤ rTr :=
    le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (min_le_right _ _)) (min_le_left _ _)
  have hetaXBridge : etaX ≤ rBridge :=
    le_trans (le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (min_le_right _ _)) (min_le_right _ _)) (min_le_left _ _)
  have hetaXTerminal : etaX ≤ rTerminal :=
    le_trans (le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _))
      (min_le_right _ _)) (min_le_right _ _)) (min_le_right _ _)
  have hprojective := hPr etaX hetaX.le hetaXPr
  have htransport := hTr etaX hetaX.le hetaXTr
  have hbridge := hBridge etaX hetaX.le hetaXBridge
  have hterminal := hTerminal etaX hetaX.le hetaXTerminal
  let Lcommon : ℕ := max Ltr (⌈4 * (initExpQ d g : ℝ) * chop /
    (initExpA g * Real.log 3)⌉₊ + 1)
  obtain ⟨l0, hl0, tau0, htau0, delta0, hdelta0, etaPre0, hetaPre0,
      Bshort, hBshort, hshortLog, hshortGeom, hrhoBuffer, hBshortCutoff,
      hthreshold0, hshortLaw0⟩ := HCPoly.Frozen.random_source_bridge_short_hop d hd g hg
    chop hchop etaNew hetaNew hetaNew1 etaX hetaX hetaXquarter Lcommon Khop hKhop hhop
    Ltr hLtr Ctr hCtr Cd hCd
  have haLog : 0 < initExpA g * Real.log 3 :=
    mul_pos (initExpA_pos hg) (Real.log_pos (by norm_num))
  have hceilL : ⌈4 * (initExpQ d g : ℝ) * chop /
      (initExpA g * Real.log 3)⌉₊ + 1 ≤ l0 := by
    have hcut : ⌈4 * (initExpQ d g : ℝ) * chop /
        (initExpA g * Real.log 3)⌉₊ + 1 ≤ Lcommon := by
      dsimp [Lcommon]
      exact le_max_right _ _
    exact hcut.trans ((le_max_left _ _).trans hl0)
  have haBuffer : 2 * (initExpQ d g : ℝ) * chop <
      initExpA g * (l0 : ℝ) * Real.log 3 / 2 := by
    have hceilReal : 4 * (initExpQ d g : ℝ) * chop /
        (initExpA g * Real.log 3) ≤
        (⌈4 * (initExpQ d g : ℝ) * chop /
          (initExpA g * Real.log 3)⌉₊ : ℝ) := Nat.le_ceil _
    have hcast : (⌈4 * (initExpQ d g : ℝ) * chop /
          (initExpA g * Real.log 3)⌉₊ : ℝ) + 1 ≤ (l0 : ℝ) := by
      exact_mod_cast hceilL
    have hlt : 4 * (initExpQ d g : ℝ) * chop /
        (initExpA g * Real.log 3) < (l0 : ℝ) := by
      linarith only [hceilReal, hcast]
    rw [div_lt_iff₀ haLog] at hlt
    nlinarith only [hlt]
  let etaHop : ℝ := min 1
    (etaIn / (6 * Ctr * (3 : ℝ) ^ (2 * initExpA g * (l0 : ℝ))))
  have hetaHop : 0 < etaHop := by dsimp [etaHop]; positivity
  have hetaHop1 : etaHop ≤ 1 := min_le_left _ _
  have hhopShare : Ctr * (3 : ℝ) ^ (2 * initExpA g * (l0 : ℝ)) * etaHop ≤
      etaIn / 3 := by
    have hcoef : 0 < Ctr * (3 : ℝ) ^ (2 * initExpA g * (l0 : ℝ)) := by positivity
    have hle := min_le_right (1 : ℝ)
      (etaIn / (6 * Ctr * (3 : ℝ) ^ (2 * initExpA g * (l0 : ℝ))))
    have hmul := mul_le_mul_of_nonneg_left hle hcoef.le
    have heq : (Ctr * (3 : ℝ) ^ (2 * initExpA g * (l0 : ℝ))) *
        (etaIn / (6 * Ctr * (3 : ℝ) ^ (2 * initExpA g * (l0 : ℝ)))) = etaIn / 6 := by
      field_simp
    rw [heq] at hmul
    have hbound : Ctr * (3 : ℝ) ^ (2 * initExpA g * (l0 : ℝ)) * etaHop ≤
        etaIn / 6 := by simpa [etaHop] using hmul
    linarith only [hbound, hetaIn]
  have h2l0 : (1 : ℤ) ≤ 2 * (l0 : ℤ) := by
    have : 1 ≤ l0 := le_trans hLtr (le_trans (le_max_right _ _) hl0)
    omega
  have hA2 : 0 < AL (2 * (l0 : ℤ)) := hAL _ h2l0
  let Fshort : ℝ → ℝ := fun x => AL (2 * (l0 : ℤ)) *
    (Real.exp ((initExpQ d g : ℝ) * (d : ℝ) * Real.log (1 + x)) - 1)
  obtain ⟨rShort, hrShort, hShort⟩ := exists_right_radius
    (f := Fshort) (A := etaHop / 4) (by
      dsimp [Fshort]
      have hlog : ContinuousAt (fun x : ℝ => Real.log (1 + x)) 0 :=
        (continuousAt_const.add continuousAt_id).log (by norm_num)
      have hinner : ContinuousAt
          (fun x : ℝ => (initExpQ d g : ℝ) * (d : ℝ) * Real.log (1 + x)) 0 :=
        continuousAt_const.mul hlog
      have hexp : ContinuousAt
          (fun x : ℝ => Real.exp ((initExpQ d g : ℝ) * (d : ℝ) *
            Real.log (1 + x))) 0 := Real.continuous_exp.continuousAt.comp' hinner
      exact continuousAt_const.mul (hexp.sub continuousAt_const))
    (by dsimp [Fshort]; norm_num; linarith only [hetaHop])
  let deltaShort : ℝ := min delta0 rShort
  let etaPre : ℝ := min etaPre0 (etaNew / 2)
  have hdeltaShort : 0 < deltaShort := by dsimp [deltaShort]; positivity
  have hetaPre : 0 < etaPre := by dsimp [etaPre]; positivity
  have hetaPreNew : etaPre ≤ etaNew / 2 := min_le_right _ _
  have hshortDet : Fshort deltaShort ≤ etaHop / 4 :=
    hShort deltaShort hdeltaShort.le (le_trans (min_le_right _ _) le_rfl)
  let etaReady : ℝ := min 1 (etaHop / (8 * AL (2 * (l0 : ℤ))))
  have hetaReady : 0 < etaReady := by dsimp [etaReady]; positivity
  have hetaReady1 : etaReady ≤ 1 := min_le_left _ _
  have hreadyShare : AL (2 * (l0 : ℤ)) * etaReady ≤ etaHop / 4 := by
    have hle : etaReady ≤ etaHop / (8 * AL (2 * (l0 : ℤ))) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hle hA2.le
    have heq : AL (2 * (l0 : ℤ)) * (etaHop / (8 * AL (2 * (l0 : ℤ)))) =
        etaHop / 8 := by field_simp
    rw [heq] at hmul
    linarith only [hmul, hetaHop]
  let FrPow : ℝ → ℝ := fun x => (1 + x) ^ d
  let FrDrift : ℝ → ℝ := fun x => 2 * (d : ℝ) * ((1 + x) ^ d - 1)
  obtain ⟨rPow, hrPow, hPow⟩ := exists_right_radius
    (f := FrPow) (A := 2) (by dsimp [FrPow]; fun_prop) (by dsimp [FrPow]; norm_num)
  obtain ⟨rDrift, hrDrift, hDrift⟩ := exists_right_radius
    (f := FrDrift) (A := etaPre / 4) (by dsimp [FrDrift]; fun_prop)
    (by dsimp [FrDrift]; norm_num; linarith only [hetaPre])
  let rDelta : ℝ := min rPow rDrift
  let rDr : ℝ := 1 + rDelta
  have hrDelta : 0 < rDelta := by dsimp [rDelta]; positivity
  have hrDr : 1 < rDr := by dsimp [rDr]; linarith only [hrDelta]
  have hrPowLe : rDr ^ d ≤ 2 := by
    exact hPow rDelta hrDelta.le (min_le_left _ _)
  have hrDriftLe : 2 * (d : ℝ) * (rDr ^ d - 1) ≤ etaPre / 4 := by
    exact hDrift rDelta hrDelta.le (min_le_right _ _)
  let tauTr : ℝ := etaIn / 6
  have htauTr : 0 < tauTr := by dsimp [tauTr]; positivity
  have htauTrLe : tauTr ≤ etaIn / 3 := by dsimp [tauTr]; linarith only [hetaIn]
  let etaInit : ℝ := min (etaNew / 2) (min etaIn etaReady / (2 * Cinit))
  have hetaInit : 0 < etaInit := by dsimp [etaInit]; positivity
  have hetaInitNew : etaInit ≤ etaNew :=
    (min_le_left _ _).trans (by linarith only [hetaNew])
  have hinitShare : Cinit * etaInit ≤ min etaIn etaReady := by
    have hle : etaInit ≤ min etaIn etaReady / (2 * Cinit) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hle hCinit.le
    have heq : Cinit * (min etaIn etaReady / (2 * Cinit)) = min etaIn etaReady / 2 := by
      field_simp
    rw [heq] at hmul
    have hmin0 : 0 ≤ min etaIn etaReady := le_of_lt (lt_min hetaIn hetaReady)
    linarith only [hmul, hmin0]
  let bHop : ℕ := ⌈Real.logb 2 (max 1 (etaNew / etaPre))⌉₊
  have hthreshold : ∀ b delta R₁ R₂ R₃ : ℝ,
      0 ≤ b → b ≤ etaPre → 0 ≤ delta → delta ≤ deltaShort →
      0 ≤ R₁ → R₁ ≤ tau0 → 0 ≤ R₂ → R₂ ≤ tau0 →
      0 ≤ R₃ → R₃ ≤ tau0 →
      shortBridgeErr d Ctr Khop (initExpRhoDr g) (l0 : ℤ) b delta R₁ R₂ ≤ etaX ∧
        shortNewDrift d Ctr Khop (initExpRhoDr g) (l0 : ℤ) b delta R₂ R₃ ≤ etaNew := by
    intro b delta R₁ R₂ R₃ hb hbpre hdelta hdshort hR₁ hR₁t hR₂ hR₂t hR₃ hR₃t
    exact hthreshold0 b delta R₁ R₂ R₃ hb
      (hbpre.trans (min_le_left _ _)) hdelta
      (hdshort.trans (min_le_left _ _)) hR₁ hR₁t hR₂ hR₂t hR₃ hR₃t
  let rawShortData : ShortHopProviderData d g chop etaNew etaX Khop Ctr Cd l0
      tau0 delta0 etaPre0 Bshort := ⟨hshortLaw0⟩
  have hshortData : ShortHopProviderData d g chop etaNew etaX Khop Ctr Cd l0
      tau0 deltaShort etaPre Bshort :=
    rawShortData.shrink hd hBshort (min_le_left _ _) (min_le_left _ _)
  refine ⟨{
    chop := chop, chop_pos := hchop, Crec := Crec, Crec_pos := hCrec,
    h := h, one_le_h := hh, service_le := hlam, drift_service_le := hdrift,
    CportRaw := C0, Cport := Cport, Csvc := Csvc, CportRaw_pos := hC0,
    Cport_eq := rfl, one_le_Cport := hCport1, CportRaw_le := hC0port,
    Csvc_pos := hCsvc, AL := AL, AL_pos := hAL, transportData := transportData,
    portableData := ⟨hportable⟩,
    etaOut := etaOut, epsSt := epsSt, etaIn := etaIn, etaOut_pos := hetaOut,
    epsSt_pos := hepsSt, etaIn_pos := hetaIn, profile_caps := hcaps,
    portable_share := hportableShare, startup_share := hstartupShare,
    etaNew := etaNew, etaNew_pos := hetaNew, etaNew_lt_one := hetaNew1,
    new_drift := by simpa [driftFactor] using hnewDrift,
    deltaTerm := deltaTerm, deltaTerm_pos := hdeltaTerm,
    deltaTerm_le_epsCal := hdeltaCal, deltaTerm_le_deltaDetBar := hdeltaTermDet,
    terminal_profile := hterminalProfile, terminal_drift := hterminalDrift,
    Cphi := Cphi, Cdir := Cdir, CdetBar := CdetBar, Cphi_eq := rfl, Cdir_eq := rfl,
    CdetBar_pos := hCdet, CdetBar_lower := le_rfl,
    etaX := etaX, etaX_pos := hetaX, etaX_le_quarter := hetaXquarter,
    etaX_le_epsCal := hetaXcal, projective_tolerance := hprojective,
    transport_tolerance := htransport, bridge_feedback := hbridge,
    terminal_feedback := hterminal, Lcommon := Lcommon, l0 := l0,
    Lcommon_eq := rfl, l0_lower := hl0, rho_buffer := hrhoBuffer,
    a_buffer := haBuffer, tauSrc := tau0, deltaShort := deltaShort,
    etaPre := etaPre, Bshort := Bshort, tauSrc_pos := htau0,
    deltaShort_pos := hdeltaShort, etaPre_pos := hetaPre, Bshort_pos := hBshort,
    short_log := hshortLog, short_geom := hshortGeom,
    Bshort_cutoff := hBshortCutoff, etaPre_le := hetaPreNew,
    short_thresholds := hthreshold, shortHopData := hshortData,
    etaHop := etaHop, etaReady := etaReady,
    etaHop_pos := hetaHop, etaHop_le_one := hetaHop1, etaReady_pos := hetaReady,
    etaReady_le_one := hetaReady1, hop_transport_share := hhopShare,
    ready_share := hreadyShare, short_det_share := by simpa [Fshort] using hshortDet,
    rDr := rDr, tauTr := tauTr, Cinit := Cinit, etaInit := etaInit,
    one_lt_rDr := hrDr, rDr_pow_le := hrPowLe, rDr_drift := hrDriftLe,
    tauTr_pos := htauTr, tauTr_le := htauTrLe, Cinit_pos := hCinit,
    etaInit_pos := hetaInit, init_share := hinitShare, etaInit_le := hetaInitNew,
    bHop := bHop, bHop_eq := rfl }, rfl⟩

end


end Selection
end HighContrast
end Homogenization
