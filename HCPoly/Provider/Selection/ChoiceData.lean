/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.ProviderData

/-!
# Data fixed before the global selection reads the law

This structure records the constants and the ordered-choice inequalities used
by the transition and progress arguments.  It contains no law-dependent data.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

noncomputable section

/-- The structural constants fixed in Phases 0 and 4 before the law. -/
structure Constants (d H : ℕ) (g epsCal etaDr etaProfBar deltaDetBar Cd : ℝ)
    (Khop Ctr : ℝ) (Ltr : ℕ) where
  chop : ℝ
  chop_pos : 0 < chop
  Crec : ℝ
  Crec_pos : 0 < Crec
  h : ℤ
  one_le_h : 1 ≤ h
  service_le : lambdaPort d (initExpQ d g : ℝ) (initExpA g) Crec h ≤ 1 / 4
  drift_service_le : (3 : ℝ) ^ (-(h : ℝ) * initExpRhoDr g) ≤ 1 / 8
  CportRaw : ℝ
  Cport : ℝ
  Csvc : ℝ
  CportRaw_pos : 0 < CportRaw
  Cport_eq : Cport = max 1 CportRaw
  one_le_Cport : 1 ≤ Cport
  CportRaw_le : CportRaw ≤ Cport
  Csvc_pos : 0 < Csvc
  AL : ℤ → ℝ
  AL_pos : ∀ L : ℤ, 1 ≤ L → 0 < AL L
  transportData : TransportProviderData d g (initExpQ d g) (initExpRhoMax d g)
    (initExpA g) Khop Ctr Ltr
  portableData : PortableProviderData d (initExpQ d g) (initExpA g)
    (initExpRhoMax d g) Crec h CportRaw Csvc AL
  etaOut : ℝ
  epsSt : ℝ
  etaIn : ℝ
  etaOut_pos : 0 < etaOut
  epsSt_pos : 0 < epsSt
  etaIn_pos : 0 < etaIn
  profile_caps : max (max etaIn etaOut) epsSt ≤ etaProfBar
  portable_share : Cport * etaOut ≤ epsSt
  startup_share : AL (H : ℤ) * etaIn ≤ etaOut / 4
  etaNew : ℝ
  etaNew_pos : 0 < etaNew
  etaNew_lt_one : etaNew < 1
  new_drift : (1 + (3 : ℝ) ^ (-initExpRhoDr g * (H : ℝ))) * etaNew < etaDr
  deltaTerm : ℝ
  deltaTerm_pos : 0 < deltaTerm
  deltaTerm_le_epsCal : deltaTerm ≤ epsCal
  deltaTerm_le_deltaDetBar : deltaTerm ≤ deltaDetBar
  terminal_profile : AL (H : ℤ) *
    (Real.exp ((initExpQ d g : ℝ) * (d : ℝ) * Real.log (1 + deltaTerm)) - 1) ≤
      etaOut / 4
  terminal_drift :
    (1 + (1 + deltaTerm) ^ d * (3 : ℝ) ^ (-initExpRhoDr g * (H : ℝ))) * etaNew +
      2 * (d : ℝ) * ((1 + deltaTerm) ^ d - 1) ≤ etaDr
  Cphi : ℝ
  Cdir : ℝ
  CdetBar : ℝ
  Cphi_eq : Cphi = max 1 Csvc
  Cdir_eq : Cdir = max ((initExpQ d g : ℝ) * (d : ℝ))
    (max (Cphi * (initExpQ d g : ℝ) * (d : ℝ)) ((d : ℝ) / Real.log 2))
  CdetBar_pos : 0 < CdetBar
  CdetBar_lower : 4 * max Cdir (max ((d : ℝ) / 2) 1) ≤ CdetBar
  etaX : ℝ
  etaX_pos : 0 < etaX
  etaX_le_quarter : etaX ≤ 1 / 4
  etaX_le_epsCal : etaX ≤ epsCal
  projective_tolerance : 1 / 2 * Real.log ((1 + etaX) / (1 - etaX)) ≤ chop / 4
  transport_tolerance : Ctr * etaX ≤ etaIn / 3
  bridge_feedback : 2 * CdetBar * ((h : ℝ) + 2) * Real.log (1 + etaX) ≤
    min chop (Real.log (1 + deltaTerm)) / 4
  terminal_feedback : 1 / 2 * Real.log ((1 + etaX) / (1 - etaX)) +
    2 * CdetBar * ((h : ℝ) + 2) * Real.log (1 + etaX) ≤
      CdetBar * Real.log (1 + deltaTerm) / 2
  Lcommon : ℕ
  l0 : ℕ
  Lcommon_eq : Lcommon = max Ltr
    (⌈4 * (initExpQ d g : ℝ) * chop /
      (initExpA g * Real.log 3)⌉₊ + 1)
  l0_lower : max Lcommon Ltr ≤ l0
  rho_buffer : 2 * chop < initExpRhoDr g * (l0 : ℝ) * Real.log 3 / 2
  a_buffer : 2 * (initExpQ d g : ℝ) * chop <
    initExpA g * (l0 : ℝ) * Real.log 3 / 2
  tauSrc : ℝ
  deltaShort : ℝ
  etaPre : ℝ
  Bshort : ℝ
  tauSrc_pos : 0 < tauSrc
  deltaShort_pos : 0 < deltaShort
  etaPre_pos : 0 < etaPre
  Bshort_pos : 0 < Bshort
  short_log : Ctr * (1 + Real.log Khop) ≤ (l0 : ℝ)
  short_geom : Ctr * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2
  Bshort_cutoff : 1 < initExpRhoDr g * Bshort / 2
  etaPre_le : etaPre ≤ etaNew / 2
  short_thresholds : ∀ b delta R₁ R₂ R₃ : ℝ,
    0 ≤ b → b ≤ etaPre → 0 ≤ delta → delta ≤ deltaShort →
    0 ≤ R₁ → R₁ ≤ tauSrc → 0 ≤ R₂ → R₂ ≤ tauSrc →
    0 ≤ R₃ → R₃ ≤ tauSrc →
    shortBridgeErr d Ctr Khop (initExpRhoDr g) (l0 : ℤ) b delta R₁ R₂ ≤ etaX ∧
      shortNewDrift d Ctr Khop (initExpRhoDr g) (l0 : ℤ) b delta R₂ R₃ ≤ etaNew
  shortHopData : ShortHopProviderData d g chop etaNew etaX Khop Ctr Cd l0
    tauSrc deltaShort etaPre Bshort
  etaHop : ℝ
  etaReady : ℝ
  etaHop_pos : 0 < etaHop
  etaHop_le_one : etaHop ≤ 1
  etaReady_pos : 0 < etaReady
  etaReady_le_one : etaReady ≤ 1
  hop_transport_share : Ctr * (3 : ℝ) ^ (2 * initExpA g * (l0 : ℝ)) * etaHop ≤ etaIn / 3
  ready_share : AL (2 * (l0 : ℤ)) * etaReady ≤ etaHop / 4
  short_det_share : AL (2 * (l0 : ℤ)) *
    (Real.exp ((initExpQ d g : ℝ) * (d : ℝ) * Real.log (1 + deltaShort)) - 1) ≤
      etaHop / 4
  rDr : ℝ
  tauTr : ℝ
  Cinit : ℝ
  etaInit : ℝ
  one_lt_rDr : 1 < rDr
  rDr_pow_le : rDr ^ d ≤ 2
  rDr_drift : 2 * (d : ℝ) * (rDr ^ d - 1) ≤ etaPre / 4
  tauTr_pos : 0 < tauTr
  tauTr_le : tauTr ≤ etaIn / 3
  Cinit_pos : 0 < Cinit
  etaInit_pos : 0 < etaInit
  init_share : Cinit * etaInit ≤ min etaIn etaReady
  etaInit_le : etaInit ≤ etaNew
  bHop : ℕ
  bHop_eq : bHop = ⌈Real.logb 2 (max 1 (etaNew / etaPre))⌉₊

end

end Selection
end HighContrast
end Homogenization
