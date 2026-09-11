/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileBadMajorant
import HCPoly.Provider.Response.ProfileRowSource
import HCPoly.Provider.Response.ProfileFiniteness

/-!
# Scalar profile caps for the response window

The centered-history cap and source half-cap combine at the exact profile
root used by the response window.
-/

namespace Homogenization.HighContrast.Response

open scoped ENNReal

noncomputable section

/-- Taking the inverse-`Q` power of the centered-history cap produces its
exact half-root. -/
theorem cap_rpow_inv_eq (Q : ℕ) (hQ : 0 < Q) {eta : ℝ}
    (heta : 0 ≤ eta) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(Q : ℤ)) * eta) ^ ((Q : ℝ)⁻¹) =
      ENNReal.ofReal (1 / 2 * eta ^ ((Q : ℝ)⁻¹)) := by
  have hQreal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hbase : 0 ≤ (2 : ℝ) ^ (-(Q : ℤ)) * eta :=
    mul_nonneg (zpow_nonneg (by norm_num) _) heta
  rw [ENNReal.ofReal_rpow_of_nonneg hbase (inv_nonneg.mpr hQreal.le)]
  congr 1
  rw [Real.mul_rpow (zpow_nonneg (by norm_num) _) heta]
  have hpow : ((2 : ℝ) ^ (-(Q : ℤ))) ^ ((Q : ℝ)⁻¹) = 1 / 2 := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hcast : ((-(Q : ℤ) : ℤ) : ℝ) = -(Q : ℝ) := by simp
    have hexp : -(Q : ℝ) * (Q : ℝ)⁻¹ = -1 := by field_simp
    rw [hcast, hexp, Real.rpow_neg_one]
    norm_num
  rw [hpow]

/-- The centered half-root and source half-root close the total-history root
at the exact response-window scale. -/
theorem total_root_le_of_cap {Q : ℕ} (hQ : 0 < Q)
    {eta : ℝ} (heta : 0 ≤ eta) {centered source total : ℝ≥0∞}
    (hcentered : centered ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(Q : ℤ)) * eta))
    (hsource : source ≤
      ENNReal.ofReal (1 / 2 * eta ^ ((Q : ℝ)⁻¹)))
    (htotal : total ^ ((Q : ℝ)⁻¹) ≤
      centered ^ ((Q : ℝ)⁻¹) + source) :
    total ^ ((Q : ℝ)⁻¹) ≤
      ENNReal.ofReal (eta ^ ((Q : ℝ)⁻¹)) := by
  have hQreal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hcenteredRoot : centered ^ ((Q : ℝ)⁻¹) ≤
      ENNReal.ofReal (1 / 2 * eta ^ ((Q : ℝ)⁻¹)) := by
    calc
      centered ^ ((Q : ℝ)⁻¹) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (-(Q : ℤ)) * eta) ^ ((Q : ℝ)⁻¹) :=
        ENNReal.rpow_le_rpow hcentered (inv_nonneg.mpr hQreal.le)
      _ = _ := cap_rpow_inv_eq Q hQ heta
  have hhalf : 0 ≤ 1 / 2 * eta ^ ((Q : ℝ)⁻¹) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg heta _)
  calc
    total ^ ((Q : ℝ)⁻¹) ≤ centered ^ ((Q : ℝ)⁻¹) + source := htotal
    _ ≤ ENNReal.ofReal (1 / 2 * eta ^ ((Q : ℝ)⁻¹)) +
        ENNReal.ofReal (1 / 2 * eta ^ ((Q : ℝ)⁻¹)) :=
      add_le_add hcenteredRoot hsource
    _ = ENNReal.ofReal (1 / 2 * eta ^ ((Q : ℝ)⁻¹) +
        1 / 2 * eta ^ ((Q : ℝ)⁻¹)) := by
      rw [ENNReal.ofReal_add hhalf hhalf]
    _ = ENNReal.ofReal (eta ^ ((Q : ℝ)⁻¹)) := by
      congr 1
      ring

/-- Raising an inverse-`Q` root bound back to `Q` recovers the total cap. -/
theorem total_le_of_root_le {Q : ℕ} (hQ : 0 < Q)
    {eta : ℝ} (heta : 0 ≤ eta) {total : ℝ≥0∞}
    (hroot : total ^ ((Q : ℝ)⁻¹) ≤
      ENNReal.ofReal (eta ^ ((Q : ℝ)⁻¹))) :
    total ≤ ENNReal.ofReal eta := by
  have hQreal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hexp : (Q : ℝ)⁻¹ * (Q : ℝ) = 1 :=
    inv_mul_cancel₀ hQreal.ne'
  calc
    total = total ^ (1 : ℝ) := (ENNReal.rpow_one total).symm
    _ = total ^ ((Q : ℝ)⁻¹ * (Q : ℝ)) := by rw [hexp]
    _ = (total ^ ((Q : ℝ)⁻¹)) ^ (Q : ℝ) := ENNReal.rpow_mul total _ _
    _ ≤ ENNReal.ofReal (eta ^ ((Q : ℝ)⁻¹)) ^ (Q : ℝ) :=
      ENNReal.rpow_le_rpow hroot hQreal.le
    _ = ENNReal.ofReal ((eta ^ ((Q : ℝ)⁻¹)) ^ (Q : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg heta _) hQreal.le
    _ = ENNReal.ofReal eta := by
      congr 1
      rw [← Real.rpow_mul heta, hexp, Real.rpow_one]

/-- Unit drift and the cap-two source row bound give the response-window
geometric row constant. -/
theorem profile_row_gamma_le
    {d : ℕ} {P : MeasureTheory.Measure (CoeffSpace d)}
    {rhoDr : ℝ} {q : Mat d} {Csrc g : ℝ} {E : BlockMat d}
    {jStar : ℤ} {m0 : Mat d} {s : ℤ} {GammaStar : ℝ}
    (hGamma : GammaStar =
      2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) + 1)
    (hdrift : linearDrift P rhoDr q jStar s ≤ 1)
    (hsource : kappaRef E * boundaryConst Csrc g m0 ^ 2 * 2 ^ 2 /
        ((3 : ℝ) ^ (3 / 2 - g) - 1) *
          (3 : ℝ) ^ (-(3 / 2) * ((s : ℝ) - (jStar : ℝ))) ≤ 1) :
    profileRowGamma P rhoDr q Csrc g E jStar m0 s ≤ GammaStar := by
  have hpowLt : (3 : ℝ) ^ (-(3 / 2) : ℝ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hden : 0 < 1 - (3 : ℝ) ^ (-(3 / 2) : ℝ) := by
    linarith only [hpowLt]
  have hnum : 1 + linearDrift P rhoDr q jStar s ≤ 2 := by
    linarith only [hdrift]
  have hfrac :
      (1 + linearDrift P rhoDr q jStar s) /
          (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) ≤
        2 / (1 - (3 : ℝ) ^ (-(3 / 2) : ℝ)) :=
    (div_le_div_iff_of_pos_right hden).2 hnum
  rw [profileRowGamma_eq, hGamma]
  linarith only [hfrac, hsource]

/-- The retained profile bounds imply both the sharp profile cap and its
weaker unit-scale consequence. -/
theorem history_profile_smallness
    {portable profile : ℝ≥0∞} {Cport etaProf etaIn etaOut epsSt eta : ℝ}
    {Q : ℕ} (hQ : 0 < Q) (heta : 0 ≤ eta)
    (hmaj : portable ≤ ENNReal.ofReal Cport * profile)
    (hscaled : ENNReal.ofReal Cport * profile ≤ ENNReal.ofReal epsSt)
    (hmax : max (max etaIn etaOut) epsSt ≤ etaProf)
    (hcap : etaProf ≤ (2 : ℝ) ^ (-(Q : ℤ)) * eta) :
    portable ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(Q : ℤ)) * eta) ∧
      portable ≤ ENNReal.ofReal eta := by
  have heps : epsSt ≤ etaProf := (le_max_right _ _).trans hmax
  have hpow : (2 : ℝ) ^ (-(Q : ℤ)) ≤ 1 := by
    have hz : (-(Q : ℤ)) ≤ 0 := by omega
    simpa only [zpow_zero] using
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hz)
  have hcapEta : (2 : ℝ) ^ (-(Q : ℤ)) * eta ≤ eta := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow heta
  have hsharp : portable ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(Q : ℤ)) * eta) :=
    hmaj.trans (hscaled.trans
      ((ENNReal.ofReal_le_ofReal heps).trans (ENNReal.ofReal_le_ofReal hcap)))
  exact ⟨hsharp, hsharp.trans (ENNReal.ofReal_le_ofReal hcapEta)⟩

/-- A finite total-history cap supplies the literal bad-energy majorant. -/
theorem bad_majorant_from_total_history
    {Q eta beta : ℝ} {hTot : ℝ≥0∞}
    (hQ : 2 < Q) (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 2)
    (hTotLe : hTot ≤ ENNReal.ofReal eta) (hbeta : beta ≤ eta / 2) :
    profileBadMajorant Q hTot.toReal beta ≤
      (2 : ℝ) ^ (Q / 2) * eta ^ (1 / 2 : ℝ) := by
  have hreal : hTot.toReal ≤ eta :=
    toReal_le_of_le_ofReal heta0.le hTotLe
  exact profileBadMajorant_le_of_small hQ heta0 heta1 ENNReal.toReal_nonneg
    hreal hbeta

/-- A finite cap passes through a nonnegative extended-nonnegative power. -/
theorem history_root_le_of_cap {x : ℝ≥0∞} {eta p : ℝ}
    (heta : 0 ≤ eta) (hp : 0 ≤ p) (hx : x ≤ ENNReal.ofReal eta) :
    x ^ p ≤ ENNReal.ofReal (eta ^ p) := by
  calc
    x ^ p ≤ ENNReal.ofReal eta ^ p := ENNReal.rpow_le_rpow hx hp
    _ = ENNReal.ofReal (eta ^ p) := ENNReal.ofReal_rpow_of_nonneg heta hp

/-- The three weak-profile terms specialize to the response-window weak-root
constant while retaining all profile carriers in `ENNReal`. -/
theorem weak_root_le_rstar
    {N U energy center : ℝ≥0∞}
    {C K Len Lam KStar LenStar LambdaStar sqrtTwo alpha cconst
      UStar BStar expo etaRoot RStar kappa : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hLen : 0 ≤ Len)
    (hKStar : 0 ≤ KStar) (hLenStar : 0 ≤ LenStar)
    (hLambdaStar : 0 ≤ LambdaStar) (hSqrtTwo : 0 ≤ sqrtTwo)
    (halpha : 0 < alpha) (hcconst : 0 ≤ cconst)
    (hUStar : 0 ≤ UStar) (hBStar : 0 ≤ BStar)
    (hexpo : 0 ≤ expo) (hetaRoot : 0 ≤ etaRoot)
    (hKL : K * Len ≤ KStar * LenStar * Real.sqrt kappa)
    (hKLam : K * Lam ≤ KStar * LambdaStar * Real.sqrt kappa)
    (hU : U ≤ ENNReal.ofReal UStar)
    (henergy : energy ≤ ENNReal.ofReal
      (sqrtTwo * Lam * (BStar + expo)))
    (hcenter : center ≤ ENNReal.ofReal (K * Len * etaRoot))
    (hN : N ≤ ENNReal.ofReal (C * K * Len) * U +
        ENNReal.ofReal (C * K / (2 * alpha)) * energy +
        ENNReal.ofReal cconst * center)
    (hRStar : RStar = C * KStar * LenStar * UStar +
        C * KStar * sqrtTwo * LambdaStar / (2 * alpha) * (BStar + expo) +
        cconst * KStar * LenStar * etaRoot) :
    N ≤ ENNReal.ofReal (RStar * Real.sqrt kappa) := by
  have hsqrtK : 0 ≤ Real.sqrt kappa := Real.sqrt_nonneg _
  have hden : 0 ≤ 2 * alpha := by positivity
  have hsumBE : 0 ≤ BStar + expo := add_nonneg hBStar hexpo
  have hterm1 : ENNReal.ofReal (C * K * Len) * U ≤
      ENNReal.ofReal ((C * KStar * LenStar * UStar) * Real.sqrt kappa) := by
    calc
      ENNReal.ofReal (C * K * Len) * U ≤
          ENNReal.ofReal (C * K * Len) * ENNReal.ofReal UStar := by gcongr
      _ = ENNReal.ofReal ((C * K * Len) * UStar) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC hK) hLen)]
      _ ≤ ENNReal.ofReal ((C * KStar * LenStar * UStar) *
          Real.sqrt kappa) := by
        apply ENNReal.ofReal_le_ofReal
        have hscaled := mul_le_mul_of_nonneg_left hKL hC
        have hscaled' := mul_le_mul_of_nonneg_right hscaled hUStar
        calc
          (C * K * Len) * UStar = C * (K * Len) * UStar := by ring
          _ ≤ C * (KStar * LenStar * Real.sqrt kappa) * UStar := hscaled'
          _ = (C * KStar * LenStar * UStar) * Real.sqrt kappa := by ring
  have hterm2 : ENNReal.ofReal (C * K / (2 * alpha)) * energy ≤
      ENNReal.ofReal ((C * KStar * sqrtTwo * LambdaStar / (2 * alpha) *
        (BStar + expo)) * Real.sqrt kappa) := by
    calc
      ENNReal.ofReal (C * K / (2 * alpha)) * energy ≤
          ENNReal.ofReal (C * K / (2 * alpha)) *
            ENNReal.ofReal (sqrtTwo * Lam * (BStar + expo)) := by gcongr
      _ = ENNReal.ofReal ((C * K / (2 * alpha)) *
          (sqrtTwo * Lam * (BStar + expo))) := by
        rw [← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hC hK) hden)]
      _ ≤ ENNReal.ofReal ((C * KStar * sqrtTwo * LambdaStar /
          (2 * alpha) * (BStar + expo)) * Real.sqrt kappa) := by
        apply ENNReal.ofReal_le_ofReal
        have hscaled := mul_le_mul_of_nonneg_left hKLam hC
        have hscaled' := mul_le_mul_of_nonneg_left hscaled hSqrtTwo
        have hdiv := div_le_div_of_nonneg_right hscaled' hden
        have hfinal := mul_le_mul_of_nonneg_right hdiv hsumBE
        calc
          C * K / (2 * alpha) * (sqrtTwo * Lam * (BStar + expo)) =
              (sqrtTwo * (C * K * Lam) / (2 * alpha)) *
                (BStar + expo) := by ring
          _ ≤ (sqrtTwo * (C * (KStar * LambdaStar * Real.sqrt kappa)) /
              (2 * alpha)) * (BStar + expo) := by
            simpa only [mul_assoc] using hfinal
          _ = (C * KStar * sqrtTwo * LambdaStar / (2 * alpha) *
              (BStar + expo)) * Real.sqrt kappa := by ring
  have hterm3 : ENNReal.ofReal cconst * center ≤
      ENNReal.ofReal ((cconst * KStar * LenStar * etaRoot) *
        Real.sqrt kappa) := by
    calc
      ENNReal.ofReal cconst * center ≤
          ENNReal.ofReal cconst * ENNReal.ofReal (K * Len * etaRoot) := by gcongr
      _ = ENNReal.ofReal (cconst * (K * Len * etaRoot)) := by
        rw [← ENNReal.ofReal_mul hcconst]
      _ ≤ ENNReal.ofReal ((cconst * KStar * LenStar * etaRoot) *
          Real.sqrt kappa) := by
        apply ENNReal.ofReal_le_ofReal
        have hscaled := mul_le_mul_of_nonneg_left hKL hcconst
        have hfinal := mul_le_mul_of_nonneg_right hscaled hetaRoot
        calc
          cconst * (K * Len * etaRoot) = cconst * (K * Len) * etaRoot := by ring
          _ ≤ cconst * (KStar * LenStar * Real.sqrt kappa) * etaRoot := hfinal
          _ = (cconst * KStar * LenStar * etaRoot) * Real.sqrt kappa := by ring
  calc
    N ≤ ENNReal.ofReal (C * K * Len) * U +
        ENNReal.ofReal (C * K / (2 * alpha)) * energy +
        ENNReal.ofReal cconst * center := hN
    _ ≤ ENNReal.ofReal ((C * KStar * LenStar * UStar) * Real.sqrt kappa) +
        ENNReal.ofReal ((C * KStar * sqrtTwo * LambdaStar /
          (2 * alpha) * (BStar + expo)) * Real.sqrt kappa) +
        ENNReal.ofReal ((cconst * KStar * LenStar * etaRoot) *
          Real.sqrt kappa) := add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = ENNReal.ofReal (RStar * Real.sqrt kappa) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), hRStar]
      congr 1
      ring

/-- The recent-cell and recent-average estimates aggregate at the literal
finite-window profile constant. -/
theorem recent_profile_le_ustar
    {cell average centeredRoot nonlinearRoot nonlinearHalf : ℝ≥0∞}
    {Scen Scell Sav etaRoot etaHalf UStar : ℝ}
    (hScen : 0 ≤ Scen) (hScell : 0 ≤ Scell) (hSav : 0 ≤ Sav)
    (hetaRoot : 0 ≤ etaRoot) (hetaHalf : 0 ≤ etaHalf)
    (hcell : cell ≤ ENNReal.ofReal Scen * centeredRoot +
      ENNReal.ofReal Scell * nonlinearRoot)
    (haverage : average ≤ ENNReal.ofReal Sav * nonlinearHalf)
    (hcentered : centeredRoot ≤ ENNReal.ofReal etaRoot)
    (hnonlinear : nonlinearRoot ≤ ENNReal.ofReal etaRoot)
    (hhalf : nonlinearHalf ≤ ENNReal.ofReal etaHalf)
    (hUStar : UStar = (Scen + Scell) * etaRoot + Sav * etaHalf) :
    cell + average ≤ ENNReal.ofReal UStar := by
  have hcell' : cell ≤ ENNReal.ofReal ((Scen + Scell) * etaRoot) := by
    calc
      cell ≤ ENNReal.ofReal Scen * centeredRoot +
          ENNReal.ofReal Scell * nonlinearRoot := hcell
      _ ≤ ENNReal.ofReal Scen * ENNReal.ofReal etaRoot +
          ENNReal.ofReal Scell * ENNReal.ofReal etaRoot := by gcongr
      _ = ENNReal.ofReal ((Scen + Scell) * etaRoot) := by
        rw [← ENNReal.ofReal_mul hScen, ← ENNReal.ofReal_mul hScell,
          ← ENNReal.ofReal_add (mul_nonneg hScen hetaRoot)
            (mul_nonneg hScell hetaRoot)]
        congr 1
        ring
  have hav' : average ≤ ENNReal.ofReal (Sav * etaHalf) := by
    calc
      average ≤ ENNReal.ofReal Sav * nonlinearHalf := haverage
      _ ≤ ENNReal.ofReal Sav * ENNReal.ofReal etaHalf := by gcongr
      _ = ENNReal.ofReal (Sav * etaHalf) := by rw [← ENNReal.ofReal_mul hSav]
  calc
    cell + average ≤ ENNReal.ofReal ((Scen + Scell) * etaRoot) +
        ENNReal.ofReal (Sav * etaHalf) := add_le_add hcell' hav'
    _ = ENNReal.ofReal UStar := by
      rw [hUStar, ENNReal.ofReal_add
        (mul_nonneg (add_nonneg hScen hScell) hetaRoot)
        (mul_nonneg hSav hetaHalf)]

end

end Homogenization.HighContrast.Response
