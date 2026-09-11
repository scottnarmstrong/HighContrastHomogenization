/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TerminationCounts
import HCPoly.Provider.Selection.TerminationServiceRun
import HCPoly.Provider.Selection.Cutoff

/-!
# Potential summation and the selector cap

These lemmas isolate the arithmetic of Phase 5.  They telescope a genuine
finite sequence of one-step potential drops, record the exact cancellation of
the hop debit against the aggregate determinant charge, and compare the
resulting real transition bound with the natural-number execution cap.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- A profile bounded by the readiness threshold has logarithmic work at most
`log 2`. -/
theorem stateWork_le_log_two {P : Measure (CoeffSpace d)}
    {Q a rhoMax etaReady : ℝ} {jStar : ℤ} {S : State d}
    (hetaReady : 0 < etaReady)
    (hprofile : stateProfile P Q a rhoMax jStar S ≤ ENNReal.ofReal etaReady) :
    stateWork P Q a rhoMax etaReady jStar S ≤ Real.log 2 := by
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprofile
  rw [ENNReal.toReal_ofReal hetaReady.le] at hreal
  have hratio : etaReady⁻¹ * (stateProfile P Q a rhoMax jStar S).toReal ≤ 1 := by
    rw [inv_mul_eq_div, div_le_one hetaReady]
    exact hreal
  rw [stateWork_eq]
  simp only [stateProfile_eq] at hratio
  exact Real.log_le_log (by positivity) (by linarith only [hratio])

/-- The selected initial drift threshold implies the printed dyadic index
bound. -/
theorem initialState_driftIndex_le_bHop
    {P : Measure (CoeffSpace d)} {rhoDr : ℝ} {jStar r0 : ℤ}
    {A0 : BlockMat d} {hcen hnl : ℝ≥0∞}
    (hdrift : linearDrift P rhoDr (1 : Mat d) jStar r0 ≤ c.etaNew) :
    driftIndex P rhoDr c.etaPre jStar (initialState r0 A0 hcen hnl) ≤
      c.bHop := by
  have hratio :
      linearDrift P rhoDr (1 : Mat d) jStar r0 / c.etaPre ≤
        c.etaNew / c.etaPre :=
    div_le_div_of_nonneg_right hdrift c.etaPre_pos.le
  have hmax :
      max 1 (linearDrift P rhoDr (1 : Mat d) jStar r0 / c.etaPre) ≤
        max 1 (c.etaNew / c.etaPre) := max_le_max le_rfl hratio
  have hleft : 0 < max 1
      (linearDrift P rhoDr (1 : Mat d) jStar r0 / c.etaPre) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hleft hmax
  have hceil := Nat.ceil_mono hlog
  simpa only [driftIndex, initialState, c.bHop_eq] using hceil

/-- The initialized state has potential at most `C_F Λ` once the three entry
bounds have been supplied by the initial checkpoint and entry geometry. -/
theorem initialState_potential_le
    {alphaFresh alphaX Crad c0 Chit Bmin alphaSearch : ℝ}
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} {jStar r0 : ℤ} {Lam : ℝ}
    {A0 : BlockMat d} {hcen hnl : ℝ≥0∞}
    (hLam : 1 ≤ Lam) (halphaFresh : 0 ≤ alphaFresh)
    (halphaX : 1 ≤ alphaX)
    (hprofile : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar (initialState r0 A0 hcen hnl) ≤
        ENNReal.ofReal c.etaReady)
    (hdrift : linearDrift P (initExpRhoDr g) (1 : Mat d) jStar r0 ≤ c.etaNew)
    (hprojective : stateProjectiveDistance (initialState r0 A0 hcen hnl) ≤
      Crad * Lam) :
    statePotential P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        (initExpRhoDr g) jStar c.etaReady c.etaPre c.etaReady alphaX
        alphaFresh alphaSearch (initialState r0 A0 hcen hnl) ≤ cc.CF * Lam := by
  have hwork := stateWork_le_log_two c.etaReady_pos hprofile
  have hdriftIndex := initialState_driftIndex_le_bHop (c := c) (A0 := A0)
    (hcen := hcen) (hnl := hnl) hdrift
  have hworkWeighted :
      c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) c.etaReady jStar (initialState r0 A0 hcen hnl) ≤
        c.etaReady * Real.log 2 :=
    mul_le_mul_of_nonneg_left hwork c.etaReady_pos.le
  have hprojectiveWeighted :
      alphaX * stateProjectiveDistance (initialState r0 A0 hcen hnl) ≤
        alphaX * (Crad * Lam) :=
    mul_le_mul_of_nonneg_left hprojective (le_trans zero_le_one halphaX)
  rw [cc.CF_eq, potentialCoefficient_eq]
  have hdriftReal :
      (driftIndex P (initExpRhoDr g) c.etaPre jStar
        (initialState r0 A0 hcen hnl) : ℝ) ≤ (c.bHop : ℝ) := by
    exact_mod_cast hdriftIndex
  simp only [initialState] at hworkWeighted hdriftReal hprojectiveWeighted
  simp [statePotential_eq, initialState]
  calc
    _ ≤ c.etaReady * Real.log 2 + (c.bHop : ℝ) +
        alphaX * (Crad * Lam) + alphaFresh := by
      linarith only [hworkWeighted, hdriftReal, hprojectiveWeighted]
    _ ≤ (c.etaReady * Real.log 2 + (c.bHop : ℝ) + alphaFresh +
        alphaX * Crad) * Lam := by
      have hscaledProjective : alphaX * (Crad * Lam) =
          (alphaX * Crad) * Lam := by ring
      rw [hscaledProjective]
      have hrest : c.etaReady * Real.log 2 + (c.bHop : ℝ) + alphaFresh ≤
          (c.etaReady * Real.log 2 + (c.bHop : ℝ) + alphaFresh) * Lam := by
        have hrest0 : 0 ≤ c.etaReady * Real.log 2 + (c.bHop : ℝ) + alphaFresh := by
          have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          exact add_nonneg
            (add_nonneg (mul_nonneg c.etaReady_pos.le hlog2) (Nat.cast_nonneg _))
            halphaFresh
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hLam hrest0
      linarith only [hrest]

/-- The real source bound lies strictly below the natural execution cap. -/
theorem lt_transitionCap_of_real_le {N : ℕ} {CN Lam : ℝ}
    (hN : (N : ℝ) ≤ CN * Lam) : N < transitionCap CN Lam := by
  have hceil : CN * Lam ≤ (⌈CN * Lam⌉₊ : ℝ) := Nat.le_ceil _
  have hstrict : (N : ℝ) < (transitionCap CN Lam : ℝ) := by
    rw [transitionCap_eq]
    push_cast
    linarith only [hN, hceil]
  exact_mod_cast hstrict

/-- The aggregate charge term cancels the preselected hop debit exactly,
leaving the transition coefficient `C_N`. -/
theorem transitionCount_le_of_hop_cancellation
    {Ntr Nhop : ℕ} {c0 mHop Cdet h etaX CF CN Lam entry charge : ℝ}
    (hc0 : 0 < c0) (hCdet : 0 ≤ Cdet) (hh : 0 ≤ h + 2)
    (hmHop : mHop = 2 * Cdet * (h + 2) * Real.log (1 + etaX))
    (hentry : entry ≤ Real.log 72 * Lam)
    (hcharge : charge ≤ (h + 2) *
      (entry + 2 * (Nhop : ℝ) * Real.log (1 + etaX)))
    (hpotential : c0 * (Ntr : ℝ) + mHop * (Nhop : ℝ) ≤
      CF * Lam + Cdet * charge)
    (hCN : CN = (CF + Cdet * (h + 2) * Real.log 72) / c0) :
    (Ntr : ℝ) ≤ CN * Lam := by
  have hinner : entry + 2 * (Nhop : ℝ) * Real.log (1 + etaX) ≤
      Real.log 72 * Lam + 2 * (Nhop : ℝ) * Real.log (1 + etaX) :=
    by linarith only [hentry]
  have hcharge' := hcharge.trans (mul_le_mul_of_nonneg_left hinner hh)
  have hweighted := mul_le_mul_of_nonneg_left hcharge' hCdet
  have hraw : c0 * (Ntr : ℝ) ≤
      (CF + Cdet * (h + 2) * Real.log 72) * Lam := by
    rw [hmHop] at hpotential
    linarith only [hpotential, hweighted]
  rw [hCN, div_mul_eq_mul_div]
  apply (le_div_iff₀ hc0).2
  simpa only [mul_comm] using hraw

end

end Selection
end HighContrast
end Homogenization
