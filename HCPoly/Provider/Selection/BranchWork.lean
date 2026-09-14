/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Potential
import HCPoly.Provider.Selection.Charges

/-!
# Fixed-grid work inputs for selector branches

The portable-history provider is read at the actual checkpoint and cursor of a
selector state.  The resulting extended-real profile estimates are converted
here to the real logarithmic work used by the potential.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- The logarithmic profile work is nonnegative at every positive readiness
threshold. -/
theorem stateWork_nonneg {P : Measure (CoeffSpace d)}
    {Q a rhoMax eta : ℝ} (heta : 0 < eta) {jStar : ℤ} {S : State d} :
    0 ≤ stateWork P Q a rhoMax eta jStar S := by
  rw [stateWork_eq]
  exact Real.log_nonneg (by
    have hterm : 0 ≤ eta⁻¹ *
        (portableProfile P Q a rhoMax S.q jStar S.checkpoint S.cursor).toReal :=
      mul_nonneg (inv_nonneg.mpr heta.le) ENNReal.toReal_nonneg
    linarith only [hterm])

/-- Definedness and positivity for one fixed-grid read interval. -/
structure FixedGridReadData (P : Measure (CoeffSpace d)) (jStar : ℤ)
    (S : State d) (TMax : ℤ) : Prop where
  rounded : IsRoundedGrid jStar S.q
  finiteMean : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P S.q j
  positiveMean : ∀ j : ℤ, jStar ≤ j → j ≤ TMax →
    Book.Ch02.BlockPosDef (adaptedMean P S.q j)
  finiteMoment : ∀ j : ℤ, jStar ≤ j → j ≤ TMax →
    centeredMoment P (initExpQ d g : ℝ) S.q j ≠ ⊤

private theorem toReal_add_bound {x y : ℝ≥0∞} {A B : ℝ}
    (hx : x ≠ ⊤) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : y ≤ ENNReal.ofReal A * x + ENNReal.ofReal B) :
    y.toReal ≤ A * x.toReal + B := by
  have htop : ENNReal.ofReal A * x + ENNReal.ofReal B ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx, ENNReal.ofReal_ne_top⟩
  have hr := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hA,
    ENNReal.toReal_ofReal hB] at hr
  exact hr

private theorem stateHistory_eq_portableHistory
    {P : Measure (CoeffSpace d)} {Q a rhoMax : ℝ} {jStar : ℤ}
    {S : State d}
    (hexact : ExactStateData P Q a rhoMax jStar S) :
    stateHistory S = portableHistory P Q a rhoMax S.q jStar S.checkpoint := by
  rcases hexact with ⟨-, -, hcen, hnl, -, -⟩
  rw [stateHistory_eq, portableHistory, hcen, hnl]

private theorem fixedSpanWork_of_bound {p p' : ℝ≥0∞} {A X : ℝ}
    (hp : p ≠ ⊤) (hpOne : p ≤ 1) (hA : 0 ≤ A) (hX : 0 ≤ X)
    (hbound : p' ≤ ENNReal.ofReal A * p +
      ENNReal.ofReal (A * (Real.exp X - 1))) :
    scaledWork c.etaReady p'.toReal ≤ fixedSpanLoad A + X := by
  have hexp : 0 ≤ Real.exp X - 1 := sub_nonneg.mpr (Real.one_le_exp hX)
  have hreal := toReal_add_bound hp hA (mul_nonneg hA hexp) hbound
  have hpReal : p.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hpOne
  exact scaledWork_fixedSpan c.etaReady_pos c.etaReady_le_one hA hpReal
    ENNReal.toReal_nonneg hX hreal

/-- A service step satisfies the source work row at the actual state cursor. -/
theorem serviceWork_le (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hstart : S.checkpoint + c.h ≤ S.cursor)
    (hprofileFinite : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤) :
    c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar
        (advanceCursor P S (S.cursor + c.h) .search none) ≤
      c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar S +
      c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) *
        serviceWindowCharge P S.q c.h S.cursor := by
  rcases hexact with ⟨-, -, -, -, hjcheck, hcheckCursor⟩
  have hh := c.one_le_h
  obtain ⟨-, hdetnn, -, -, -, hservice, -, -, -⟩ :=
    c.portableData.law P inferInstance hP hunit jStar S.q hread.rounded
      jStar S.checkpoint (S.cursor + c.h) le_rfl hjcheck
      (hcheckCursor.trans (by omega)) hread.finiteMean hread.positiveMean
      hread.finiteMoment
  have hbound := hservice S.cursor hstart le_rfl
  let X : ℝ := (initExpQ d g : ℝ) * synchCharge P S.q c.h S.cursor
  have hcharge : 0 ≤ synchCharge P S.q c.h S.cursor := by
    rw [synchCharge]
    exact Finset.sum_nonneg fun j hj => by
      have hjb := Finset.mem_Icc.mp hj
      exact hdetnn (j - c.h) j (by omega) (by omega) (by omega)
  have hQ : 0 ≤ (initExpQ d g : ℝ) := by
    exact_mod_cast (Nat.zero_le (initExpQ d g))
  have hX : 0 ≤ X := mul_nonneg hQ hcharge
  have hnoise : 0 ≤ c.Csvc * (Real.exp X - 1) :=
    mul_nonneg c.Csvc_pos.le (sub_nonneg.mpr (Real.one_le_exp hX))
  have hlam : 0 ≤ lambdaPort d (initExpQ d g : ℝ) (initExpA g)
      c.Crec c.h :=
    (Real.rpow_nonneg (by norm_num) _).trans (le_max_right _ _)
  have hcoef : 0 ≤ lambdaPort d (initExpQ d g : ℝ) (initExpA g)
      c.Crec c.h * Real.exp X :=
    mul_nonneg hlam (Real.exp_pos X).le
  have hreal := toReal_add_bound hprofileFinite hcoef hnoise (by
    simpa only [X] using! hbound)
  have hwork := scaledWork_service c.etaReady_pos c.etaReady_le_one
    hlam (c.service_le.trans (by norm_num))
    c.Csvc_pos.le ENNReal.toReal_nonneg ENNReal.toReal_nonneg hX hreal
  have hsync := synchCharge_eq_natCast_mul_serviceWindowCharge
    (P := P) (q := S.q) (u := S.cursor) (by omega : d ≠ 0) c.one_le_h
    (fun j hjlow hjhigh => posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q j)
      (hread.positiveMean j (by omega) (by omega)))
  rw [c.Cphi_eq]
  simpa only [scaledWork, stateWork, stateProfile, advanceCursor, X, hsync,
    mul_assoc] using hwork

/-- Above readiness, a service step also pays the strict work decrement. -/
theorem serviceWork_decrement_le (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + c.h))
    (hstart : S.checkpoint + c.h ≤ S.cursor)
    (hprofileFinite : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤)
    (habove : ENNReal.ofReal c.etaReady < stateProfile P
      (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g) jStar S) :
    c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar
        (advanceCursor P S (S.cursor + c.h) .search none) ≤
      c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar S -
      c.etaReady * potentialWorkDecrement c +
      c.Cphi * (initExpQ d g : ℝ) * (d : ℝ) *
        serviceWindowCharge P S.q c.h S.cursor := by
  rcases hexact with ⟨-, -, -, -, hjcheck, hcheckCursor⟩
  have hh := c.one_le_h
  obtain ⟨-, hdetnn, -, -, -, hservice, -, -, -⟩ :=
    c.portableData.law P inferInstance hP hunit jStar S.q hread.rounded
      jStar S.checkpoint (S.cursor + c.h) le_rfl hjcheck
      (hcheckCursor.trans (by omega)) hread.finiteMean hread.positiveMean
      hread.finiteMoment
  have hbound := hservice S.cursor hstart le_rfl
  let X : ℝ := (initExpQ d g : ℝ) * synchCharge P S.q c.h S.cursor
  have hcharge : 0 ≤ synchCharge P S.q c.h S.cursor := by
    rw [synchCharge]
    exact Finset.sum_nonneg fun j hj => by
      have hjb := Finset.mem_Icc.mp hj
      exact hdetnn (j - c.h) j (by omega) (by omega) (by omega)
  have hQ : 0 ≤ (initExpQ d g : ℝ) := by
    exact_mod_cast (Nat.zero_le (initExpQ d g))
  have hX : 0 ≤ X := mul_nonneg hQ hcharge
  have hnoise : 0 ≤ c.Csvc * (Real.exp X - 1) :=
    mul_nonneg c.Csvc_pos.le (sub_nonneg.mpr (Real.one_le_exp hX))
  have hlam : 0 ≤ lambdaPort d (initExpQ d g : ℝ) (initExpA g)
      c.Crec c.h :=
    (Real.rpow_nonneg (by norm_num) _).trans (le_max_right _ _)
  have hcoef : 0 ≤ lambdaPort d (initExpQ d g : ℝ) (initExpA g)
      c.Crec c.h * Real.exp X :=
    mul_nonneg hlam (Real.exp_pos X).le
  have hreal := toReal_add_bound hprofileFinite hcoef hnoise (by
    simpa only [X] using! hbound)
  have hp : c.etaReady < (stateProfile P (initExpQ d g : ℝ)
      (initExpA g) (initExpRhoMax d g) jStar S).toReal := by
    rw [← ENNReal.toReal_ofReal c.etaReady_pos.le]
    exact (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hprofileFinite).2 habove
  have hwork := scaledWork_service_decrement c.etaReady_pos
    c.etaReady_le_one hlam
    (c.service_le.trans_lt (by norm_num)) c.Csvc_pos.le ENNReal.toReal_nonneg
    hX hp hreal
  have hsync := synchCharge_eq_natCast_mul_serviceWindowCharge
    (P := P) (q := S.q) (u := S.cursor) (by omega : d ≠ 0) c.one_le_h
    (fun j hjlow hjhigh => posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q j)
      (hread.positiveMean j (by omega) (by omega)))
  rw [c.Cphi_eq, potentialWorkDecrement_eq]
  simpa only [scaledWork, stateWork, stateProfile, advanceCursor, X, hsync,
    mul_assoc] using hwork

/-- A startup read from an exact fresh checkpoint has the fixed-span work
load and the uniform determinant slope. -/
theorem startupWork_le (hd : 2 ≤ d) (hetaProfBar : etaProfBar ≤ 1)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar L : ℤ} {S : State d}
    (hL : 1 ≤ L)
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + L))
    (hcheckpoint : S.checkpoint = S.cursor)
    (hhistory : stateHistory S ≤ ENNReal.ofReal c.etaIn) :
    c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar
        (advanceCursor P S (S.cursor + L) .search none) ≤
      fixedSpanLoad (c.AL L) + (initExpQ d g : ℝ) * (d : ℝ) *
        detLoss P S.q S.cursor (S.cursor + L) := by
  have hexactCopy := hexact
  rcases hexact with ⟨-, -, -, -, hjcheck, hcheckCursor⟩
  obtain ⟨-, hdetnn, -, -, -, -, -, -, hstartup⟩ :=
    c.portableData.law P inferInstance hP hunit jStar S.q hread.rounded
      jStar S.checkpoint (S.cursor + L) le_rfl hjcheck
      (hcheckCursor.trans (by omega)) hread.finiteMean hread.positiveMean
      hread.finiteMoment
  have hetaInOne : c.etaIn ≤ 1 := by
    have hin : c.etaIn ≤ etaProfBar :=
      (le_max_left c.etaIn c.etaOut).trans
        ((le_max_left (max c.etaIn c.etaOut) c.epsSt).trans c.profile_caps)
    exact hin.trans hetaProfBar
  have hpOne : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) S.q jStar S.checkpoint ≤ 1 := by
    rw [← stateHistory_eq_portableHistory hexactCopy]
    exact hhistory.trans <| by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hetaInOne
  have hpFinite : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) S.q jStar S.checkpoint ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hpOne
  have hbound := hstartup L hL (by omega) hpOne
  let X : ℝ := (initExpQ d g : ℝ) *
    detIncrement P S.q S.cursor (S.cursor + L)
  have hQ : 0 ≤ (initExpQ d g : ℝ) := by positivity
  have hX : 0 ≤ X := mul_nonneg hQ
    (hdetnn S.cursor (S.cursor + L) (by omega) (by omega) le_rfl)
  have hwork := fixedSpanWork_of_bound (c := c) hpFinite hpOne
    (c.AL_pos L hL).le hX (by simpa only [hcheckpoint, X] using hbound)
  have hinc := detIncrement_eq_natCast_mul_detLoss
    (P := P) (q := S.q) (u := S.cursor) (v := S.cursor + L)
    (by omega : d ≠ 0)
    (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.cursor)
      (hread.positiveMean S.cursor (by omega) (by omega)))
    (posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q (S.cursor + L))
      (hread.positiveMean (S.cursor + L) (by omega) le_rfl))
  simpa only [scaledWork, stateWork, stateProfile, advanceCursor, X, hinc,
    hcheckpoint, mul_assoc] using hwork

/-- A bounded incoming profile has the fixed-span propagation work row. -/
theorem propagationWork_le (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar L : ℤ} {S : State d}
    (hL : 1 ≤ L)
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + L))
    (hstart : S.checkpoint + c.h ≤ S.cursor)
    (hprofile : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≤ ENNReal.ofReal c.etaReady) :
    c.etaReady * stateWork P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) c.etaReady jStar
        (advanceCursor P S (S.cursor + L) .search none) ≤
      fixedSpanLoad (c.AL L) + (initExpQ d g : ℝ) * (d : ℝ) *
        detLoss P S.q S.cursor (S.cursor + L) := by
  rcases hexact with ⟨-, -, -, -, hjcheck, hcheckCursor⟩
  obtain ⟨-, hdetnn, -, -, -, -, -, hprop, -⟩ :=
    c.portableData.law P inferInstance hP hunit jStar S.q hread.rounded
      jStar S.checkpoint (S.cursor + L) le_rfl hjcheck
      (hcheckCursor.trans (by omega)) hread.finiteMean hread.positiveMean
      hread.finiteMoment
  have hpOne : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≤ 1 := hprofile.trans <| by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal c.etaReady_le_one
  have hpFinite : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hpOne
  have hbound := hprop L S.cursor hL hstart le_rfl hpOne
  let X : ℝ := (initExpQ d g : ℝ) *
    detIncrement P S.q S.cursor (S.cursor + L)
  have hQ : 0 ≤ (initExpQ d g : ℝ) := by positivity
  have hX : 0 ≤ X := mul_nonneg hQ
    (hdetnn S.cursor (S.cursor + L) (by omega) (by omega) le_rfl)
  have hwork := fixedSpanWork_of_bound (c := c) hpFinite hpOne
    (c.AL_pos L hL).le hX (by simpa only [stateProfile, X] using hbound)
  have hinc := detIncrement_eq_natCast_mul_detLoss
    (P := P) (q := S.q) (u := S.cursor) (v := S.cursor + L)
    (by omega : d ≠ 0)
    (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.cursor)
      (hread.positiveMean S.cursor (by omega) (by omega)))
    (posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P S.q (S.cursor + L))
      (hread.positiveMean (S.cursor + L) (by omega) le_rfl))
  simpa only [scaledWork, stateWork, stateProfile, advanceCursor, X, hinc,
    mul_assoc] using hwork

end

end Homogenization.HighContrast.Selection
