/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Charges

/-!
# Terminal profile and history bounds

At a stopped selector state, the strict determinant test and the retained
checkpoint history feed the startup row of portable history.  The resulting
profile is then majorized at the terminal scale, with its centered component
bounded by the same terminal allowance.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

private theorem detLoss_lt_log_of_root_lt {P : Measure (CoeffSpace d)}
    {q : Mat d} {u v : ℤ} {delta : ℝ}
    (hu : 0 < adaptedDetRoot P q u) (hv : 0 < adaptedDetRoot P q v)
    (hdelta : 0 < delta)
    (hroot : adaptedDetRoot P q u <
      (1 + delta) * adaptedDetRoot P q v) :
    detLoss P q u v < Real.log (1 + delta) := by
  have hfactor : 0 < 1 + delta := by linarith only [hdelta]
  have hright : 0 < (1 + delta) * adaptedDetRoot P q v :=
    mul_pos hfactor hv
  have hlog := Real.strictMonoOn_log hu hright hroot
  rw [Real.log_mul hfactor.ne' hv.ne'] at hlog
  rw [detLoss]
  linarith only [hlog]

/-- The stopped terminal test bounds the full determinant increment by the
chosen terminal logarithmic allowance. -/
theorem terminal_detIncrement_lt (hd : 2 ≤ d) {P : Measure (CoeffSpace d)}
    {q : Mat d} {s : ℤ}
    (hbase : Book.Ch02.BlockPosDef (adaptedMean P q s))
    (hterm : Book.Ch02.BlockPosDef (adaptedMean P q (s + (H : ℤ))))
    (hpass : adaptedDetRoot P q s <
      (1 + c.deltaTerm) * adaptedDetRoot P q (s + (H : ℤ))) :
    detIncrement P q s (s + (H : ℤ)) <
      (d : ℝ) * Real.log (1 + c.deltaTerm) := by
  have hbase' : (toFullBlockMat (adaptedMean P q s)).PosDef :=
    posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q s) hbase
  have hterm' : (toFullBlockMat (adaptedMean P q (s + (H : ℤ)))).PosDef :=
    posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P q (s + (H : ℤ))) hterm
  have hloss : detLoss P q s (s + (H : ℤ)) < Real.log (1 + c.deltaTerm) :=
    detLoss_lt_log_of_root_lt (ShortHop.detRoot_pos hbase') (ShortHop.detRoot_pos hterm')
      c.deltaTerm_pos hpass
  rw [detIncrement_eq_natCast_mul_detLoss (by omega) hbase' hterm']
  exact mul_lt_mul_of_pos_left hloss (by exact_mod_cast (by omega : 0 < d))

/-- The retained exact state history is the portable history at the terminal
checkpoint. -/
theorem terminal_stateHistory_eq {P : Measure (CoeffSpace d)}
    {Q a rhoMax rhoDr etaIn etaNew etaX : ℝ} {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P Q a rhoMax jStar S)
    (hterminal : TerminalInvariant P rhoDr etaIn etaNew etaX jStar S) :
    stateHistory S = portableHistory P Q a rhoMax S.q jStar S.base := by
  rcases hexact with ⟨-, -, hcen, hnl, -, -⟩
  rcases hterminal with ⟨-, hbase, -, -, -, -⟩
  rw [stateHistory_eq, portableHistory, hcen, hnl, hbase]

/-- Phase 6 profile, history, and centered-history conclusions at a stopped
terminal state.  All analytic hypotheses are the exact portable-history
definedness data already established for the terminal tower. -/
theorem terminal_profile_history_bounds (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hetaProfBar : etaProfBar ≤ 1)
    (hH : 4 ≤ H)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hq : IsRoundedGrid jStar S.q)
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hterminal : TerminalInvariant P (initExpRhoDr g) c.etaIn c.etaNew
      c.etaX jStar S)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ S.base + (H : ℤ) →
      HasFiniteAdaptedMean P S.q j)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ S.base + (H : ℤ) →
      Book.Ch02.BlockPosDef (adaptedMean P S.q j))
    (hmom : ∀ j : ℤ, jStar ≤ j → j ≤ S.base + (H : ℤ) →
      centeredMoment P (initExpQ d g : ℝ) S.q j ≠ ⊤)
    (hpass : adaptedDetRoot P S.q S.base <
      (1 + c.deltaTerm) * adaptedDetRoot P S.q (S.base + (H : ℤ))) :
    portableProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) ≤
        ENNReal.ofReal (c.etaOut / 2) ∧
      portableHistory P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) S.q jStar (S.base + (H : ℤ)) ≤
        ENNReal.ofReal c.Cport *
          portableProfile P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) ∧
      ENNReal.ofReal c.Cport *
          portableProfile P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) ≤
        ENNReal.ofReal c.epsSt ∧
      centeredHistory P (initExpQ d g : ℝ) (initExpRhoMax d g) S.q jStar
          (S.base + (H : ℤ)) ≤ ENNReal.ofReal c.epsSt := by
  have hjbase : jStar ≤ S.base := by
    rcases hexact with ⟨-, -, -, -, hjcheck, -⟩
    rcases hterminal with ⟨-, hbase, -, -, -, -⟩
    simpa only [hbase] using hjcheck
  have hbaseTerm : S.base ≤ S.base + (H : ℤ) := by omega
  have hH1 : (1 : ℤ) ≤ (H : ℤ) := by exact_mod_cast (le_trans (by omega) hH)
  obtain ⟨-, -, -, -, hmajor, -, -, -, hstartup⟩ :=
    c.portableData.law P inferInstance hP hunit jStar S.q hq jStar S.base
      (S.base + (H : ℤ)) le_rfl hjbase hbaseTerm hfin hpos hmom
  have hhist : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) S.q jStar S.base ≤ ENNReal.ofReal c.etaIn := by
    rw [← terminal_stateHistory_eq hexact hterminal]
    exact hterminal.2.2.2.1
  have hetaInOne : c.etaIn ≤ 1 := by
    have hin : c.etaIn ≤ etaProfBar :=
      (le_max_left c.etaIn c.etaOut).trans
        ((le_max_left (max c.etaIn c.etaOut) c.epsSt).trans c.profile_caps)
    exact hin.trans hetaProfBar
  have hhistOne : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) S.q jStar S.base ≤ 1 := by
    exact hhist.trans <| by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hetaInOne
  have hinc := terminal_detIncrement_lt (c := c) hd
    (hpos S.base hjbase hbaseTerm)
    (hpos (S.base + (H : ℤ)) (hjbase.trans hbaseTerm) le_rfl) hpass
  have hQ : 0 < (initExpQ d g : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) (two_le_initExpQ hg)
  have hexp : Real.exp ((initExpQ d g : ℝ) *
        detIncrement P S.q S.base (S.base + (H : ℤ))) - 1 ≤
      Real.exp ((initExpQ d g : ℝ) * (d : ℝ) *
        Real.log (1 + c.deltaTerm)) - 1 := by
    apply sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1
    nlinarith only [hQ, hinc]
  have hA : 0 ≤ c.AL (H : ℤ) := (c.AL_pos _ hH1).le
  have hprof0 := hstartup (H : ℤ) hH1 le_rfl hhistOne
  have hfirst : ENNReal.ofReal (c.AL (H : ℤ)) *
        portableHistory P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) S.q jStar S.base ≤
      ENNReal.ofReal (c.AL (H : ℤ) * c.etaIn) := by
    calc
      _ ≤ ENNReal.ofReal (c.AL (H : ℤ)) * ENNReal.ofReal c.etaIn :=
        mul_le_mul_right hhist _
      _ = _ := by rw [ENNReal.ofReal_mul hA]
  have hsecond : ENNReal.ofReal (c.AL (H : ℤ) *
        (Real.exp ((initExpQ d g : ℝ) *
          detIncrement P S.q S.base (S.base + (H : ℤ))) - 1)) ≤
      ENNReal.ofReal (c.AL (H : ℤ) *
        (Real.exp ((initExpQ d g : ℝ) * (d : ℝ) *
          Real.log (1 + c.deltaTerm)) - 1)) := by
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp hA)
  have hprof : portableProfile P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) ≤
      ENNReal.ofReal (c.etaOut / 2) := by
    calc
      _ ≤ ENNReal.ofReal (c.AL (H : ℤ)) *
            portableHistory P (initExpQ d g : ℝ) (initExpA g)
              (initExpRhoMax d g) S.q jStar S.base +
          ENNReal.ofReal (c.AL (H : ℤ) *
            (Real.exp ((initExpQ d g : ℝ) *
              detIncrement P S.q S.base (S.base + (H : ℤ))) - 1)) := hprof0
      _ ≤ ENNReal.ofReal (c.AL (H : ℤ) * c.etaIn) +
          ENNReal.ofReal (c.AL (H : ℤ) *
            (Real.exp ((initExpQ d g : ℝ) * (d : ℝ) *
              Real.log (1 + c.deltaTerm)) - 1)) := add_le_add hfirst hsecond
      _ ≤ ENNReal.ofReal (c.etaOut / 2) := by
        have hlog : 0 ≤ Real.log (1 + c.deltaTerm) :=
          (Real.log_pos (by linarith only [c.deltaTerm_pos])).le
        have hexponent : 0 ≤ (initExpQ d g : ℝ) * (d : ℝ) *
            Real.log (1 + c.deltaTerm) := by
          exact mul_nonneg (mul_nonneg hQ.le (Nat.cast_nonneg d)) hlog
        rw [← ENNReal.ofReal_add (mul_nonneg hA c.etaIn_pos.le)
          (mul_nonneg hA (sub_nonneg.mpr (Real.one_le_exp hexponent)))]
        exact ENNReal.ofReal_le_ofReal (by
          linarith only [c.startup_share, c.terminal_profile, c.etaOut_pos])
  have hprofOut : portableProfile P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) ≤
      ENNReal.ofReal c.etaOut :=
    hprof.trans (ENNReal.ofReal_le_ofReal (by linarith only [c.etaOut_pos]))
  have hmaj := hmajor (S.base + (H : ℤ)) hbaseTerm le_rfl
  have hmajCport : portableHistory P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) S.q jStar (S.base + (H : ℤ)) ≤
      ENNReal.ofReal c.Cport *
        portableProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) := by
    exact hmaj.trans <| mul_le_mul'
      (ENNReal.ofReal_le_ofReal c.CportRaw_le) le_rfl
  have hCport : ENNReal.ofReal c.Cport *
        portableProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) ≤
      ENNReal.ofReal c.epsSt := by
    calc
      _ ≤ ENNReal.ofReal c.Cport * ENNReal.ofReal c.etaOut :=
        mul_le_mul_right hprofOut _
      _ = ENNReal.ofReal (c.Cport * c.etaOut) := by
        rw [ENNReal.ofReal_mul (le_trans zero_le_one c.one_le_Cport)]
      _ ≤ ENNReal.ofReal c.epsSt := ENNReal.ofReal_le_ofReal c.portable_share
  have hcentered : centeredHistory P (initExpQ d g : ℝ)
        (initExpRhoMax d g) S.q jStar (S.base + (H : ℤ)) ≤
      ENNReal.ofReal c.epsSt := by
    calc
      _ ≤ portableHistory P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) S.q jStar (S.base + (H : ℤ)) := by
        rw [portableHistory]
        exact le_self_add
      _ ≤ _ := hmajCport
      _ ≤ _ := hCport
  exact ⟨hprof, hmajCport, hCport, hcentered⟩

end

end Homogenization.HighContrast.Selection
