/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TerminalCalibration

/-!
# Analytic conclusions at the terminal selector state

The exact and phase invariants are consumed here to assemble the calibration,
determinant, drift, profile, full-history, and centered-history groups returned
by the global selector.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- The four analytic property groups of the returned terminal tuple. -/
theorem terminal_phase_outputs (hd : 2 ≤ d) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (hetaProfBar : etaProfBar ≤ 1) (hH : 4 ≤ H)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    {E0 : BlockMat d} (hE0 : IsSymmetricBlockMat E0)
    (hE0pd : Book.Ch02.BlockPosDef E0) (hcandidate : S.candidate = some E0)
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
    (hmono : ∀ j T : ℤ, jStar ≤ j → j ≤ T →
      T ≤ S.base + (H : ℤ) →
        BlockMatLoewnerLE (adaptedMean P S.q T) (adaptedMean P S.q j))
    (hpass : adaptedDetRoot P S.q S.base <
      (1 + c.deltaTerm) * adaptedDetRoot P S.q (S.base + (H : ℤ))) :
    (BlockMatLoewnerLE (blockScale (1 - epsCal) E0)
          (adaptedMean P S.q S.base) ∧
        BlockMatLoewnerLE (adaptedMean P S.q S.base)
          (blockScale (1 + epsCal) E0) ∧
        adaptedDetRoot P S.q S.base <
          (1 + c.deltaTerm) * adaptedDetRoot P S.q (S.base + (H : ℤ)) ∧
        linearDrift P (initExpRhoDr g) S.q jStar S.base +
            linearDrift P (initExpRhoDr g) S.q jStar (S.base + (H : ℤ)) ≤
          etaDr) ∧
      (portableHistory P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) S.q jStar S.base ≤ ENNReal.ofReal c.etaIn ∧
        portableProfile P (initExpQ d g : ℝ) (initExpA g)
            (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) ≤
          ENNReal.ofReal c.etaOut ∧
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
            (S.base + (H : ℤ)) ≤ ENNReal.ofReal c.epsSt) := by
  have hcal := terminal_calibration_bounds (c := c) hE0 hE0pd hcandidate
    hexact hterminal
  have hdrift := terminal_determinant_drift_bounds (c := c) hd hg hexact
    hterminal hpos hmono hpass
  have hhist : portableHistory P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) S.q jStar S.base ≤ ENNReal.ofReal c.etaIn := by
    rw [← terminal_stateHistory_eq hexact hterminal]
    exact hterminal.2.2.2.1
  obtain ⟨hprofileHalf, hmajor, hsmall, hcentered⟩ :=
    terminal_profile_history_bounds (c := c) hd hg hetaProfBar hH hP hunit hq
      hexact hterminal hfin hpos hmom hpass
  have hprofile : portableProfile P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) S.q jStar S.base (S.base + (H : ℤ)) ≤
      ENNReal.ofReal c.etaOut :=
    hprofileHalf.trans
      (ENNReal.ofReal_le_ofReal (by linarith only [c.etaOut_pos]))
  exact ⟨⟨hcal.1, hcal.2, hdrift.1, hdrift.2⟩,
    hhist, hprofile, hmajor, hsmall, hcentered⟩

end

end Homogenization.HighContrast.Selection
