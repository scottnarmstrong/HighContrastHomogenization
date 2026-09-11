/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchFixed
import HCPoly.Provider.Selection.InitialCheckpoint
import HCPoly.Provider.Selection.TerminalGeometry

/-!
# Constants chosen before the coefficient law

The selector's structural constants, progress weights, and initial-checkpoint
provider are chosen before a coefficient law is read.  The final scale buffer
is then enlarged only after its prescribed lower bound is supplied.
-/

namespace Homogenization.HighContrast.Selection

noncomputable section

private theorem fixedSpanLoad_nonneg_of_pos {A : ℝ} (hA : 0 < A) :
    0 ≤ fixedSpanLoad A := by
  rw [fixedSpanLoad_eq]
  exact Real.log_nonneg (by linarith only [hA])

private theorem driftIndexLoad_nonneg_of_pos {d : ℕ} {eta : ℝ}
    (heta : 0 < eta) : 0 ≤ driftIndexLoad d eta := by
  rw [driftIndexLoad_eq]
  have hquot : 0 ≤ 2 * (d : ℝ) / eta := by positivity
  have harg : 1 ≤ 1 + 2 * (d : ℝ) / eta := by
    linarith only [hquot]
  have hlog : 0 ≤ Real.logb 2 (1 + 2 * (d : ℝ) / eta) :=
    Real.logb_nonneg (by norm_num) harg
  linarith only [hlog]

private theorem startupBranchLoad_nonneg {d H Ltr : ℕ}
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr) :
    0 ≤ startupBranchLoad c := by
  rw [startupBranchLoad_eq]
  have hspan := fixedSpanLoad_nonneg_of_pos (c.AL_pos c.h c.one_le_h)
  have hdrift := driftIndexLoad_nonneg_of_pos (d := d) c.etaPre_pos
  exact add_nonneg (add_nonneg hspan hdrift) (Nat.cast_nonneg _)

private theorem shortFailureBranchLoad_nonneg {d H Ltr : ℕ}
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr) :
    0 ≤ shortFailureBranchLoad c := by
  rw [shortFailureBranchLoad_eq]
  have hl0 : 1 ≤ c.l0 := c.transportData.one_le_Ltr.trans
    ((le_max_right c.Lcommon Ltr).trans c.l0_lower)
  have hspan := fixedSpanLoad_nonneg_of_pos
    (c.AL_pos (2 * (c.l0 : ℤ)) (by exact_mod_cast (show 1 ≤ 2 * c.l0 by omega)))
  have hdrift := driftIndexLoad_nonneg_of_pos (d := d) c.etaPre_pos
  exact add_nonneg hspan hdrift

private theorem hopBranchLoad_nonneg {d H Ltr : ℕ}
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr) :
    0 ≤ hopBranchLoad c := by
  rw [hopBranchLoad_eq]
  have hratio : 0 ≤ c.etaIn / c.etaReady :=
    div_nonneg c.etaIn_pos.le c.etaReady_pos.le
  have harg : 1 ≤ 1 + c.etaIn / c.etaReady := by
    linarith only [hratio]
  have hlog : 0 ≤ Real.log (1 + c.etaIn / c.etaReady) := Real.log_nonneg harg
  exact add_nonneg (mul_nonneg c.etaReady_pos.le hlog) (Nat.cast_nonneg _)

private theorem terminalFailureBranchLoad_nonneg {d H Ltr : ℕ}
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr) :
    0 ≤ terminalFailureBranchLoad c := by
  rw [terminalFailureBranchLoad_eq]
  have hspanIndex : (1 : ℤ) ≤ max (H : ℤ) c.h :=
    c.one_le_h.trans (le_max_right _ _)
  have hspan := fixedSpanLoad_nonneg_of_pos
    (c.AL_pos (max (H : ℤ) c.h) hspanIndex)
  have hdrift := driftIndexLoad_nonneg_of_pos (d := d) c.etaPre_pos
  exact add_nonneg (add_nonneg hspan hdrift) (Nat.cast_nonneg _)

private theorem fixedBranchSlope_nonneg (d : ℕ) (g : ℝ) :
    0 ≤ fixedBranchSlope d g := by
  rw [fixedBranchSlope_eq]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The selector data fixed before the law exists, and every later lower
buffer admits a cutoff package with the same transition coefficient. -/
theorem exists_globalSelection_preLaw
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (epsCal etaDr etaProfBar deltaDetBar : ℝ)
    (hepsCal : 0 < epsCal) (hetaDr : 0 < etaDr)
    (hetaProf : 0 < etaProfBar) (hdeltaDet : 0 < deltaDetBar)
    (H : ℕ) (hH : 4 ≤ H) (Cd : ℝ) (hCd : 1 ≤ Cd)
    (Khop : ℝ) (hKhop : 1 ≤ Khop)
    (hhop : ∀ l : ℤ, (kZero d : ℤ) ≤ l → ∀ m₀ m₁ : Mat d,
      m₀.PosDef → m₁.PosDef → projDist m₀ m₁ ≤ (1 : ℝ) →
        gridRatio (roundedGrid l m₀) (roundedGrid l m₁) ≤ Khop)
    (Ltr : ℕ) (Ctr : ℝ)
    (transportData : TransportProviderData d g (initExpQ d g)
      (initExpRhoMax d g) (initExpA g) Khop Ctr Ltr) :
    ∃ c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr,
      c.chop = 1 ∧
      ∃ Chit : ℝ, InitialProviderData c c.etaInit Chit ∧
        ∃ w : ProgressWeights c (startupBranchLoad c) (shortFailureBranchLoad c)
            (hopBranchLoad c) (terminalFailureBranchLoad c) (fixedBranchSlope d g),
          ∀ Bmin : ℝ, 1 ≤ Bmin →
            Nonempty (CutoffConstants c w.alphaFresh w.alphaX
              (2 * (d : ℝ) * Real.log 12) w.c0 Chit Bmin) := by
  obtain ⟨c, hchop⟩ := exists_selConstants d hd hg hepsCal hetaDr hetaProf
    hdeltaDet H hH Cd hCd 1 one_pos Khop hKhop hhop Ltr Ctr transportData
    1 one_pos
  obtain ⟨Chit, hinit⟩ := exists_initialProviderData hd hg c c.etaInit_pos
  obtain ⟨w⟩ := exists_progressWeights
    (startupBranchLoad_nonneg c) (shortFailureBranchLoad_nonneg c)
    (hopBranchLoad_nonneg c) (terminalFailureBranchLoad_nonneg c)
    (fixedBranchSlope_nonneg d g)
  refine ⟨c, hchop, Chit, hinit, w, ?_⟩
  intro Bmin hBmin
  exact exists_cutoffConstants c hg hCd hKhop transportData.Ctr_pos
    w.alphaFresh_pos (le_trans one_le_two w.two_le_alphaX) (by positivity) w.c0_pos
    hinit.Chit_pos.le hBmin

end

end Homogenization.HighContrast.Selection
