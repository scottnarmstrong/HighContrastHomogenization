/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Constants
import HCPoly.Provider.Selection.TransportAmortization

/-!
# The final cutoff and derived pre-law coefficients

The last Phase-0 choice enlarges the short-hop cutoff until both source
remainders are uniformly below their allowances.  The remaining coefficients
are then the displayed pre-law formulas of the global selector.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

noncomputable section

/-! ## Derived coefficients -/

/-- The determinant-charge coefficient of the selector. -/
def determinantCoefficient (CdetBar alphaX : ℝ) : ℝ := CdetBar * alphaX

/-- Defining equation for `determinantCoefficient`. -/
theorem determinantCoefficient_eq (CdetBar alphaX : ℝ) :
    determinantCoefficient CdetBar alphaX = CdetBar * alphaX := rfl

/-- The upper bound for the initial potential. -/
def potentialCoefficient (alphaW : ℝ) (bHop : ℕ) (alphaFresh alphaX Crad : ℝ) : ℝ :=
  alphaW * Real.log 2 + (bHop : ℝ) + alphaFresh + alphaX * Crad

/-- Defining equation for `potentialCoefficient`. -/
theorem potentialCoefficient_eq (alphaW : ℝ) (bHop : ℕ)
    (alphaFresh alphaX Crad : ℝ) :
    potentialCoefficient alphaW bHop alphaFresh alphaX Crad =
      alphaW * Real.log 2 + (bHop : ℝ) + alphaFresh + alphaX * Crad := rfl

/-- The transition-count coefficient obtained by summing the potential drop. -/
def transitionCoefficient (CF Cdet h c0 : ℝ) : ℝ :=
  (CF + Cdet * (h + 2) * Real.log 72) / c0

/-- Defining equation for `transitionCoefficient`. -/
theorem transitionCoefficient_eq (CF Cdet h c0 : ℝ) :
    transitionCoefficient CF Cdet h c0 =
      (CF + Cdet * (h + 2) * Real.log 72) / c0 := rfl

/-- The longest scale span used by one transition. -/
def executionSpan (h : ℤ) (l0 H : ℕ) : ℝ :=
  max (h : ℝ) (max (2 * (l0 : ℝ)) (H : ℝ))

/-- The synchronized checkpoint coefficient. -/
def checkpointCoefficient (B Chit : ℝ) : ℝ := B + Chit + 1

/-- Defining equation for `checkpointCoefficient`. -/
theorem checkpointCoefficient_eq (B Chit : ℝ) :
    checkpointCoefficient B Chit = B + Chit + 1 := rfl

/-- The upper coefficient for the returned terminal scale. -/
def selectionCoefficient (CR Lexec CN : ℝ) : ℝ := CR + Lexec * (CN + 3)

/-- Defining equation for `selectionCoefficient`. -/
theorem selectionCoefficient_eq (CR Lexec CN : ℝ) :
    selectionCoefficient CR Lexec CN = CR + Lexec * (CN + 3) := rfl

/-- The least execution-window coefficient required by all cell reads. -/
def executionMinimum (d : ℕ) (chop CR Lexec CN : ℝ) : ℝ :=
  CR + (Lexec + chop / Real.log 3) * (CN + 3) + 3 +
    (⌈(1 / 2 : ℝ) * Real.logb 3 d⌉₊ : ℝ)

/-- Defining equation for `executionMinimum`. -/
theorem executionMinimum_eq (d : ℕ) (chop CR Lexec CN : ℝ) :
    executionMinimum d chop CR Lexec CN =
      CR + (Lexec + chop / Real.log 3) * (CN + 3) + 3 +
        (⌈(1 / 2 : ℝ) * Real.logb 3 d⌉₊ : ℝ) := rfl

/-- The structural coefficient in the transport source amortization. -/
def transportCutoffAmplitude (Ctr Cd g Q Khop chop : ℝ) : ℝ :=
  2 * Ctr * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
    Real.exp (2 * Q * chop)

/-- Defining equation for `transportCutoffAmplitude`. -/
theorem transportCutoffAmplitude_eq (Ctr Cd g Q Khop chop : ℝ) :
    transportCutoffAmplitude Ctr Cd g Q Khop chop =
      2 * Ctr * (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) ^ Q *
        Real.exp (2 * Q * chop) := rfl

/-- The transport cutoff amplitude is positive for the structural inputs. -/
theorem transportCutoffAmplitude_pos {Ctr Cd g Q Khop chop : ℝ}
    (hCtr : 0 < Ctr) (hCd : 1 ≤ Cd) (hg : g < 1) (hKhop : 1 ≤ Khop) :
    0 < transportCutoffAmplitude Ctr Cd g Q Khop chop := by
  rw [transportCutoffAmplitude_eq]
  have hzeta : 0 < zetaG g := Transport.zero_lt_zetaG hg
  have hchi : 0 < chiG g := Transport.zero_lt_chiG hg
  have hinner : 0 < 1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by
    have : 0 ≤ 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by positivity
    linarith only [this]
  exact mul_pos
    (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2) hCtr)
      (Real.rpow_pos_of_pos hinner _))
    (Real.exp_pos _)

/-! ## Uniform power cutoff -/

/-- A linearly decreasing exponent makes a positive structural coefficient
uniformly small on every base `2 + Pi` with `Pi ≥ 1`. -/
theorem exists_uniform_transportCutoff {a C tau Q : ℝ} (ha : 0 < a)
    (hQ : 0 < Q) (hC : 0 < C) (htau : 0 < tau) :
    ∃ B : ℝ, 0 < B ∧ Q < a * B ∧
      ∀ Pi : ℝ, 1 ≤ Pi → C * (2 + Pi) ^ (Q - a * B) ≤ tau := by
  let s : ℝ := max 1 (Real.logb 3 (C / tau))
  have hs : 1 ≤ s := le_max_left _ _
  let B : ℝ := (Q + s) / a
  have hB : 0 < B := by dsimp [B]; positivity
  have haB : a * B = Q + s := by dsimp [B]; field_simp
  refine ⟨B, hB, by rw [haB]; linarith only [hs], fun Pi hPi => ?_⟩
  have hbase : (3 : ℝ) ≤ 2 + Pi := by linarith only [hPi]
  have hbase0 : (0 : ℝ) < 2 + Pi := by linarith only [hPi]
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hpow : (3 : ℝ) ^ s ≤ (2 + Pi) ^ s :=
    Real.rpow_le_rpow (by norm_num) hbase hs0
  have hpow0 : (0 : ℝ) < (3 : ℝ) ^ s := by positivity
  have hinv : (2 + Pi) ^ (-s) ≤ ((3 : ℝ) ^ s)⁻¹ := by
    rw [Real.rpow_neg hbase0.le]
    exact inv_anti₀ hpow0 hpow
  have hratio : C / tau ≤ (3 : ℝ) ^ s := by
    have hlog : Real.logb 3 (C / tau) ≤ s := le_max_right _ _
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hlog
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (div_pos hC htau)] at hp
  have hmul := mul_le_mul_of_nonneg_left hinv hC.le
  rw [haB, show Q - (Q + s) = -s by ring]
  refine hmul.trans ?_
  rw [mul_inv_le_iff₀ hpow0]
  rw [div_le_iff₀ htau] at hratio
  linarith only [hratio]

/-! ## The completed coefficient package -/

/-- The last Phase-0 cutoff and the coefficients derived after it. -/
structure CutoffConstants {d H Ltr : ℕ} {g epsCal etaDr etaProfBar deltaDetBar Cd : ℝ}
    {Khop Ctr : ℝ}
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr)
    (alphaFresh alphaX Crad c0 Chit Bmin : ℝ) where
  B : ℝ
  B_pos : 0 < B
  Bmin_le : Bmin ≤ B
  service_le : (c.h : ℝ) ≤ B
  shortCutoff_le : c.Bshort ≤ B
  rho_buffer : 2 * c.chop < initExpRhoDr g * (c.l0 : ℝ) * Real.log 3 / 2
  a_buffer : 2 * (initExpQ d g : ℝ) * c.chop <
    initExpA g * (c.l0 : ℝ) * Real.log 3 / 2
  rho_cutoff : 1 < initExpRhoDr g * B / 2
  moment_cutoff : (initExpQ d g : ℝ) < initExpA g * B / 2
  transport_uniform : ∀ Pi : ℝ, 1 ≤ Pi →
    transportCutoffAmplitude Ctr Cd g (initExpQ d g : ℝ) Khop c.chop *
      (2 + Pi) ^ ((initExpQ d g : ℝ) - initExpA g * B) ≤ c.tauTr
  CF : ℝ
  CN : ℝ
  Lexec : ℝ
  CR : ℝ
  Csel : ℝ
  CM : ℝ
  Cexec : ℝ
  CF_eq : CF = potentialCoefficient c.etaReady c.bHop alphaFresh alphaX Crad
  CN_eq : CN = transitionCoefficient CF
    (determinantCoefficient c.CdetBar alphaX) (c.h : ℝ) c0
  Lexec_eq : Lexec = executionSpan c.h c.l0 H
  CR_eq : CR = checkpointCoefficient B Chit
  Csel_eq : Csel = selectionCoefficient CR Lexec CN
  CM_eq : CM = executionMinimum d c.chop CR Lexec CN
  Cexec_eq : Cexec = max 1 CM
  CN_pos : 0 < CN
  Lexec_pos : 0 < Lexec
  Cexec_pos : 0 < Cexec
  Csel_pos : 0 < Csel
  CM_le_Cexec : CM ≤ Cexec

/-- The bridge-side source conclusion remains available at the enlarged final
cutoff. -/
theorem CutoffConstants.shortHopProvider {d H Ltr : ℕ}
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
    {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}
    (z : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin) (hd : 2 ≤ d) :
    ShortHopProviderData d g c.chop c.etaNew c.etaX Khop Ctr Cd c.l0
      c.tauSrc c.deltaShort c.etaPre z.B :=
  c.shortHopData.enlargeCutoff hd z.shortCutoff_le

/-- The transport amortization and final uniform cutoff give the printed
transport source allowance. -/
theorem CutoffConstants.transportAllowance {d H Ltr : ℕ}
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
    {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}
    (z : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCd : 1 ≤ Cd) (hKhop : 1 ≤ Khop)
    {Pi : ℝ} {r0 jStar : ℤ} {k : ℕ} {R : ℝ}
    (hPi : 1 ≤ Pi)
    (hentry : z.B * Real.logb 3 (2 + Pi) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hboot : R ≤ transportCutoffAmplitude Ctr Cd g (initExpQ d g : ℝ) Khop c.chop *
      (2 + Pi) ^ (initExpQ d g : ℝ) *
      (3 : ℝ) ^ (-initExpA g * ((r0 : ℝ) - (jStar : ℝ))) *
      Real.exp (-(k : ℝ) * (initExpA g * (c.l0 : ℝ) * Real.log 3 -
        2 * (initExpQ d g : ℝ) * c.chop))) :
    R ≤ c.tauTr := by
  have ha : 0 < initExpA g := initExpA_pos hg
  have hCamp : 0 < transportCutoffAmplitude Ctr Cd g (initExpQ d g : ℝ)
      Khop c.chop := transportCutoffAmplitude_pos c.transportData.Ctr_pos hCd hg.2 hKhop
  have hleft : 0 ≤ 2 * (initExpQ d g : ℝ) * c.chop :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) c.chop_pos.le
  have hstrict : 2 * (initExpQ d g : ℝ) * c.chop <
      initExpA g * (c.l0 : ℝ) * Real.log 3 := by
    linarith only [c.a_buffer, hleft]
  exact (transport_amortized_le_rpow ha hPi hCamp.le hentry hstrict hboot).trans
    (z.transport_uniform Pi hPi)

/-- The final cutoff and all displayed derived coefficients exist once the
progress weights and the two entry coefficients have been fixed. -/
theorem exists_cutoffConstants {d H Ltr : ℕ}
    {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
    (c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr)
    {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCd : 1 ≤ Cd) (hKhop : 1 ≤ Khop)
    (hCtr : 0 < Ctr)
    (halphaFresh : 0 < alphaFresh)
    (halphaX : 1 ≤ alphaX) (hCrad : 0 ≤ Crad) (hc0 : 0 < c0)
    (hChit : 0 ≤ Chit) (hBmin : 1 ≤ Bmin) :
    Nonempty (CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin) := by
  have ha : 0 < initExpA g := initExpA_pos hg
  have hQnat : 2 ≤ initExpQ d g := two_le_initExpQ hg
  have hQ : 0 < (initExpQ d g : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hQnat
  let Camp : ℝ := transportCutoffAmplitude Ctr Cd g
    (initExpQ d g : ℝ) Khop c.chop
  have hCamp : 0 < Camp := by
    dsimp [Camp]
    exact transportCutoffAmplitude_pos hCtr hCd hg.2 hKhop
  obtain ⟨Btr, _hBtr, _hQtr, htr⟩ :=
    exists_uniform_transportCutoff ha hQ hCamp c.tauTr_pos
  let Bmom : ℝ := 2 * ((initExpQ d g : ℝ) + 1) / initExpA g
  have hBmom : 0 < Bmom := by dsimp [Bmom]; positivity
  have hmoment : (initExpQ d g : ℝ) < initExpA g * Bmom / 2 := by
    dsimp [Bmom]
    rw [show initExpA g * (2 * ((initExpQ d g : ℝ) + 1) / initExpA g) / 2 =
      (initExpQ d g : ℝ) + 1 by field_simp]
    exact lt_add_one _
  let B : ℝ := max c.Bshort (max Bmin (max (c.h : ℝ) (max Bmom Btr)))
  have hshortB : c.Bshort ≤ B := le_max_left _ _
  have hBminB : Bmin ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hhB : (c.h : ℝ) ≤ B :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hBmomB : Bmom ≤ B :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  have hBtrB : Btr ≤ B :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)
  have hB : 0 < B := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hBmin) hBminB
  have hrho : 0 < initExpRhoDr g := initExpRhoDr_pos hg
  have hrhoCut : 1 < initExpRhoDr g * B / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hshortB hrho.le
    linarith only [c.Bshort_cutoff, hmul]
  have hmomentB : (initExpQ d g : ℝ) < initExpA g * B / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hBmomB ha.le
    linarith only [hmoment, hmul]
  have htransport : ∀ Pi : ℝ, 1 ≤ Pi → Camp *
      (2 + Pi) ^ ((initExpQ d g : ℝ) - initExpA g * B) ≤ c.tauTr := by
    intro Pi hPi
    have hbase1 : (1 : ℝ) ≤ 2 + Pi := by linarith only [hPi]
    have hexp : (initExpQ d g : ℝ) - initExpA g * B ≤
        (initExpQ d g : ℝ) - initExpA g * Btr := by
      have hmul := mul_le_mul_of_nonneg_left hBtrB ha.le
      linarith only [hmul]
    have hp := Real.rpow_le_rpow_of_exponent_le hbase1 hexp
    exact (mul_le_mul_of_nonneg_left hp hCamp.le).trans (htr Pi hPi)
  let CF : ℝ := potentialCoefficient c.etaReady c.bHop alphaFresh alphaX Crad
  let Cdet : ℝ := determinantCoefficient c.CdetBar alphaX
  let CN : ℝ := transitionCoefficient CF Cdet (c.h : ℝ) c0
  let Lexec : ℝ := executionSpan c.h c.l0 H
  let CR : ℝ := checkpointCoefficient B Chit
  let Csel : ℝ := selectionCoefficient CR Lexec CN
  let CM : ℝ := executionMinimum d c.chop CR Lexec CN
  let Cexec : ℝ := max 1 CM
  have hCF : 0 < CF := by
    dsimp [CF, potentialCoefficient]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hax : 0 ≤ alphaX * Crad := mul_nonneg (le_trans zero_le_one halphaX) hCrad
    have hb : (0 : ℝ) ≤ (c.bHop : ℝ) := Nat.cast_nonneg _
    have := mul_pos c.etaReady_pos hlog2
    linarith only [this, hb, halphaFresh, hax]
  have hCdet : 0 < Cdet := by
    dsimp [Cdet, determinantCoefficient]
    exact mul_pos c.CdetBar_pos (lt_of_lt_of_le zero_lt_one halphaX)
  have hh2 : 0 < (c.h : ℝ) + 2 := by
    have : (1 : ℝ) ≤ (c.h : ℝ) := by exact_mod_cast c.one_le_h
    linarith only [this]
  have hCN : 0 < CN := by
    dsimp [CN, transitionCoefficient]
    have hlog72 : 0 < Real.log 72 := Real.log_pos (by norm_num)
    have : 0 < CF + Cdet * ((c.h : ℝ) + 2) * Real.log 72 := by positivity
    exact div_pos this hc0
  have hLexec : 0 < Lexec := by
    dsimp [Lexec, executionSpan]
    have hh0 : (0 : ℝ) < (c.h : ℝ) := by
      have : (1 : ℝ) ≤ (c.h : ℝ) := by exact_mod_cast c.one_le_h
      linarith only [this]
    exact lt_of_lt_of_le hh0 (le_max_left _ _)
  have hCR : 0 < CR := by dsimp [CR, checkpointCoefficient]; linarith only [hB, hChit]
  have hCsel : 0 < Csel := by
    dsimp [Csel, selectionCoefficient]
    have hsum : 0 < CN + 3 := by linarith only [hCN]
    have : 0 < Lexec * (CN + 3) := mul_pos hLexec hsum
    linarith only [hCR, this]
  have hCexec : 0 < Cexec := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact ⟨{
    B := B, B_pos := hB, Bmin_le := hBminB, service_le := hhB,
    shortCutoff_le := hshortB, rho_buffer := c.rho_buffer, a_buffer := c.a_buffer,
    rho_cutoff := hrhoCut, moment_cutoff := hmomentB,
    transport_uniform := by simpa [Camp] using htransport,
    CF := CF, CN := CN, Lexec := Lexec, CR := CR, Csel := Csel, CM := CM,
    Cexec := Cexec, CF_eq := rfl, CN_eq := rfl, Lexec_eq := rfl, CR_eq := rfl,
    Csel_eq := rfl, CM_eq := rfl, Cexec_eq := rfl, Cexec_pos := hCexec,
    CN_pos := hCN, Lexec_pos := hLexec, Csel_pos := hCsel,
    CM_le_Cexec := le_max_right _ _ }⟩

end

end Selection
end HighContrast
end Homogenization
