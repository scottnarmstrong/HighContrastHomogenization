/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredCollectiveConclusion
import HCPoly.Provider.Transport.FreshMajorantProfile
import HCPoly.Provider.Transport.InheritedMajorantMax
import HCPoly.Provider.Transport.BelowStartMajorantProfile
import HCPoly.Provider.Transport.FiniteMaxCoefficient

/-!
# Fixed constants for the centered half of grid transport

These constants depend only on binders occurring before the buffer, law,
reference block, and grid witnesses in the frozen statement.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

noncomputable section

/-- Coefficient of the simultaneous positive-gap estimate. -/
def centeredCollectiveGapConst (d Q : ℕ) : ℝ :=
  (((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ *
      (1 +
        (2 * (1 + (2 : ℝ) ^ ((Q : ℝ) - 2) +
          (2 : ℝ) ^ ((Q : ℝ) - 2) *
            (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹))) ^ ((Q : ℝ))⁻¹ +
        (2 * (1 + (2 : ℝ) ^ ((Q : ℝ) - 2) +
          (2 : ℝ) ^ ((Q : ℝ) - 2) *
            (2 * (d : ℝ)) ^ (1 - ((Q : ℝ))⁻¹))) ^
              ((Q : ℝ) - 1)⁻¹)) ^ (Q : ℝ)) *
    (2 : ℝ) ^ ((Q : ℝ) - 1)

/-- Real coefficient of the three-maximum Schatten split. -/
def centeredMajorantSplitConst (d Q : ℕ) : ℝ :=
  (((2 * (d : ℝ)) ^ 2) ^ (Q : ℝ)) *
    (((2 : ℝ) ^ ((Q : ℝ) - 1)) ^ 2)

/-- Fixed inherited-row coefficient. -/
def centeredInheritedConst (d Q : ℕ) (rhoMax Khop : ℝ) : ℝ :=
  (((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * (4 / 3 : ℝ) *
      (max 1 (6 * (d : ℝ) * Real.sqrt d * Khop) *
        (1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax)))))) ^ (Q : ℝ) *
    (2 + Real.sqrt d * Khop) ^ d)

/-- Fixed fresh-row coefficient, uniform for `etaX ≤ 1 / 4`. -/
def centeredFreshConst (d Q : ℕ) (a Khop : ℝ) : ℝ :=
  (((2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * (4 / 3 : ℝ)) *
      (2 * (d : ℝ) *
        ((2 * (Q : ℝ) +
          4 * IndependentSums.rosenthalBennettIntegralConst *
            Real.sqrt (Q : ℝ)) * Real.sqrt ((3 : ℝ) ^ d))) *
      Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop *
        (Real.sqrt d * Khop) ^ d) *
      (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) ^ (Q : ℝ) *
    (1 / (1 - (3 : ℝ) ^
      (-(((d : ℝ) + 1) / 2 - a / (Q : ℝ))))) ^ (Q : ℝ)

/-- Fixed coefficient of the shared below-start maximum. -/
def centeredBelowStartConst (d Q : ℕ) (Khop : ℝ) : ℝ :=
  (4 * (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) ^ (Q : ℝ) *
    (18 * (d : ℝ) * Real.sqrt d * Khop) ^ (Q : ℝ)

/-- One profile/bridge constant dominating the three centered profile
coefficients. -/
def centeredTransportProfileConst (d Q : ℕ) (rhoMax a Khop CgapP CgapE : ℝ) : ℝ :=
  centeredCollectiveGapConst d Q *
      (centeredMajorantSplitConst d Q *
          (centeredInheritedConst d Q rhoMax Khop +
            centeredFreshConst d Q a Khop) +
        2 * CgapP) +
    centeredCollectiveGapConst d Q * (2 * CgapE) + 1

/-- Source constant dominating the split below-start row and deterministic
gap source row. -/
def centeredTransportSourceConst (d Q : ℕ) (Khop CgapS : ℝ) : ℝ :=
  centeredCollectiveGapConst d Q *
    (centeredMajorantSplitConst d Q * centeredBelowStartConst d Q Khop +
      2 * CgapS)

/-- All five fixed component constants are nonnegative in the transport
parameter range. -/
theorem centered_component_constants_nonnegative
    (d Q : ℕ)
    {rhoMax a Khop : ℝ} (hrho : rhoMax < 1)
    (hkernel : 0 < ((d : ℝ) + 1) / 2 - a / (Q : ℝ))
    (hKhop : 1 ≤ Khop) :
    0 ≤ centeredCollectiveGapConst d Q ∧
      0 ≤ centeredMajorantSplitConst d Q ∧
      0 ≤ centeredInheritedConst d Q rhoMax Khop ∧
      0 ≤ centeredFreshConst d Q a Khop ∧
      0 ≤ centeredBelowStartConst d Q Khop := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hKhop0 : 0 ≤ Khop := le_trans zero_le_one hKhop
  have hrhoDen : 0 < 1 - (3 : ℝ) ^ (-(1 - rhoMax)) := by
    have hexp : -(1 - rhoMax) < 0 := by linarith only [hrho]
    have hpow := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
      (by norm_num) hexp
    linarith only [hpow]
  have hfreshDen : 0 < 1 - (3 : ℝ) ^
      (-(((d : ℝ) + 1) / 2 - a / (Q : ℝ))) := by
    have hexp : -(((d : ℝ) + 1) / 2 - a / (Q : ℝ)) < 0 := by
      linarith only [hkernel]
    have hpow := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ))
      (by norm_num) hexp
    linarith only [hpow]
  have hRB : 0 ≤ IndependentSums.rosenthalBennettIntegralConst := by
    simp only [IndependentSums.rosenthalBennettIntegralConst]
    positivity
  constructor
  · simp only [centeredCollectiveGapConst]
    positivity
  constructor
  · simp only [centeredMajorantSplitConst]
    positivity
  constructor
  · simp only [centeredInheritedConst]
    positivity
  constructor
  · simp only [centeredFreshConst]
    positivity
  · simp only [centeredBelowStartConst]
    positivity

/-- The final two centered constants are nonnegative and dominate the three
coefficients consumed by `centered_collective_conclusion`. -/
theorem centered_final_constants_data
    (d Q : ℕ) {rhoMax a Khop CgapP CgapE CgapS : ℝ}
    (hKgap : 0 ≤ centeredCollectiveGapConst d Q)
    (hKsplit : 0 ≤ centeredMajorantSplitConst d Q)
    (hCinh : 0 ≤ centeredInheritedConst d Q rhoMax Khop)
    (hCfresh : 0 ≤ centeredFreshConst d Q a Khop)
    (hCsource : 0 ≤ centeredBelowStartConst d Q Khop)
    (hCgapP : 0 ≤ CgapP) (hCgapE : 0 ≤ CgapE) (hCgapS : 0 ≤ CgapS) :
    0 ≤ centeredTransportProfileConst d Q rhoMax a Khop CgapP CgapE ∧
      0 ≤ centeredTransportSourceConst d Q Khop CgapS ∧
      centeredCollectiveGapConst d Q *
          (centeredMajorantSplitConst d Q *
              (centeredInheritedConst d Q rhoMax Khop +
                centeredFreshConst d Q a Khop) +
            2 * CgapP) ≤
        centeredTransportProfileConst d Q rhoMax a Khop CgapP CgapE ∧
      centeredCollectiveGapConst d Q * (2 * CgapE) ≤
        centeredTransportProfileConst d Q rhoMax a Khop CgapP CgapE ∧
      centeredCollectiveGapConst d Q *
          (centeredMajorantSplitConst d Q * centeredBelowStartConst d Q Khop +
            2 * CgapS) ≤ centeredTransportSourceConst d Q Khop CgapS := by
  have hprofTerm : 0 ≤ centeredCollectiveGapConst d Q *
      (centeredMajorantSplitConst d Q *
          (centeredInheritedConst d Q rhoMax Khop +
            centeredFreshConst d Q a Khop) + 2 * CgapP) := by
    positivity
  have hbridgeTerm : 0 ≤
      centeredCollectiveGapConst d Q * (2 * CgapE) := by positivity
  have hsourceTerm : 0 ≤ centeredCollectiveGapConst d Q *
      (centeredMajorantSplitConst d Q * centeredBelowStartConst d Q Khop +
        2 * CgapS) := by positivity
  simp only [centeredTransportProfileConst, centeredTransportSourceConst]
  constructor
  · positivity
  constructor
  · exact hsourceTerm
  constructor
  · linarith only [hbridgeTerm]
  constructor
  · linarith only [hprofTerm]
  · exact le_rfl

end

end Transport
end HighContrast
end Homogenization
