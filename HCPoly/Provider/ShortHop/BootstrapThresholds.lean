/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.ShortHop.CutoffCoefficient
import HCPoly.Provider.ShortHop.OrderedChoice

/-!
# The ordered choice with the bootstrap constant inside the cutoff clause

The cutoff coefficient `B` of `p.successful.short.bridge` is chosen
last, against the source allowance, and its job is to make the amortized source
bound along the sequence of geometry changes fall below that allowance uniformly
in the reference aspect ratio.  That amortized bound carries
the structural constant of the bootstrap, not the two-grid constant alone, so the
uniform clause the ordered choice must export reads that structural constant.

The statement below is the ordered choice with the structural constant a
parameter, presented as a function of the hop length because the hop length is
chosen first and the bootstrap constant depends on it — through the fixed factors
`e^{2c_hop - ρ_dr ℓ₀ log3/2}` and `3^{ρ_dr ℓ₀}` that the amortization collects.
Everything else is unchanged: the five thresholds in the printed order, the four
constants requirements, and the two threshold inequalities on the six envelopes.

Read at the constant one this is the earlier form, so nothing is lost; read at
the bootstrap constant it is what closes the source hypotheses of the successful
short test.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

noncomputable section

/-- **The ordered choice, with the bootstrap constant in the cutoff clause.**
All five thresholds, in the printed order, with the four constants requirements,
the two threshold inequalities, and the uniform source bound at a structural
constant that may depend on the hop length. -/
theorem exists_short_thresholds_of_const (d Lcommon Ltr : ℕ) {g chop etaNew etaX C Khop : ℝ}
    (Cboot : ℕ → ℝ) (hCboot : ∀ n : ℕ, 0 < Cboot n) (hg : g < 1) (hetaNew : 0 < etaNew)
    (hetaX : 0 < etaX) (hC : 0 < C) (hKhop : 1 ≤ Khop) :
    ∃ l0 : ℕ, max Lcommon Ltr ≤ l0 ∧
      ∃ tauSrc : ℝ, 0 < tauSrc ∧
        ∃ deltaShort : ℝ, 0 < deltaShort ∧
          ∃ etaPre : ℝ, 0 < etaPre ∧
            ∃ B : ℝ, 0 < B ∧
              C * (1 + Real.log Khop) ≤ (l0 : ℝ) ∧
              C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2 ∧
              2 * chop < initExpRhoDr g * (l0 : ℝ) * Real.log 3 / 2 ∧
              1 < initExpRhoDr g * B / 2 ∧
              (∀ b delta R₁ R₂ R₃ : ℝ,
                0 ≤ b → b ≤ etaPre → 0 ≤ delta → delta ≤ deltaShort →
                0 ≤ R₁ → R₁ ≤ tauSrc → 0 ≤ R₂ → R₂ ≤ tauSrc →
                0 ≤ R₃ → R₃ ≤ tauSrc →
                shortBridgeErr d C Khop (initExpRhoDr g) (l0 : ℤ) b delta R₁ R₂ ≤ etaX ∧
                  shortNewDrift d C Khop (initExpRhoDr g) (l0 : ℤ) b delta R₂ R₃ ≤
                    etaNew) ∧
              ∀ Pi : ℝ, 1 ≤ Pi →
                Cboot l0 * (2 + Pi) ^ (1 - initExpRhoDr g * B / 2) ≤ tauSrc := by
  obtain ⟨l0, hl0common, hl0log, hl0half, hl0strict, hbr0, hnd0⟩ :=
    exists_shortScale d Lcommon Ltr hg hetaNew hetaX hC hKhop
  have hcast : (((l0 : ℕ) : ℤ) : ℝ) = (l0 : ℝ) := by push_cast; ring
  have hden : C * Khop * (3 : ℝ) ^ (-(((l0 : ℕ) : ℤ) : ℝ)) ≤ 1 / 2 := by
    rw [hcast]; exact hl0half
  obtain ⟨tau, htau, hthr⟩ :=
    exists_shortThresholds d hC.le (by linarith only [hKhop]) hden hetaX hetaNew hbr0 hnd0
  obtain ⟨B, hB, hBstrict, hBunif⟩ :=
    exists_cutoff (initExpRhoDr_pos hg) (hCboot l0) htau
  exact ⟨l0, hl0common, tau, htau, tau, htau, tau, htau, B, hB, hl0log, hl0half,
    hl0strict, hBstrict, hthr, hBunif⟩

end

end ShortHop
end HighContrast
end Homogenization
