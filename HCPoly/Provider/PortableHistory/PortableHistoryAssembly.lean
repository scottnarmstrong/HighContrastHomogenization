/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.MajorizationAssembly
import HCPoly.Provider.PortableHistory.PropagationConstant
import HCPoly.Provider.PortableHistory.ServiceAssembly
import HCPoly.Provider.PortableHistory.StartupAssembly

/-!
# The portable complete history

The nine displays of `p.fixed.geometry.one.grid.propagation` are collected here into the
proposition's own statement.

The three constants are exhibited.  The majorization constant is the sum of the
geometric weights,

`C_0 = (1 - 3^{-a})^{-1}`,

and depends on the decay rate alone.  The service constant is the majorization
constant plus the two contributions of one service window -- the `h` nonlinear
scales it opens and the `h` centred scales it closes at the gain of the
recurrence --

`C = (1 - 3^{-a})^{-1} + h + h2^{Q-1}C_{\rm rec}^Q2^Q`.

The propagation and startup displays share one constant in the statement,
while each is proved with its own: the propagation constant of the induction
bounding the new fluctuation terms and the startup constant of
`e.fixed.geometry.profile.startup`.  Their maximum serves both, because a
propagation-shaped estimate is monotone in its constant.  Every constant
depends only on `d, Q, a, C_{\rm rec}, h` and, for the last, the number `L` of
scales propagated.

The hypothesis `hrec` is exactly the recurrence's conclusion, at the value
`C_{\rm rec}` for which the contraction factor `λ_port` is admissible; the
service, propagation, and startup displays consume it, and the admissibility
hypothesis `λ_port ≤ 1/4` is read by the propagation display alone.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- **`p.fixed.geometry.one.grid.propagation`.**  The portable profile carries the whole
earlier history as one checkpoint datum: it agrees with the complete history at
its own checkpoint, majorizes it at every later scale of the window, contracts
over one service length with no scale-independent error, has synchronized
charges of bounded multiplicity, and propagates over a bounded number of scales
from a unit-size profile or from a unit-size checkpoint. -/
theorem portable_history_assembly
    (d : ℕ) (hd : 2 ≤ d) (Q : ℕ) (hQ : 2 ≤ Q) (hQeven : Even Q)
    (a rhoMax : ℝ) (ha : 0 < a) (hrhoMax : 0 < rhoMax)
    (hadm : a ≤ (Q : ℝ) * rhoMax - (d : ℝ))
    (Crec : ℝ) (hCrec : 0 < Crec)
    (hrec :
      ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d)),
        MeasureTheory.IsProbabilityMeasure P →
        HCPoly.Frozen.IsStationaryLaw P →
        HCPoly.Frozen.IsUnitRangeLaw P →
        ∀ (l : ℤ) (q : Homogenization.Mat d),
          Homogenization.HighContrast.IsRoundedGrid l q →
          ∀ j h : ℤ, l ≤ j → 1 ≤ h →
            Homogenization.Book.Ch02.BlockPosDef
              (Homogenization.HighContrast.adaptedMean P q j) →
            Homogenization.Book.Ch02.BlockPosDef
              (Homogenization.HighContrast.adaptedMean P q (j + h)) →
            Homogenization.HighContrast.HasFiniteAdaptedMean P q j →
            Homogenization.HighContrast.HasFiniteAdaptedMean P q (j + h) →
            Homogenization.HighContrast.centeredMoment P (Q : ℝ) q j ≠ ⊤ →
            Homogenization.HighContrast.centeredMoment P (Q : ℝ) q (j + h) ≠ ⊤ →
            0 ≤ Homogenization.HighContrast.detIncrement P q j (j + h) ∧
              Homogenization.HighContrast.centeredMoment P (Q : ℝ) q (j + h) ≤
                ENNReal.ofReal
                    (Crec * (3 : ℝ) ^ (-(h : ℝ) * (d : ℝ) / 2) *
                      Real.exp
                        (Homogenization.HighContrast.detIncrement P q j (j + h))) *
                  Homogenization.HighContrast.centeredMoment P (Q : ℝ) q j +
                ENNReal.ofReal
                  (Crec *
                    Homogenization.HighContrast.gainPhi (Q : ℝ)
                      (Homogenization.HighContrast.detIncrement P q j (j + h))))
    (h : ℤ) (hh : 1 ≤ h)
    (hlam : Homogenization.HighContrast.lambdaPort d (Q : ℝ) a Crec h ≤ 1 / 4) :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∃ CL : ℤ → ℝ, (∀ L : ℤ, 1 ≤ L → 0 < CL L) ∧
        ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d)),
          MeasureTheory.IsProbabilityMeasure P →
          HCPoly.Frozen.IsStationaryLaw P →
          HCPoly.Frozen.IsUnitRangeLaw P →
          ∀ (l : ℤ) (q : Homogenization.Mat d),
            Homogenization.HighContrast.IsRoundedGrid l q →
            ∀ jStar b TMax : ℤ, l ≤ jStar → jStar ≤ b → b ≤ TMax →
              (∀ j : ℤ, jStar ≤ j → j ≤ TMax →
                Homogenization.HighContrast.HasFiniteAdaptedMean P q j) →
              (∀ j : ℤ, jStar ≤ j → j ≤ TMax →
                Homogenization.Book.Ch02.BlockPosDef
                  (Homogenization.HighContrast.adaptedMean P q j)) →
              (∀ j : ℤ, jStar ≤ j → j ≤ TMax →
                Homogenization.HighContrast.centeredMoment P (Q : ℝ) q j ≠ ⊤) →
              -- the mean order, the determinant increment, and `I ≤ P_{j,T}^q`
              (∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ TMax →
                  Homogenization.BlockMatLoewnerLE
                    (Homogenization.HighContrast.adaptedMean P q T)
                    (Homogenization.HighContrast.adaptedMean P q j)) ∧
                (∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ TMax →
                  0 ≤ Homogenization.HighContrast.detIncrement P q j T) ∧
                (∀ j T : ℤ, jStar ≤ j → j ≤ T → T ≤ TMax →
                  Homogenization.BlockMatLoewnerLE
                    (Homogenization.Book.Ch02.blockIdentity d)
                    (Homogenization.HighContrast.relMean P q j T)) ∧
                -- `𝒫_q(b;b) = 𝓗_q(b)`
                Homogenization.HighContrast.portableProfile P (Q : ℝ) a rhoMax q
                    jStar b b =
                  Homogenization.HighContrast.portableHistory P (Q : ℝ) a rhoMax q
                    jStar b ∧
                -- majorization
                (∀ T : ℤ, b ≤ T → T ≤ TMax →
                  Homogenization.HighContrast.portableHistory P (Q : ℝ) a rhoMax q
                      jStar T ≤
                    ENNReal.ofReal C₀ *
                      Homogenization.HighContrast.portableProfile P (Q : ℝ) a rhoMax
                        q jStar b T) ∧
                -- service
                (∀ T : ℤ, b + h ≤ T → T + h ≤ TMax →
                  Homogenization.HighContrast.portableProfile P (Q : ℝ) a rhoMax q
                      jStar b (T + h) ≤
                    ENNReal.ofReal
                        (Homogenization.HighContrast.lambdaPort d (Q : ℝ) a Crec h *
                          Real.exp
                            ((Q : ℝ) *
                              Homogenization.HighContrast.synchCharge P q h T)) *
                        Homogenization.HighContrast.portableProfile P (Q : ℝ) a
                          rhoMax q jStar b T +
                      ENNReal.ofReal
                        (C *
                          (Real.exp
                              ((Q : ℝ) *
                                Homogenization.HighContrast.synchCharge P q h T) -
                            1))) ∧
                -- multiplicity of the synchronized charges
                (∀ (T₀ : ℤ) (K : ℕ), b + h ≤ T₀ → 1 ≤ K →
                  T₀ + (K : ℤ) * h ≤ TMax →
                  ∑ k ∈ Finset.range K,
                      Homogenization.HighContrast.synchCharge P q h (T₀ + k * h) ≤
                    (h : ℝ) *
                      Homogenization.HighContrast.detIncrement P q (T₀ + 1 - h)
                        (T₀ + K * h)) ∧
                -- propagation over a bounded number of scales
                (∀ L T : ℤ, 1 ≤ L → b + h ≤ T → T + L ≤ TMax →
                  Homogenization.HighContrast.portableProfile P (Q : ℝ) a rhoMax q
                      jStar b T ≤ 1 →
                  Homogenization.HighContrast.portableProfile P (Q : ℝ) a rhoMax q
                      jStar b (T + L) ≤
                    ENNReal.ofReal (CL L) *
                        Homogenization.HighContrast.portableProfile P (Q : ℝ) a
                          rhoMax q jStar b T +
                      ENNReal.ofReal
                        (CL L *
                          (Real.exp
                              ((Q : ℝ) *
                                Homogenization.HighContrast.detIncrement P q T
                                  (T + L)) -
                            1))) ∧
                -- startup at the checkpoint
                (∀ L : ℤ, 1 ≤ L → b + L ≤ TMax →
                  Homogenization.HighContrast.portableHistory P (Q : ℝ) a rhoMax q
                      jStar b ≤ 1 →
                  Homogenization.HighContrast.portableProfile P (Q : ℝ) a rhoMax q
                      jStar b (b + L) ≤
                    ENNReal.ofReal (CL L) *
                        Homogenization.HighContrast.portableHistory P (Q : ℝ) a
                          rhoMax q jStar b +
                      ENNReal.ofReal
                        (CL L *
                          (Real.exp
                              ((Q : ℝ) *
                                Homogenization.HighContrast.detIncrement P q b
                                  (b + L)) -
                            1)))
    := by
  have : NeZero d := ⟨by omega⟩
  -- the parity of `Q` and the positivity of `ρ_max` are premises of the
  -- recurrence and of the centred history; the displays below read neither
  have _hQeven := hQeven
  have _hrhoMax := hrhoMax
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith only [hQR]
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith only [hQR]
  have hCrec0 : (0 : ℝ) ≤ Crec := hCrec.le
  have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := by linarith only [hh1]
  have hC₀ : (0 : ℝ) < 1 / (1 - (3 : ℝ) ^ (-a)) := majorization_const_pos ha
  -- the gain factor of the recurrence, at the service length
  have hgain : (0 : ℝ) < 2 ^ ((Q : ℝ) - 1) * Crec ^ (Q : ℝ) * 2 ^ (Q : ℝ) :=
    mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hCrec _)) (Real.rpow_pos_of_pos (by norm_num) _)
  have hservice : (0 : ℝ) ≤
      (h : ℝ) * (2 ^ ((Q : ℝ) - 1) * Crec ^ (Q : ℝ) * 2 ^ (Q : ℝ)) :=
    mul_nonneg hh0 hgain.le
  refine
    ⟨1 / (1 - (3 : ℝ) ^ (-a)),
      1 / (1 - (3 : ℝ) ^ (-a)) + (h : ℝ) +
        (h : ℝ) * (2 ^ ((Q : ℝ) - 1) * Crec ^ (Q : ℝ) * 2 ^ (Q : ℝ)),
      hC₀, by linarith only [hC₀, hh1, hservice],
      fun L =>
        max
          (1 + (L : ℝ) *
              ((3 : ℝ) ^ (a * (h : ℝ)) +
                2 * (2 ^ ((Q : ℝ) - 1) * Crec ^ (Q : ℝ) * 2 ^ (Q : ℝ) *
                  (1 + (Q : ℝ) *
                      Real.exp ((Q : ℝ) *
                        ((1 + (3 : ℝ) ^ (a * (h : ℝ))) ^ ((Q : ℝ))⁻¹ - 1)) *
                    (3 : ℝ) ^ (a * (h : ℝ))))) +
            1 / (1 - (3 : ℝ) ^ (-a)) + (L : ℝ))
          (1 + (L : ℝ) + (L : ℝ) * (2 * (d : ℝ)) * (2 ^ ((Q : ℝ) - 1) * Crec ^ (Q : ℝ)) +
            (L : ℝ) * (2 ^ ((Q : ℝ) - 1) * Crec ^ (Q : ℝ) * 2 ^ (Q : ℝ))),
      ?_, ?_⟩
  · -- the shared constant is positive because the startup constant is
    intro L hL
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans zero_le_one hL
    have hcen : (0 : ℝ) ≤
        (L : ℝ) * (2 * (d : ℝ)) * (2 ^ ((Q : ℝ) - 1) * Crec ^ (Q : ℝ)) :=
      mul_nonneg (mul_nonneg hL0 (by positivity))
        (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
          (Real.rpow_pos_of_pos hCrec _)).le
    have hnl : (0 : ℝ) ≤ (L : ℝ) * (2 ^ ((Q : ℝ) - 1) * Crec ^ (Q : ℝ) * 2 ^ (Q : ℝ)) :=
      mul_nonneg hL0 hgain.le
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    linarith only [hL0, hcen, hnl]
  intro P hPprob hPstat hPunit l q hq jStar b TMax hlj hjb hbT hfin _hposdef hmom
  have := hPprob
  refine
    ⟨fun j T hj hjT hT => blockMatLoewnerLE_adaptedMean_window hPstat hq hlj hfin hj hjT hT,
      fun j T hj hjT hT => detIncrement_nonneg_window hPstat hq hlj hfin hj hjT hT,
      fun j T hj hjT hT =>
        blockMatLoewnerLE_blockIdentity_relMean_window hPstat hq hlj hfin hj hjT hT,
      portableProfile_self (Q : ℝ) a rhoMax hPstat hq hlj hfin hjb hbT,
      fun T hbTle hTmax => portable_majorization hQ0 ha hadm hPstat hq hlj hfin hjb hbTle hTmax,
      fun T hbTle hTmax =>
        portableProfile_service hQ1 ha hCrec0 hPstat hPunit hq hlj hfin hmom hrec hh hjb
          hbTle hTmax,
      fun T₀ K hT₀ _hK hKT => sum_synchCharge_le hPstat hq hlj hfin hh K (by omega) hKT,
      ?_, ?_⟩
  · -- propagation, at the shared constant
    intro L T hL hbTle hTL hprof
    have hD : 0 ≤ detIncrement P q T (T + L) :=
      detIncrement_nonneg_window hPstat hq hlj hfin (by omega) (by omega) hTL
    have hE : (0 : ℝ) ≤ Real.exp ((Q : ℝ) * detIncrement P q T (T + L)) - 1 := by
      have h1 := Real.one_le_exp (mul_nonneg hQ0.le hD)
      linarith only [h1]
    refine le_of_le_const (le_max_left _ _) hE ?_
    exact portableProfile_propagation_of_lambdaPort hQ1 ha hCrec0 hPstat hPunit hq hlj hfin
      hmom hrec hh hL hjb hbTle hTL hlam hprof
  · -- startup, at the shared constant
    intro L hL hbL hhist
    have hD : 0 ≤ detIncrement P q b (b + L) :=
      detIncrement_nonneg_window hPstat hq hlj hfin hjb (by omega) hbL
    have hE : (0 : ℝ) ≤ Real.exp ((Q : ℝ) * detIncrement P q b (b + L)) - 1 := by
      have h1 := Real.one_le_exp (mul_nonneg hQ0.le hD)
      linarith only [h1]
    refine le_of_le_const (le_max_right _ _) hE ?_
    exact portableProfile_startup hQ1 ha hCrec0 hPstat hPunit hq hlj hfin hmom hrec hL hjb
      hbL hhist

end

end PortableHistory
end HighContrast
end Homogenization
