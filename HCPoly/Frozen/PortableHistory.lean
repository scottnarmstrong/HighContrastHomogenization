/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.PortableHistoryAssembly
import HCPoly.Setup.Moments

/-!
# Proposition `p.fixed.geometry.one.grid.propagation`

Portable complete histories.  The centered and nonlinear histories at a
checkpoint `b`, and the profile `𝒫_q(T;b)` that carries the whole earlier
history as one checkpoint datum: the profile majorizes the history at every
later scale, it contracts over one service length with no scale-independent
error, its synchronized charges have bounded multiplicity, and it propagates
over a bounded number of scales from a unit-size profile or from a unit-size
checkpoint.

The constant `C_rec(d,Q)` of `p.fixed.geometry.parent.child.recurrence` enters through the
service length: the hypothesis `hrec` is exactly that proposition's conclusion,
at the value `Crec` for which the contraction factor `λ_port` is admissible.  A
consumer discharges it by destructuring `p.fixed.geometry.parent.child.recurrence` itself.

As in the recurrence, the grid's alignment `ℓ` is explicit and `j_*` is at or
above it; the printed hypothesis `j_* ≥ k_0(d)` is the special case
`ℓ = k_0(d)`.

The definedness and positivity guards, and every clause that reads a scale,
are bounded by the ceiling `TMax`.  The paper states the guards for every
scale at or above `j_*`, but each provider of these hypotheses controls only
a bounded window, so the bounded form is the one the proposition's consumers
can instantiate.
-/

theorem HCPoly.Frozen.portable_history
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
  exact Homogenization.HighContrast.PortableHistory.portable_history_assembly d hd Q hQ hQeven a rhoMax ha
    hrhoMax hadm Crec hCrec hrec h hh hlam
