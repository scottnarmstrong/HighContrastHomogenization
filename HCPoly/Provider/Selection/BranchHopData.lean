/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchHopTransport
import HCPoly.Provider.Selection.TransitionGuards

/-!
# Analytic data for the actual projective-hop successor

The transition guard identifies the T5 state update, to which the transported
short-hop estimates apply.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- Aligned short-hop and transport providers control every analytic component
of the actual T5 successor. -/
theorem branchT5Data_of_alignedConstant (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCd : 1 ≤ Cd)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {source : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K source)
    {jStar M : ℤ} (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Psi K Cd jStar M Y)
    (hbridge : ∀ mp mv : Mat d, mp.PosDef → mv.PosDef → ∀ nn l : ℤ,
      jStar ≤ nn - l →
      Ctr * (1 + Real.log (gridRatio (roundedGrid jStar mp)
        (roundedGrid jStar mv))) ≤ (l : ℝ) →
      Ctr * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
        (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
      (∀ r : Mat d, r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
        ∀ j : ℤ, jStar ≤ j → j ≤ nn + l → adaptedCell r j ⊆ centeredCube d M) →
      BlockMatLoewnerLE
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn - l)))
          (blockScale (bridgeErrUpper Ctr Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) nn)) ∧
        BlockMatLoewnerLE
          (blockScale (-bridgeErrLower Ctr Cd g (initExpRhoDr g)
            (gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv))
            P E jStar mp mv nn l) (adaptedMean P (roundedGrid jStar mp) (nn + l)))
          (blockSub (adaptedMean P (roundedGrid jStar mv) nn)
            (adaptedMean P (roundedGrid jStar mp) (nn + l))) ∧
        ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
          BlockMatLoewnerLE (blockScale (1 - eta)
            (adaptedMean P (roundedGrid jStar mp) (nn + l)))
            (adaptedMean P (roundedGrid jStar mv) nn) →
          linearDrift P (initExpRhoDr g) (roundedGrid jStar mv) jStar nn ≤
            Ctr * (eta + gridRatio (roundedGrid jStar mp)
                (roundedGrid jStar mv) * (3 : ℝ) ^ (-(l : ℝ)) +
              (1 + gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv)) *
                (3 : ℝ) ^ (2 * initExpRhoDr g * (l : ℝ)) *
                linearDrift P (initExpRhoDr g) (roundedGrid jStar mp)
                  jStar (nn + l) +
              bridgeShiftedRemainder Ctr Cd g (initExpRhoDr g) E
                jStar mp mv nn l))
    {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}
    (z : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {S S' : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S)
    (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      c.deltaShort c.deltaTerm c.l0 H .t5 S)
    (hout : (selectorStep P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm S).outcome = StepOutcome.next S')
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + 2 * (c.l0 : ℤ)))
    {r0 : ℤ} {k : ℕ} (cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 k)
    (hmu : cert.mus k = S.mu) (hstage : cert.starts k ≤ S.cursor)
    (hentry : z.B * Real.logb 3 (2 + aspectRatio E) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hcont : ∀ r : Mat d, r = S.q ∨ r = S'.q → ∀ j : ℤ,
      jStar ≤ j → j ≤ S.cursor + 2 * (c.l0 : ℤ) →
        adaptedCell r j ⊆ centeredCube d M) :
    let step := selectorStep P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm S
    step.rule = .t5 ∧ S'.mu.PosDef ∧
      Matrix.PosDef (toFullBlockMat (adaptedMean P S'.q S'.cursor)) ∧
      stateHistory S' ≤ ENNReal.ofReal c.etaIn ∧
      linearDrift P (initExpRhoDr g) S'.q jStar S'.cursor ≤ c.etaNew ∧
      projDist S.mu S'.mu ≤ c.chop ∧ gridRatio S.q S'.q ≤ Khop ∧
      BlockMatLoewnerLE (blockScale (1 - c.etaX)
        (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ))))
        (adaptedMean P S'.q (S.cursor + (c.l0 : ℤ))) ∧
      BlockMatLoewnerLE (adaptedMean P S'.q (S.cursor + (c.l0 : ℤ)))
        (blockScale (1 + c.etaX)
          (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ)))) ∧
      stateProfile P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) jStar S' = stateHistory S' := by
  dsimp only
  have hselected := ruleGuard_unique P (initExpQ d g : ℝ) (initExpA g)
    (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
    c.deltaShort c.deltaTerm c.l0 H S .t5 hguard
  have hrule : (selectorStep P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.h c.chop c.l0 H
      c.etaReady c.etaPre c.deltaShort c.deltaTerm S).rule = .t5 := by
    simp [selectorStep, ← hselected]
  simp [selectorStep, ← hselected] at hout
  subst S'
  obtain ⟨hmuPos, hnewPos, hhistory, hdrift, hjump, hratio, hlo, hhi, hprofile⟩ :=
    branchT5Transport_of_alignedConstant hd hg hCd hstat hunit hdag hwin hY
      hbridge z hexact hsearch hguard hread cert hmu hstage hentry hcont
  exact ⟨hrule, hmuPos, hnewPos, hhistory, hdrift, hjump, hratio, hlo, hhi, hprofile⟩

end

end Homogenization.HighContrast.Selection
