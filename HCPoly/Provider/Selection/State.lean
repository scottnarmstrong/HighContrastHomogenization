/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Cutoff
import HCPoly.Provider.Selection.ProjectiveProgress

/-!
# States of the global selector

The selector retains the two exact history components at its checkpoint and
keeps the moving profile and drift as derived coordinates.  Its state is built
entirely from annealed data; in particular, it contains no window multiplier.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- The three phases used by the ordered transition rules. -/
inductive Phase where
  | fresh
  | search
  | terminal
deriving DecidableEq

/-- The twelve components of the persistent selector state carried by the
one-pass selection iteration of `p.global.selection`. -/
structure State (d : ℕ) where
  stage : ℕ
  q : Mat d
  mu : Mat d
  base : ℤ
  baseMean : BlockMat d
  checkpoint : ℤ
  centered : ℝ≥0∞
  nonlinear : ℝ≥0∞
  cursor : ℤ
  phase : Phase
  candidate : Option (BlockMat d)
  prefixLoss : ℝ

variable {d : ℕ}

/-- The complete retained history is the sum of its exact components. -/
def stateHistory (S : State d) : ℝ≥0∞ :=
  S.centered + S.nonlinear

/-- Defining equation for the retained history. -/
theorem stateHistory_eq (S : State d) :
    stateHistory S = S.centered + S.nonlinear := rfl

/-- The moving portable profile `𝒫_q(u;r)` read by the search guards. -/
def stateProfile (P : Measure (CoeffSpace d)) (Q a rhoMax : ℝ)
    (jStar : ℤ) (S : State d) : ℝ≥0∞ :=
  portableProfile P Q a rhoMax S.q jStar S.checkpoint S.cursor

/-- Defining equation for the moving portable profile. -/
theorem stateProfile_eq (P : Measure (CoeffSpace d)) (Q a rhoMax : ℝ)
    (jStar : ℤ) (S : State d) :
    stateProfile P Q a rhoMax jStar S =
      portableProfile P Q a rhoMax S.q jStar S.checkpoint S.cursor := rfl

/-- The logarithmic profile work `W(S)`.  The profile is finite on every
reachable state, so `toReal` is the real-valued reading used in the potential. -/
def stateWork (P : Measure (CoeffSpace d)) (Q a rhoMax etaReady : ℝ)
    (jStar : ℤ) (S : State d) : ℝ :=
  Real.log (1 + etaReady⁻¹ * (stateProfile P Q a rhoMax jStar S).toReal)

/-- Defining equation for the logarithmic profile work. -/
theorem stateWork_eq (P : Measure (CoeffSpace d)) (Q a rhoMax etaReady : ℝ)
    (jStar : ℤ) (S : State d) :
    stateWork P Q a rhoMax etaReady jStar S =
      Real.log (1 + etaReady⁻¹ *
        (portableProfile P Q a rhoMax S.q jStar S.checkpoint S.cursor).toReal) := rfl

/-- The dyadic drift index `b_dr(u)`. -/
def driftIndex (P : Measure (CoeffSpace d)) (rhoDr etaPre : ℝ)
    (jStar : ℤ) (S : State d) : ℕ :=
  ⌈Real.logb 2 (max 1
    (linearDrift P rhoDr S.q jStar S.cursor / etaPre))⌉₊

/-- The projective distance from the retained witness to the current base
mean. -/
def stateProjectiveDistance (S : State d) : ℝ :=
  projDist S.mu (canonicalMetric S.baseMean)

/-- Defining equation for the state projective distance. -/
theorem stateProjectiveDistance_eq (S : State d) :
    stateProjectiveDistance S =
      projDist S.mu (canonicalMetric S.baseMean) := rfl

/-- The potential `𝓕(S)` of the selector.  The drift weight is the fixed value
one, and the two phase charges are the printed indicator terms. -/
def statePotential (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar : ℤ) (etaReady etaPre alphaW alphaX alphaFresh alphaSearch : ℝ)
    (S : State d) : ℝ :=
  alphaW * stateWork P Q a rhoMax etaReady jStar S +
    (driftIndex P rhoDr etaPre jStar S : ℝ) +
    alphaX * stateProjectiveDistance S +
    (if S.phase = Phase.fresh then alphaFresh else 0) +
    (if S.phase = Phase.search then alphaSearch else 0)

/-- Defining equation for the selector potential. -/
theorem statePotential_eq (P : Measure (CoeffSpace d))
    (Q a rhoMax rhoDr : ℝ) (jStar : ℤ)
    (etaReady etaPre alphaW alphaX alphaFresh alphaSearch : ℝ)
    (S : State d) :
    statePotential P Q a rhoMax rhoDr jStar etaReady etaPre alphaW alphaX
        alphaFresh alphaSearch S =
      alphaW * stateWork P Q a rhoMax etaReady jStar S +
        (driftIndex P rhoDr etaPre jStar S : ℝ) +
        alphaX * stateProjectiveDistance S +
        (if S.phase = Phase.fresh then alphaFresh else 0) +
        (if S.phase = Phase.search then alphaSearch else 0) := rfl

/-- The initial identity-grid state at the least synchronized checkpoint. -/
def initialState (r0 : ℤ) (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) : State d :=
  { stage := 0
    q := 1
    mu := 1
    base := r0
    baseMean := A0
    checkpoint := r0
    centered := hcen
    nonlinear := hnl
    cursor := r0
    phase := Phase.fresh
    candidate := none
    prefixLoss := 0 }

/-- A same-grid cursor advance, including the determinant-prefix update. -/
def advanceCursor (P : Measure (CoeffSpace d)) (S : State d) (v : ℤ)
    (phase : Phase) (candidate : Option (BlockMat d)) : State d :=
  { S with
    cursor := v
    phase := phase
    candidate := candidate
    prefixLoss := S.prefixLoss + detLoss P S.q S.cursor v }

/-- The common exact-data invariant at a persistent decision point. -/
def ExactStateData (P : Measure (CoeffSpace d)) (Q a rhoMax : ℝ)
    (jStar : ℤ) (S : State d) : Prop :=
  S.q = roundedGrid jStar S.mu ∧
    S.baseMean = adaptedMean P S.q S.base ∧
    S.centered = centeredHistory P Q rhoMax S.q jStar S.checkpoint ∧
    S.nonlinear = nonlinearHistory P Q a S.q jStar S.checkpoint ∧
    jStar ≤ S.checkpoint ∧ S.checkpoint ≤ S.cursor

/-- The fresh-phase invariant. -/
def FreshInvariant (P : Measure (CoeffSpace d)) (rhoDr etaIn etaNew : ℝ)
    (jStar : ℤ) (S : State d) : Prop :=
  S.phase = Phase.fresh ∧ S.base = S.checkpoint ∧
    S.checkpoint = S.cursor ∧ S.candidate = none ∧
    stateHistory S ≤ ENNReal.ofReal etaIn ∧
    linearDrift P rhoDr S.q jStar S.cursor ≤ etaNew

/-- The search-phase invariant. -/
def SearchInvariant (h : ℤ) (S : State d) : Prop :=
  S.phase = Phase.search ∧ S.checkpoint + h ≤ S.cursor ∧
    S.candidate = none

/-- The terminal-phase invariant, including the candidate calibration. -/
def TerminalInvariant (P : Measure (CoeffSpace d)) (rhoDr etaIn etaNew etaX : ℝ)
    (jStar : ℤ) (S : State d) : Prop :=
  S.phase = Phase.terminal ∧ S.base = S.checkpoint ∧
    S.checkpoint = S.cursor ∧ stateHistory S ≤ ENNReal.ofReal etaIn ∧
    linearDrift P rhoDr S.q jStar S.cursor ≤ etaNew ∧
    ∃ E0 : BlockMat d, S.candidate = some E0 ∧
      S.mu = canonicalMetric E0 ∧
      BlockMatLoewnerLE (blockScale (1 - etaX) E0) S.baseMean ∧
      BlockMatLoewnerLE S.baseMean (blockScale (1 + etaX) E0)

end

end Selection
end HighContrast
end Homogenization
