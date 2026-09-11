/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.Enclosure
import HCPoly.Provider.Selection.HopTrace
import HCPoly.Provider.Selection.TerminationCharges

/-!
# Extending the projective-hop certificate

The proof-only hop certificate is extended only when the executable selector
takes rule T5.  The extension retains all earlier stages and appends the
actual witness, grid, scale, bridge tolerance, and determinant interval.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-- Append one genuine projective hop to a proof-only prefix certificate. -/
theorem HopPrefixCertificate.extend
    {P : Measure (CoeffSpace d)} {jStar : ℤ} {chop Khop : ℝ}
    {l0 : ℕ} {r0 Tquery : ℤ} {k : ℕ}
    (cert : HopPrefixCertificate P jStar chop Khop l0 r0 k)
    {mu' q' : Mat d} {s' t : ℤ} {eta' : ℝ}
    (hmu' : mu'.PosDef) (hq' : q' = roundedGrid jStar mu')
    (hscale : cert.starts k + (l0 : ℤ) ≤ s')
    (hhop : projDist (cert.mus k) mu' ≤ chop)
    (hgrid : gridRatio (cert.grids k) q' ≤ Khop)
    (heta0 : 0 ≤ eta') (heta4 : eta' ≤ 1 / 4)
    (hterminal : cert.starts k ≤ t)
    (hstartsBound : ∀ i : ℕ, i ≤ k → cert.starts i ≤ Tquery)
    (hterminalsBound : ∀ i : ℕ, i < k → cert.terminals i ≤ Tquery)
    (hs'Bound : s' ≤ Tquery) (htBound : t ≤ Tquery) :
    ∃ cert' : HopPrefixCertificate P jStar chop Khop l0 r0 (k + 1),
      cert'.mus (k + 1) = mu' ∧ cert'.grids (k + 1) = q' ∧
        cert'.starts (k + 1) = s' ∧ cert'.terminals k = t ∧
        cert'.eta k = eta' ∧
        cert'.completedLoss = cert.completedLoss +
          detLoss P (cert.grids k) (cert.starts k) t ∧
        (∀ i : ℕ, i ≤ k → cert'.mus i = cert.mus i ∧
          cert'.grids i = cert.grids i ∧ cert'.starts i = cert.starts i) ∧
        (∀ i : ℕ, i < k →
          cert'.terminals i = cert.terminals i ∧ cert'.eta i = cert.eta i) ∧
        (∀ i : ℕ, i ≤ k + 1 → cert'.starts i ≤ Tquery) ∧
        ∀ i : ℕ, i < k + 1 → cert'.terminals i ≤ Tquery := by
  let mus' := Function.update cert.mus (k + 1) mu'
  let grids' := Function.update cert.grids (k + 1) q'
  let starts' := Function.update cert.starts (k + 1) s'
  let terminals' := Function.update cert.terminals k t
  let eta'' := Function.update cert.eta k eta'
  let loss' := cert.completedLoss +
    detLoss P (cert.grids k) (cert.starts k) t
  have hold (i : ℕ) (hi : i ≤ k) : i ≠ k + 1 := by omega
  have holdSucc (i : ℕ) (hi : i < k) : i + 1 ≠ k + 1 := by omega
  have hsum : loss' = ∑ i ∈ Finset.range (k + 1),
      detLoss P (grids' i) (starts' i) (terminals' i) := by
    dsimp only [loss']
    rw [Finset.sum_range_succ, cert.completedLoss_eq]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      simp only [grids', starts', terminals', Function.update_of_ne (hold i hik.le),
        Function.update_of_ne (by omega : i ≠ k)]
    · simp only [grids', starts', terminals', Function.update_of_ne
        (by omega : k ≠ k + 1), Function.update_self]
  let cert' : HopPrefixCertificate P jStar chop Khop l0 r0 (k + 1) := {
    mus := mus'
    grids := grids'
    starts := starts'
    terminals := terminals'
    eta := eta''
    mus_pos := by
      intro i hi
      by_cases hik : i = k + 1
      · subst i
        simpa only [mus', Function.update_self] using hmu'
      · simpa only [mus', Function.update_of_ne hik] using cert.mus_pos i (by omega)
    mus_zero := by
      simpa only [mus', Function.update_of_ne (by omega : 0 ≠ k + 1)] using cert.mus_zero
    grids_eq := by
      intro i hi
      by_cases hik : i = k + 1
      · subst i
        simpa only [grids', mus', Function.update_self] using hq'
      · simpa only [grids', mus', Function.update_of_ne hik] using
          cert.grids_eq i (by omega)
    starts_zero := by
      simpa only [starts', Function.update_of_ne (by omega : 0 ≠ k + 1)] using
        cert.starts_zero
    scale_step := by
      intro i hi
      by_cases hik : i = k
      · subst i
        simpa only [starts', Function.update_of_ne (by omega : k ≠ k + 1),
          Function.update_self] using hscale
      · have hiold : i < k := by omega
        simpa only [starts', Function.update_of_ne (hold i hiold.le),
          Function.update_of_ne (holdSucc i hiold)] using cert.scale_step i hiold
    hop_step := by
      intro i hi
      by_cases hik : i = k
      · subst i
        simpa only [mus', Function.update_of_ne (by omega : k ≠ k + 1),
          Function.update_self] using hhop
      · have hiold : i < k := by omega
        simpa only [mus', Function.update_of_ne (hold i hiold.le),
          Function.update_of_ne (holdSucc i hiold)] using cert.hop_step i hiold
    grid_step := by
      intro i hi
      by_cases hik : i = k
      · subst i
        simpa only [grids', Function.update_of_ne (by omega : k ≠ k + 1),
          Function.update_self] using hgrid
      · have hiold : i < k := by omega
        simpa only [grids', Function.update_of_ne (hold i hiold.le),
          Function.update_of_ne (holdSucc i hiold)] using cert.grid_step i hiold
    eta_nonneg := by
      intro i hi
      by_cases hik : i = k
      · subst i
        simpa only [eta'', Function.update_self] using heta0
      · have hiold : i < k := by omega
        simpa only [eta'', Function.update_of_ne hik] using cert.eta_nonneg i hiold
    eta_le := by
      intro i hi
      by_cases hik : i = k
      · subst i
        simpa only [eta'', Function.update_self] using heta4
      · have hiold : i < k := by omega
        simpa only [eta'', Function.update_of_ne hik] using cert.eta_le i hiold
    terminal_ge := by
      intro i hi
      by_cases hik : i = k
      · subst i
        simpa only [starts', terminals', Function.update_of_ne
          (by omega : k ≠ k + 1), Function.update_self] using hterminal
      · have hiold : i < k := by omega
        simpa only [starts', terminals', Function.update_of_ne (hold i hiold.le),
          Function.update_of_ne hik] using cert.terminal_ge i hiold
    completedLoss := loss'
    completedLoss_eq := hsum
  }
  refine ⟨cert', ?_⟩
  simp only [cert', mus', grids', starts', terminals', eta'', loss',
    Function.update_self, true_and]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [Function.update_of_ne (hold i hi), and_self]
  · simp only [Function.update_of_ne (by omega : i ≠ k), and_self]
  · by_cases hik : i = k + 1
    · subst i
      simpa only [Function.update_self] using hs'Bound
    · simpa only [Function.update_of_ne hik] using hstartsBound i (by omega)
  · by_cases hik : i = k
    · subst i
      simpa only [Function.update_self] using htBound
    · simpa only [Function.update_of_ne hik] using hterminalsBound i (by omega)

/-- Advancing a cursor preserves all exact checkpoint data. -/
theorem exactStateData_advanceCursor
    {P : Measure (CoeffSpace d)} {Q a rhoMax : ℝ} {jStar v : ℤ}
    {S : State d} (hexact : ExactStateData P Q a rhoMax jStar S)
    (hv : S.checkpoint ≤ v) :
    ExactStateData P Q a rhoMax jStar (advanceCursor P S v .search none) := by
  rcases hexact with ⟨hq, hmean, hcen, hnl, hj, -⟩
  exact ⟨hq, hmean, hcen, hnl, hj, hv⟩

/-- A same-grid cursor advance retains the hop certificate and extends only
its current determinant interval. -/
theorem HopPrefixCertificate.advanceCursor
    {P : Measure (CoeffSpace d)} {jStar : ℤ} {chop Khop : ℝ}
    {l0 : ℕ} {r0 Tquery : ℤ} {S : State d}
    (cert : HopPrefixCertificate P jStar chop Khop l0 r0 S.stage)
    (hmu : cert.mus S.stage = S.mu) (hq : cert.grids S.stage = S.q)
    (hs : cert.starts S.stage = S.base)
    (hloss : S.prefixLoss = cert.completedLoss +
      detLoss P S.q S.base S.cursor)
    (hbridge : ∀ i : ℕ, i < S.stage →
      BlockMatLoewnerLE (blockScale (1 - cert.eta i)
        (adaptedMean P (cert.grids i) (cert.terminals i)))
        (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1))) ∧
      BlockMatLoewnerLE
        (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1)))
        (blockScale (1 + cert.eta i)
          (adaptedMean P (cert.grids i) (cert.terminals i))))
    (hstartsBound : ∀ i : ℕ, i ≤ S.stage → cert.starts i ≤ Tquery)
    (hterminalsBound : ∀ i : ℕ, i < S.stage → cert.terminals i ≤ Tquery)
    (v : ℤ) :
    ∃ cert' : HopPrefixCertificate P jStar chop Khop l0 r0
        (advanceCursor P S v .search none).stage,
      cert'.mus (advanceCursor P S v .search none).stage =
          (advanceCursor P S v .search none).mu ∧
        cert'.grids (advanceCursor P S v .search none).stage =
          (advanceCursor P S v .search none).q ∧
        cert'.starts (advanceCursor P S v .search none).stage =
          (advanceCursor P S v .search none).base ∧
        (advanceCursor P S v .search none).prefixLoss = cert'.completedLoss +
          detLoss P (advanceCursor P S v .search none).q
            (advanceCursor P S v .search none).base
            (advanceCursor P S v .search none).cursor ∧
        (∀ i : ℕ, i < (advanceCursor P S v .search none).stage →
          BlockMatLoewnerLE (blockScale (1 - cert'.eta i)
            (adaptedMean P (cert'.grids i) (cert'.terminals i)))
            (adaptedMean P (cert'.grids (i + 1)) (cert'.starts (i + 1))) ∧
          BlockMatLoewnerLE
            (adaptedMean P (cert'.grids (i + 1)) (cert'.starts (i + 1)))
            (blockScale (1 + cert'.eta i)
              (adaptedMean P (cert'.grids i) (cert'.terminals i)))) ∧
        (∀ i : ℕ, i ≤ (advanceCursor P S v .search none).stage →
          cert'.starts i ≤ Tquery) ∧
        ∀ i : ℕ, i < (advanceCursor P S v .search none).stage →
          cert'.terminals i ≤ Tquery := by
  refine ⟨cert, ?_⟩
  change cert.mus S.stage = S.mu ∧ cert.grids S.stage = S.q ∧
    cert.starts S.stage = S.base ∧
      S.prefixLoss + detLoss P S.q S.cursor v = cert.completedLoss +
        detLoss P S.q S.base v ∧
      (∀ i : ℕ, i < S.stage →
        BlockMatLoewnerLE (blockScale (1 - cert.eta i)
          (adaptedMean P (cert.grids i) (cert.terminals i)))
          (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1))) ∧
        BlockMatLoewnerLE
          (adaptedMean P (cert.grids (i + 1)) (cert.starts (i + 1)))
          (blockScale (1 + cert.eta i)
            (adaptedMean P (cert.grids i) (cert.terminals i)))) ∧
      (∀ i : ℕ, i ≤ S.stage → cert.starts i ≤ Tquery) ∧
      ∀ i : ℕ, i < S.stage → cert.terminals i ≤ Tquery
  refine ⟨hmu, hq, hs, ?_, hbridge, hstartsBound, hterminalsBound⟩
  rw [hloss]
  calc
    cert.completedLoss + detLoss P S.q S.base S.cursor +
        detLoss P S.q S.cursor v =
      cert.completedLoss + (detLoss P S.q S.base S.cursor +
        detLoss P S.q S.cursor v) := by ring
    _ = cert.completedLoss + detLoss P S.q S.base v := by rw [detLoss_add]

/-- An invariant closed under actual nonterminal steps holds at every state
retained by a capped run. -/
theorem runCapped_invariant_aux
    {P : Measure (CoeffSpace d)} {Q a rhoMax rhoDr : ℝ}
    {jStar h : ℤ} {chop : ℝ} {l0 H fuel : ℕ}
    {etaReady etaPre deltaShort deltaTerm : ℝ} {S : State d}
    {Inv : State d → Prop} {full : CappedRun d}
    (hsub : ∀ T ∈ (runCapped P Q a rhoMax rhoDr jStar h chop l0 H
      etaReady etaPre deltaShort deltaTerm fuel S).states, T ∈ full.states)
    (hquery : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm fuel S).queryScale ≤ full.queryScale)
    (hnext : ∀ {S₀ S₁ : State d}, S₀ ∈ full.states → S₁ ∈ full.states →
      (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm S₀).outcome = StepOutcome.next S₁ →
      (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm S₀).readScale ≤ full.queryScale → Inv S₀ → Inv S₁)
    (hS : Inv S) :
    ∀ T ∈ (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states, Inv T := by
  induction fuel generalizing S with
  | zero =>
      intro T hT
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H
        etaReady etaPre deltaShort deltaTerm S).outcome <;>
        simp [runCapped, hout] at hT <;> subst T <;> exact hS
  | succ fuel ih =>
      intro T hT
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H
        etaReady etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          simp [runCapped, hout] at hT
          subst T
          exact hS
      | next Sn =>
          have hread : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H
              etaReady etaPre deltaShort deltaTerm S).readScale ≤ full.queryScale :=
            (le_max_left _ _).trans (by simpa only [runCapped, hout] using hquery)
          have htailQuery : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H
              etaReady etaPre deltaShort deltaTerm fuel Sn).queryScale ≤
              full.queryScale :=
            (le_max_right _ _).trans (by simpa only [runCapped, hout] using hquery)
          simp only [runCapped, hout, List.mem_cons] at hT
          rcases hT with rfl | htail
          · exact hS
          · have hSfull : S ∈ full.states := hsub S (by simp [runCapped, hout])
            have hSnfull : Sn ∈ full.states := hsub Sn (by
              simp only [runCapped, hout, List.mem_cons]
              exact Or.inr (runCapped_initial_mem P Q a rhoMax rhoDr jStar h
                chop l0 H etaReady etaPre deltaShort deltaTerm fuel Sn))
            apply ih (S := Sn) (hS := hnext hSfull hSnfull hout hread hS)
              (hsub := fun U hU => hsub U (by
                simp only [runCapped, hout, List.mem_cons]
                exact Or.inr hU)) (hquery := htailQuery)
            exact htail

/-- The first selector read is included in the query scale of its capped run. -/
theorem runCapped_initial_readScale_le_queryScale
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H fuel : ℕ)
    (etaReady etaPre deltaShort deltaTerm : ℝ) (S : State d) :
    (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).readScale ≤
      (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
        deltaShort deltaTerm fuel S).queryScale := by
  cases fuel <;>
    cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm S).outcome <;> simp [runCapped, hout]

end

end Homogenization.HighContrast.Selection
