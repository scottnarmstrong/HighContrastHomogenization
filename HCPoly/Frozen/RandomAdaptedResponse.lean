/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.SelectionObjects
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Provider.Response.RandomAdaptedResponseFinal

/-!
# The adapted response estimate `e.response.adapted.conclusion`

Fixed-window adapted response with a random source scale.  On the terminal
window of one selected adapted grid, the canonical imbalance of the terminal
annealed block is within the prescribed target of one.  The conclusion is
uniform in the coefficient law, its source scale, its gauge, its reference
block, its intrinsic contrast and aspect ratio, the alignment, the retained base
block, and the incoming imbalances: none of those data appears in it.

The response-window constants are produced, not assumed.  The reference text
fixes the calibration tolerance, the determinant tolerance, the terminal length,
the profile tolerance and the drift tolerance in that order, subject to the
printed bounds, and then verifies that the numerical absorption inequality can
be met by letting the determinant tolerance, then the reciprocal terminal
length, then the profile tolerance go to zero.  The response coefficient of that
inequality is built from the dimensional constants of the three response lemmas
this argument uses, so it is not a quantity a consumer can evaluate; what a
consumer needs, and what the reference text supplies, is one admissible choice.
The statement therefore produces the five numbers with their printed bounds, and
the absorption inequality is discharged inside the argument.

The lower scale buffer is produced the same way and in the printed order: after
the five numbers, and after a witness-radius exponent is prescribed, since the
buffer must be large against that exponent.  The exponent is bound universally
here, because the selection produces it; the printed order — the response caps
and the terminal length, then the radius exponent, then the buffer — is exactly
this alternation.

The hypotheses are the four printed categories — block order, base-block
calibration, determinant ratio, retained history — together with the terminal
geometry, the enclosure of every queried cell in the window, the finiteness and
positivity of the annealed blocks of the terminal range with their aligned mean
order, the five windowed source fields, the portable majorant at its constant,
and the exact source buffer.  No response-load or canonical-comparison
hypothesis is imposed: those are derived inside the argument.

Two readings are recorded.  The five windowed source fields are read at the
selector's uniform multiplier cap rather than at the mean of the multiplier: the
provider produces the rows and the reference comparisons in the capped form, the
mean is at most the cap, and the argument uses the mean only through that cap.
The terminal centered and nonlinear histories of the reference text are the
recentered forms of the portable histories of the fixed-grid layer; the constant
skew congruence that relates them preserves every normalized size in them, so
the majorant is read on the portable histories themselves.
-/

theorem HCPoly.Frozen.random_adapted_response
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (deltaAd : ℝ) (hdeltaAdLo : 0 < deltaAd) (hdeltaAdHi : deltaAd ≤ 1) :
    ∀ Cd : ℝ, 1 ≤ Cd →
    ∃ (epsCal deltaDet : ℝ) (H : ℕ) (eta etaDr : ℝ),
      -- the response parameters, in their pre-law order
      0 < epsCal ∧ epsCal ≤ 1 / 3 ∧ 0 < deltaDet ∧ deltaDet ≤ 1 ∧ 4 ≤ H ∧
        0 < eta ∧ eta ≤ 1 / 2 ∧ 0 < etaDr ∧ etaDr ≤ min 1 (eta / 2) ∧
        ∀ Arad : ℝ, 0 ≤ Arad →
        ∃ Bresp : ℝ, 0 < Bresp ∧
          -- the slack in the source exponent
          1 + 2 * Arad < Homogenization.HighContrast.initExpRhoMax d g * Bresp ∧
          -- the smallness of the terminal source contribution
          24 * (Cd * Homogenization.HighContrast.zetaG g) ^ 2 *
              (3 : ℝ) ^
                (1 + 2 * Arad -
                  Homogenization.HighContrast.initExpRhoMax d g * Bresp) ≤
            1 / 2 * eta ^ ((Homogenization.HighContrast.initExpQ d g : ℝ)⁻¹) ∧
          -- the smallness of the source row
          24 * (Cd * Homogenization.HighContrast.zetaG g) ^ 2 /
                ((3 : ℝ) ^ (3 / 2 - g) - 1) *
              (3 : ℝ) ^ (1 + 2 * Arad - 3 / 2 * Bresp) ≤ 1 ∧
          ∀ (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d))
            (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (S : Homogenization.HighContrast.CoeffSpace d → ℝ),
            MeasureTheory.IsProbabilityMeasure P →
            HCPoly.Frozen.IsStationaryLaw P →
            HCPoly.Frozen.IsUnitRangeLaw P →
            HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S →
            ∀ jStar M : ℤ,
              Homogenization.HighContrast.IsCoupledWindow d
                (Homogenization.HighContrast.initExpQ d g : ℝ) K jStar M →
              ∀ Y : Homogenization.HighContrast.CoeffSpace d → ℝ,
                Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd jStar
                  M Y →
                -- the moment bound for the source multiplier
                1 ≤ ∫ a, Y a ∂P →
                ENNReal.ofReal (∫ a, Y a ∂P) ≤
                  Homogenization.HighContrast.lqNorm P
                    (Homogenization.HighContrast.initExpQ d g : ℝ) Y →
                Homogenization.HighContrast.lqNorm P
                    (Homogenization.HighContrast.initExpQ d g : ℝ) Y ≤ 2 →
                ∀ (E0 : Homogenization.BlockMat d)
                  (m0 q : Homogenization.Mat d) (s t : ℤ),
                  Homogenization.IsSymmetricBlockMat E0 →
                  Homogenization.Book.Ch02.BlockPosDef E0 →
                  -- `e.global.selection.scales`
                  m0 = Homogenization.HighContrast.canonicalMetric E0 →
                  q = Homogenization.HighContrast.roundedGrid jStar m0 →
                  jStar ≤ s → t = s + (H : ℤ) → (H : ℤ) < t →
                  -- every queried cell lies in the window
                  (∀ k : ℤ, jStar ≤ k → k ≤ t →
                    Homogenization.HighContrast.adaptedCell q k ⊆
                      Homogenization.HighContrast.centeredCube d M) →
                  (∀ k : ℤ, k < jStar → ∀ v : ℤ, v = s ∨ v = t →
                    ∀ z ∈ Homogenization.HighContrast.containedCenters q k v,
                      Homogenization.HighContrast.adaptedCellTranslate q k z ⊆
                        Homogenization.HighContrast.centeredCube d M) →
                  -- the annealed blocks are finite and positive, and decrease
                  -- with the generation
                  (∀ k : ℤ, jStar ≤ k → k ≤ t →
                    Homogenization.HighContrast.HasFiniteAdaptedMean P q k ∧
                      Homogenization.Book.Ch02.BlockPosDef
                        (Homogenization.HighContrast.adaptedMean P q k)) →
                  (∀ k : ℤ, jStar ≤ k → k ≤ t →
                    Homogenization.BlockMatLoewnerLE
                      (Homogenization.HighContrast.adaptedMean P q t)
                      (Homogenization.HighContrast.adaptedMean P q k)) →
                  -- the source data carried into the response estimate
                  Homogenization.HighContrast.IsWindowedSourceFields P g Cd E
                    jStar m0 s t Y →
                  -- the portable majorant of the terminal history
                  ∀ Cport : ℝ, 1 ≤ Cport →
                    Homogenization.HighContrast.portableHistory P
                          (Homogenization.HighContrast.initExpQ d g : ℝ)
                          (Homogenization.HighContrast.initExpA g)
                          (Homogenization.HighContrast.initExpRhoMax d g) q jStar
                          t ≤
                        ENNReal.ofReal Cport *
                          Homogenization.HighContrast.portableProfile P
                            (Homogenization.HighContrast.initExpQ d g : ℝ)
                            (Homogenization.HighContrast.initExpA g)
                            (Homogenization.HighContrast.initExpRhoMax d g) q
                            jStar s t →
                    -- the block orders and determinant ratio at the response endpoints
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.adaptedMean P q t)
                        (Homogenization.HighContrast.adaptedMean P q s) →
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.blockSharp
                          (Homogenization.HighContrast.adaptedMean P q s))
                        (Homogenization.HighContrast.adaptedMean P q s) →
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.blockSharp
                          (Homogenization.HighContrast.adaptedMean P q t))
                        (Homogenization.HighContrast.adaptedMean P q t) →
                    Homogenization.HighContrast.adaptedDetRoot P q s <
                      (1 + deltaDet) *
                        Homogenization.HighContrast.adaptedDetRoot P q t →
                    -- the base-block calibration `e.global.selection.calibration`
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.blockScale (1 - epsCal) E0)
                        (Homogenization.HighContrast.adaptedMean P q s) →
                    Homogenization.BlockMatLoewnerLE
                        (Homogenization.HighContrast.adaptedMean P q s)
                        (Homogenization.HighContrast.blockScale (1 + epsCal)
                          E0) →
                    -- the downstream determinant caps and the determinant
                    -- ratio at the two endpoints
                    ∀ deltaDetBar deltaTerm : ℝ,
                      0 < deltaDetBar → deltaDetBar ≤ deltaDet →
                      0 < deltaTerm → deltaTerm ≤ deltaDetBar →
                      Homogenization.HighContrast.adaptedDetRoot P q s <
                        (1 + deltaTerm) *
                          Homogenization.HighContrast.adaptedDetRoot P q t →
                      -- the drift input at the two endpoints
                      Homogenization.HighContrast.linearDrift P
                            (Homogenization.HighContrast.initExpRhoDr g) q jStar
                            s +
                          Homogenization.HighContrast.linearDrift P
                            (Homogenization.HighContrast.initExpRhoDr g) q jStar
                            t ≤
                        etaDr →
                      -- the retained history input
                      ∀ etaProfBar etaIn etaOut epsSt : ℝ,
                        0 < etaProfBar →
                        etaProfBar ≤
                          (2 : ℝ) ^
                              (-(Homogenization.HighContrast.initExpQ d g : ℤ)) *
                            eta →
                        Homogenization.HighContrast.portableProfile P
                            (Homogenization.HighContrast.initExpQ d g : ℝ)
                            (Homogenization.HighContrast.initExpA g)
                            (Homogenization.HighContrast.initExpRhoMax d g) q
                            jStar s t ≤ ENNReal.ofReal etaOut →
                        ENNReal.ofReal Cport *
                            Homogenization.HighContrast.portableProfile P
                              (Homogenization.HighContrast.initExpQ d g : ℝ)
                              (Homogenization.HighContrast.initExpA g)
                              (Homogenization.HighContrast.initExpRhoMax d g) q
                              jStar s t ≤ ENNReal.ofReal epsSt →
                        max (max etaIn etaOut) epsSt ≤ etaProfBar →
                        -- `e.global.selection.eccentricity`
                        Homogenization.HighContrast.kappaRef E ≤
                          6 * Homogenization.HighContrast.aspectRatio E →
                        Homogenization.HighContrast.witnessEccentricity m0 ≤
                          (2 + Homogenization.HighContrast.aspectRatio E) ^
                            Arad →
                        jStar +
                            ⌈Bresp *
                              Real.logb 3
                                (2 +
                                  Homogenization.HighContrast.aspectRatio E)⌉ ≤
                          s →
                        -- `e.response.adapted.conclusion`
                        Homogenization.HighContrast.blockImbalance
                            (Homogenization.HighContrast.adaptedMean P q t) ≤
                          1 + deltaAd
    := by
  exact Homogenization.HighContrast.Response.random_adapted_response_assembly
    d hd g hg deltaAd hdeltaAdLo hdeltaAdHi
