/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.TransportObjects
import HCPoly.Frozen.Stationarity
import HCPoly.Frozen.UnitRange
import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Provider.ShortHop.ShortHopAssembly

/-!
# Proposition `p.successful.short.bridge`

The successful short test.  After a retained finite prefix of bounded projective
hops, a cursor that passes the drift test and the determinant test admits one
further path step: the annealed block of the new grid at the intermediate scale
is a near isometry of the old grid's terminal block, and the new grid's weighted
determinant drift is below the prescribed allowance.

Every threshold is chosen before the law, in the printed order — the buffer, the
source allowance, the determinant tolerance, the drift tolerance, the cutoff
coefficient — and each depends only on the dimension, the growth exponent, the
hop length, the two allowances, the common lower buffer, the rounded-hop
constant, the transport threshold, the two-grid constant, and the dimensional
constant of the source-control subsection.  The reference text lists a shorter
set, because there the transport threshold and the two-grid constant are
themselves functions of the listed data; here they are free binders, and the
buffer visibly depends on both — it is at least the transport threshold and at
least a multiple of the two-grid constant.  The dependence on the dimensional
constant is why that constant is bound first, ahead of all five thresholds: the
source coefficients of the bridge are cubic in it, so the cutoff coefficient
that makes their remainders small must be allowed to grow with it.  The two
constants play different roles and neither dominates the other: the dimensional
constant names only the coefficient of the pathwise cell bounds carried by the
window multiplier, while the counting constant of the cross-grid boundary row —
which the reference text writes with the same symbol — is a deterministic
geometric fact absorbed into the two-grid constant.  The candidate is not a free parameter: it is the next point of the
fixed constant-speed projective path from the current witness to the canonical
metric of the old grid's terminal block, and the endpoint when the two
projective classes already agree.

The thresholds are not merely positive numbers.  The ordered choice is what the
statement exports: on the box cut out by the drift tolerance, the determinant
tolerance and the source allowance, the bridge-error envelope stays below the
prescribed near-isometry allowance and the new-grid drift envelope below the
prescribed drift allowance.  Both envelopes are continuous, written out in the
carrier layer, and the source allowance is the radius within which a consumer's
own remainder bounds must fall for the two envelopes to apply.  The bridge-error
envelope reads four arguments and the new-grid drift envelope three; the
reference text displays the second with a fourth argument that its own body
never uses, so the carrier drops it.  Without that pair of inequalities the source allowance
would be an unconstrained positive number and the global argument's citation of
it would have no content.

Two constants of neighbouring results enter as data with their conclusions
inlined, as the recurrence constant does in `p.fixed.geometry.one.grid.propagation`.  The
rounded-hop constant is presented with the distortion bound it names — in the
form its proof establishes, for **any** pair of positive witnesses at
projective distance at most the hop length.  The reference text states that
bound only for successive points of one constant-speed path, but its proof
assumes nothing beyond the distance, and the general form is what the
self-comparison below needs.  The two-grid constant is presented with
the two mean comparisons and the shifted drift it names; a consumer discharges
each by destructuring the result that produces it.  The transport threshold
enters only through the buffer it lower-bounds.

The printed hypothesis "all old-grid, new-grid, comparison, and shifted-drift
cells lie in the preassigned window" is carried by the containment of the two
grid towers over the scales the test reads: every cell any of those families
contributes lies inside a cell of one of the two towers.

Nothing about definedness is assumed or concluded, and that is deliberate.  The
tower containment, the window multiplier, and the terminal block of
`e.source.adapted.bound` together force the annealed blocks of the old grid
to be finite and positive definite at every scale of the tower, before the
candidate is formed; the same chain then runs on the new grid.  Two steps of it
are not immediate.  One is the self-comparison of the old grid against itself,
which the rounded-hop bound supplies at coincident witnesses, where the
projective distance is zero — this is the second place the general form of that
bound earns its keep.  The other is the alignment: reading the rounded-hop bound
at the burn scale needs that scale to be at or above the rounding scale, which is
not a binder here but follows from the coupled window, whose burn is a maximum
taken over the rounding scale.

Every quantity in this statement with a junk branch is closed by that chain or
fails in the safe direction; the enumeration below is given in full so that
each position can be checked.  The weighted drift collapses to zero when its terminal block is
singular; the determinant root is a real power of a determinant; the canonical
metric is a chosen factorization, defined off positive data by a junk witness;
the path step reads a square root and a real matrix power; the cross-grid factor
and the projective distance read matrix inverses; the aspect ratio is a
quotient; and the lower comparison envelope divides by a quantity the scale
condition keeps away from zero.  The chain closes the first five on every
instance the hypotheses admit, and the division is closed by the scale condition
that sits beside it.

The aspect ratio needs a word of its own, because it is the one position closed
from outside this chain rather than inside it.  It enters the lower bound on the
entry scale, where the reference text reads it as at least one.  That floor is
proved content: `one_le_aspectRatio_of_coarseEllipticityDagger` derives it from
the coarse ellipticity datum together with a probability law, and both are
hypotheses this proposition already carries, so nothing further is assumed and
nothing is left open.  Neither the window nor the multiplier nor any grid enters
that derivation.

The neighbouring transport proposition does export a definedness block, because
its own printed statement does; this one does not, because its printed statement
does not and no consumer reads it here.
-/

theorem HCPoly.Frozen.random_source_bridge_short_hop
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (chop : ℝ) (hchop : 0 < chop)
    (etaNew : ℝ) (hetaNewLo : 0 < etaNew) (hetaNewHi : etaNew < 1)
    (etaX : ℝ) (hetaXLo : 0 < etaX) (hetaXHi : etaX ≤ 1 / 4)
    (Lcommon : ℕ)
    (Khop : ℝ) (hKhop : 1 ≤ Khop)
    (hhop :
      ∀ l : ℤ, (Homogenization.HighContrast.kZero d : ℤ) ≤ l →
        ∀ m₀ m₁ : Homogenization.Mat d, m₀.PosDef → m₁.PosDef →
          Homogenization.HighContrast.projDist m₀ m₁ ≤ chop →
          Homogenization.HighContrast.gridRatio
              (Homogenization.HighContrast.roundedGrid l m₀)
              (Homogenization.HighContrast.roundedGrid l m₁) ≤ Khop)
    (Ltr : ℕ) (hLtr : 1 ≤ Ltr)
    (C : ℝ) (hC : 0 < C) :
    ∀ Cd : ℝ, 1 ≤ Cd →
    ∃ l0 : ℕ, max Lcommon Ltr ≤ l0 ∧
      ∃ tauSrc : ℝ, 0 < tauSrc ∧
        ∃ deltaShort : ℝ, 0 < deltaShort ∧
          ∃ etaPre : ℝ, 0 < etaPre ∧
            ∃ B : ℝ, 0 < B ∧
              -- the constants fixed for the bridge test
              C * (1 + Real.log Khop) ≤ (l0 : ℝ) ∧
              C * Khop * (3 : ℝ) ^ (-(l0 : ℝ)) ≤ 1 / 2 ∧
              2 * chop <
                Homogenization.HighContrast.initExpRhoDr g * (l0 : ℝ) *
                  Real.log 3 / 2 ∧
              1 < Homogenization.HighContrast.initExpRhoDr g * B / 2 ∧
              -- the two threshold inequalities of the ordered choice
              (∀ b delta R₁ R₂ R₃ : ℝ,
                0 ≤ b → b ≤ etaPre → 0 ≤ delta → delta ≤ deltaShort →
                0 ≤ R₁ → R₁ ≤ tauSrc → 0 ≤ R₂ → R₂ ≤ tauSrc →
                0 ≤ R₃ → R₃ ≤ tauSrc →
                Homogenization.HighContrast.shortBridgeErr d C Khop
                    (Homogenization.HighContrast.initExpRhoDr g) (l0 : ℤ) b delta
                    R₁ R₂ ≤ etaX ∧
                  Homogenization.HighContrast.shortNewDrift d C Khop
                      (Homogenization.HighContrast.initExpRhoDr g) (l0 : ℤ) b delta
                      R₂ R₃ ≤ etaNew) ∧
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
                    Homogenization.HighContrast.IsWindowMultiplier P g E Ψ K Cd
                      jStar M Y →
                    -- the two-grid means and the shifted determinant drift, at C
                    (∀ mp mv : Homogenization.Mat d, mp.PosDef → mv.PosDef →
                      ∀ nn l : ℤ, jStar ≤ nn - l →
                        C *
                            (1 +
                              Real.log
                                (Homogenization.HighContrast.gridRatio
                                  (Homogenization.HighContrast.roundedGrid jStar mp)
                                  (Homogenization.HighContrast.roundedGrid jStar
                                    mv))) ≤ (l : ℝ) →
                        C *
                              Homogenization.HighContrast.gridRatio
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                (Homogenization.HighContrast.roundedGrid jStar mv) *
                              (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
                        (∀ r : Homogenization.Mat d,
                          r = Homogenization.HighContrast.roundedGrid jStar mp ∨
                            r = Homogenization.HighContrast.roundedGrid jStar mv →
                          ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
                            Homogenization.HighContrast.adaptedCell r j ⊆
                              Homogenization.HighContrast.centeredCube d M) →
                        Homogenization.BlockMatLoewnerLE
                            (Homogenization.HighContrast.blockSub
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mv)
                                nn)
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                (nn - l)))
                            (Homogenization.HighContrast.blockScale
                              (Homogenization.HighContrast.bridgeErrUpper C Cd g
                                (Homogenization.HighContrast.initExpRhoDr g)
                                (Homogenization.HighContrast.gridRatio
                                  (Homogenization.HighContrast.roundedGrid jStar mp)
                                  (Homogenization.HighContrast.roundedGrid jStar mv))
                                P E jStar mp mv nn l)
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                nn)) ∧
                          Homogenization.BlockMatLoewnerLE
                            (Homogenization.HighContrast.blockScale
                              (-Homogenization.HighContrast.bridgeErrLower C Cd g
                                (Homogenization.HighContrast.initExpRhoDr g)
                                (Homogenization.HighContrast.gridRatio
                                  (Homogenization.HighContrast.roundedGrid jStar mp)
                                  (Homogenization.HighContrast.roundedGrid jStar mv))
                                P E jStar mp mv nn l)
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                (nn + l)))
                            (Homogenization.HighContrast.blockSub
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mv)
                                nn)
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mp)
                                (nn + l))) ∧
                          ∀ eta : ℝ, 0 ≤ eta → eta ≤ 1 / 4 →
                            Homogenization.BlockMatLoewnerLE
                              (Homogenization.HighContrast.blockScale (1 - eta)
                                (Homogenization.HighContrast.adaptedMean P
                                  (Homogenization.HighContrast.roundedGrid jStar mp)
                                  (nn + l)))
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mv)
                                nn) →
                            Homogenization.HighContrast.linearDrift P
                                (Homogenization.HighContrast.initExpRhoDr g)
                                (Homogenization.HighContrast.roundedGrid jStar mv)
                                jStar nn ≤
                              C *
                                (eta +
                                  Homogenization.HighContrast.gridRatio
                                      (Homogenization.HighContrast.roundedGrid jStar
                                        mp)
                                      (Homogenization.HighContrast.roundedGrid jStar
                                        mv) *
                                    (3 : ℝ) ^ (-(l : ℝ)) +
                                  (1 +
                                      Homogenization.HighContrast.gridRatio
                                        (Homogenization.HighContrast.roundedGrid
                                          jStar mp)
                                        (Homogenization.HighContrast.roundedGrid
                                          jStar mv)) *
                                    (3 : ℝ) ^
                                      (2 *
                                        Homogenization.HighContrast.initExpRhoDr g *
                                        (l : ℝ)) *
                                    Homogenization.HighContrast.linearDrift P
                                      (Homogenization.HighContrast.initExpRhoDr g)
                                      (Homogenization.HighContrast.roundedGrid jStar
                                        mp)
                                      jStar (nn + l) +
                                  Homogenization.HighContrast.bridgeShiftedRemainder
                                    C Cd g
                                    (Homogenization.HighContrast.initExpRhoDr g) E
                                    jStar mp mv nn l)) →
                    -- the retained finite prefix
                    ∀ (k : ℕ) (mus : ℕ → Homogenization.Mat d) (ss : ℕ → ℤ)
                      (r0 : ℤ),
                      (∀ i : ℕ, i ≤ k → (mus i).PosDef) →
                      mus 0 = 1 →
                      (∀ i : ℕ, i < k →
                        Homogenization.HighContrast.projDist (mus i) (mus (i + 1)) ≤
                          chop) →
                      (∀ i : ℕ, i < k →
                        Homogenization.HighContrast.gridRatio
                            (Homogenization.HighContrast.roundedGrid jStar (mus i))
                            (Homogenization.HighContrast.roundedGrid jStar
                              (mus (i + 1))) ≤ Khop) →
                      r0 ≤ ss 0 →
                      (∀ i : ℕ, i < k → ss i + (l0 : ℤ) ≤ ss (i + 1)) →
                      B * Real.logb 3 (2 + Homogenization.HighContrast.aspectRatio E) ≤
                        (r0 : ℝ) - (jStar : ℝ) →
                      ∀ u : ℤ, ss k ≤ u →
                        -- the determinant test preceding a change of geometry
                        Homogenization.HighContrast.linearDrift P
                            (Homogenization.HighContrast.initExpRhoDr g)
                            (Homogenization.HighContrast.roundedGrid jStar (mus k))
                            jStar u ≤ etaPre →
                        Homogenization.HighContrast.adaptedDetRoot P
                            (Homogenization.HighContrast.roundedGrid jStar (mus k))
                            u ≤
                          (1 + deltaShort) *
                            Homogenization.HighContrast.adaptedDetRoot P
                              (Homogenization.HighContrast.roundedGrid jStar (mus k))
                              (u + 2 * (l0 : ℤ)) →
                        -- the candidate: the next point on the fixed path
                        ∀ mu' : Homogenization.Mat d,
                          mu' =
                            Homogenization.HighContrast.projPathStep chop (mus k)
                              (Homogenization.HighContrast.canonicalMetric
                                (Homogenization.HighContrast.adaptedMean P
                                  (Homogenization.HighContrast.roundedGrid jStar
                                    (mus k))
                                  (u + 2 * (l0 : ℤ)))) →
                          -- every cell read lies in the window
                          (∀ r : Homogenization.Mat d,
                            r =
                                Homogenization.HighContrast.roundedGrid jStar
                                  (mus k) ∨
                              r = Homogenization.HighContrast.roundedGrid jStar mu' →
                            ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * (l0 : ℤ) →
                              Homogenization.HighContrast.adaptedCell r j ⊆
                                Homogenization.HighContrast.centeredCube d M) →
                          -- the candidate is a positive witness at a bounded
                          -- projective jump, so the rounded hop is bounded
                          mu'.PosDef ∧
                            Homogenization.HighContrast.projDist (mus k) mu' ≤
                              chop ∧
                            Homogenization.HighContrast.gridRatio
                                (Homogenization.HighContrast.roundedGrid jStar
                                  (mus k))
                                (Homogenization.HighContrast.roundedGrid jStar
                                  mu') ≤ Khop ∧
                          -- `e.successful.short.near`
                          Homogenization.BlockMatLoewnerLE
                              (Homogenization.HighContrast.blockScale (1 - etaX)
                                (Homogenization.HighContrast.adaptedMean P
                                  (Homogenization.HighContrast.roundedGrid jStar
                                    (mus k))
                                  (u + 2 * (l0 : ℤ))))
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mu')
                                (u + (l0 : ℤ))) ∧
                            Homogenization.BlockMatLoewnerLE
                              (Homogenization.HighContrast.adaptedMean P
                                (Homogenization.HighContrast.roundedGrid jStar mu')
                                (u + (l0 : ℤ)))
                              (Homogenization.HighContrast.blockScale (1 + etaX)
                                (Homogenization.HighContrast.adaptedMean P
                                  (Homogenization.HighContrast.roundedGrid jStar
                                    (mus k))
                                  (u + 2 * (l0 : ℤ)))) ∧
                            Homogenization.HighContrast.linearDrift P
                                (Homogenization.HighContrast.initExpRhoDr g)
                                (Homogenization.HighContrast.roundedGrid jStar mu')
                                jStar (u + (l0 : ℤ)) ≤ etaNew
    := by
  exact Homogenization.HighContrast.ShortHop.short_hop_assembly d hd g hg chop hchop etaNew
    hetaNewLo hetaNewHi etaX hetaXLo hetaXHi Lcommon Khop hKhop hhop Ltr hLtr C hC
