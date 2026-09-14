/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.ReferenceComparison
import HCPoly.Provider.ShortHop.BootstrapThresholds
import HCPoly.Provider.ShortHop.DriftEnvelopes
import HCPoly.Provider.ShortHop.PathStep
import HCPoly.Provider.ShortHop.PrefixScales
import HCPoly.Provider.ShortHop.ShortHopCore
import HCPoly.Provider.ShortHop.SourceBounds

/-!
# The assembly of `p.successful.short.bridge`

The successful short test, composed from the short-hop development.

The five thresholds and the four constants requirements are the ordered choice
`exists_short_thresholds_of_const`, read at the structural constant of the
hop-index bootstrap: the product of the two-grid constant, the source
coefficient's cubic factor in the dimensional constant, the linear-factor
absorption, the collapsing exponential, and the fixed shift `3^{ρ_dr ℓ₀}` that
the shifted remainder carries.  That constant is chosen before the hop length,
as a function of it, which is exactly the shape the ordered choice admits, and
reading its uniform clause at the reference aspect ratio discharges both source
hypotheses at once — the shifted one directly, the comparison one because the
fixed shift is at least one.

The law clause is then the printed proof.  The prefix bookkeeping
(`scale_recursion`, `projDist_prefix`) puts the entry scale plus `k` hop lengths
below the test scale and the identity witness within `k` hop lengths of the
`k`-th witness; the candidate clauses (`candidate_of_short_test`) add one more
hop, so both witnesses are within `k+1` hop lengths of the identity, which is
the hypothesis of the amortized source bounds.  The alignment
(`kZero_le_of_isCoupledWindow`) lets the rounded-hop bound be read at the
window's alignment scale, in both directions.  The entry-scale clause is not
vacuous (`lt_entry_scale`), and with the scale recursion it places the alignment
scale below the test scale.  The two-grid data is destructured at the
intermediate scale, its two side conditions coming from the constants
requirements and the monotonicity of the logarithm, and
`shortHop_conclusion` closes.

The reference-ratio bound the amortized source bounds carry is
`Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger`, the
factor-six reference-block comparison for the coarse ellipticity datum this
statement already binds.
-/

namespace Homogenization
namespace HighContrast
namespace ShortHop

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

/-- **`p.successful.short.bridge`.**  After a retained finite prefix
of bounded projective hops, a cursor that passes the drift test and the
determinant test admits one further path step: the annealed block of the new
grid at the intermediate scale is a near isometry of the old grid's terminal
block, and the new grid's weighted determinant drift is below the prescribed
allowance. -/
theorem short_hop_assembly
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
                          -- the conclusion `e.successful.short.near`
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
  intro Cd hCd
  -- the drift allowance being below one and the transport threshold being at
  -- least one are premises of the printed statement that the proof never reads:
  -- the first constrains only the consumer, the second only through the buffer
  have _hetaNewHi := hetaNewHi
  have _hLtr := hLtr
  have hg1 : g < 1 := hg.2
  have hd0 : d ≠ 0 := by omega
  have : NeZero d := ⟨hd0⟩
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hCd0 : (0 : ℝ) ≤ Cd := le_trans zero_le_one hCd
  have hKhop0 : (0 : ℝ) ≤ Khop := le_trans zero_le_one hKhop
  have hrho : (0 : ℝ) < initExpRhoDr g := initExpRhoDr_pos hg1
  have hL3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hchi : (0 : ℝ) < chiG g := zero_lt_chiG hg1
  have hM0 : (0 : ℝ) < 1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1) := by
    have h2 : (0 : ℝ) ≤ Khop * chiG g + 1 := by
      have := mul_nonneg hKhop0 hchi.le
      linarith only [this]
    have hprod := mul_nonneg (mul_nonneg (by linarith only [hCd0] : (0 : ℝ) ≤ 24 * Cd)
      (sq_nonneg (Cd * zetaG g))) h2
    linarith only [hprod]
  have hCr : (0 : ℝ) < 1 + 2 / (initExpRhoDr g * Real.log 3) := by
    have hdiv := div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hrho hL3)
    linarith only [hdiv]
  -- the structural constant of the hop-index bootstrap, as a function of the hop length
  have hCboot : ∀ n : ℕ,
      0 < (3 : ℝ) ^ (initExpRhoDr g * (n : ℝ)) * C *
          (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
          (1 + 2 / (initExpRhoDr g * Real.log 3)) *
        Real.exp (2 * chop - initExpRhoDr g * (n : ℝ) * Real.log 3 / 2) := fun n =>
    mul_pos (mul_pos (mul_pos (mul_pos
      (Real.rpow_pos_of_pos (by norm_num) _) hC) hM0) hCr) (Real.exp_pos _)
  obtain ⟨l0, hl0common, tauSrc, htau, deltaShort, hdeltaPos, etaPre, hetaPrePos, B, hBpos,
      hl0log, hl0half, hl0strict, hBstrict, hthr, hunif⟩ :=
    exists_short_thresholds_of_const d Lcommon Ltr _ hCboot hg1 hetaNewLo hetaXLo hC hKhop
  refine ⟨l0, hl0common, tauSrc, htau, deltaShort, hdeltaPos, etaPre, hetaPrePos, B, hBpos,
    hl0log, hl0half, hl0strict, hBstrict, hthr, ?_⟩
  intro P E Ψ K S hPprob hstat _hunitLaw hdag jStar M hw Y hY hsd k mus ss r0
    hmusPos hmus0 hmusJump _hmusRatio hr0 hstepScale hentry u huk hshort hdetTest mu' hmu'def hcont
  have : IsProbabilityMeasure P := hPprob
  -- the casts of the hop length
  have hcastl0 : (((l0 : ℕ) : ℤ) : ℝ) = ((l0 : ℕ) : ℝ) := by push_cast; ring
  have hl0Z : (0 : ℤ) ≤ ((l0 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hl0R : (0 : ℝ) ≤ (((l0 : ℕ) : ℤ) : ℝ) := by rw [hcastl0]; positivity
  have hl0logZ : C * (1 + Real.log Khop) ≤ (((l0 : ℕ) : ℤ) : ℝ) := by
    rw [hcastl0]; exact hl0log
  have hl0halfZ : C * Khop * (3 : ℝ) ^ (-(((l0 : ℕ) : ℤ) : ℝ)) ≤ 1 / 2 := by
    rw [hcastl0]; exact hl0half
  have hl0strictZ : 2 * chop <
      initExpRhoDr g * (((l0 : ℕ) : ℤ) : ℝ) * Real.log 3 / 2 := by
    rw [hcastl0]; exact hl0strict
  -- the prefix bookkeeping
  have hmuk : (mus k).PosDef := hmusPos k le_rfl
  have hjr0 : jStar < r0 := lt_entry_scale hdag hBpos hentry
  have hss0k : ss 0 + (k : ℤ) * ((l0 : ℕ) : ℤ) ≤ ss k := scale_recursion hstepScale
  have hkl0 : (0 : ℤ) ≤ (k : ℤ) * ((l0 : ℕ) : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) hl0Z
  have hju : jStar ≤ u := by linarith only [hjr0, hr0, hss0k, huk, hkl0]
  have hscaleZ : r0 + (k : ℤ) * ((l0 : ℕ) : ℤ) ≤ u := by
    linarith only [hr0, hss0k, huk]
  have hscale : (r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (((l0 : ℕ) : ℤ) : ℝ) ≤
      (u : ℝ) + (((l0 : ℕ) : ℤ) : ℝ) - (jStar : ℝ) := by
    have h : ((r0 + (k : ℤ) * ((l0 : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((u : ℤ) : ℝ) :=
      Int.cast_le.mpr hscaleZ
    push_cast at h ⊢
    linarith only [h]
  -- the candidate
  have hcontOld : ∀ j : ℤ, jStar ≤ j → j ≤ u + 2 * ((l0 : ℕ) : ℤ) →
      adaptedCell (roundedGrid jStar (mus k)) j ⊆ centeredCube d M :=
    fun j hj hj2 => hcont _ (Or.inl rfl) j hj hj2
  have hEt : (toFullBlockMat (adaptedMean P (roundedGrid jStar (mus k))
      (u + 2 * ((l0 : ℕ) : ℤ)))).PosDef :=
    posDef_adaptedMean_of_window hw hY hmuk (by omega) le_rfl hcontOld
  obtain ⟨hmu'pos, hmu'dist⟩ := candidate_of_short_test hchop.le hmuk hEt hmu'def
  have hKfac : gridRatio (roundedGrid jStar (mus k)) (roundedGrid jStar mu') ≤ Khop :=
    hhop jStar (kZero_le_of_isCoupledWindow hw) (mus k) mu' hmuk hmu'pos hmu'dist
  have hKfac' : gridRatio (roundedGrid jStar mu') (roundedGrid jStar (mus k)) ≤ Khop :=
    hhop jStar (kZero_le_of_isCoupledWindow hw) mu' (mus k) hmu'pos hmuk
      (by rw [projDist_comm]; exact hmu'dist)
  -- the two projective prefixes
  have hone : (1 : Mat d).PosDef := Matrix.PosDef.one
  have hpre0 : projDist (mus 0) (mus k) ≤ (k : ℝ) * chop :=
    projDist_prefix hmusPos hmusJump k le_rfl
  have hpre0' : projDist (1 : Mat d) (mus k) ≤ (k : ℝ) * chop := by
    rw [← hmus0]; exact hpre0
  have hprefix : projDist (1 : Mat d) (mus k) ≤ ((k : ℝ) + 1) * chop := by
    have := hchop.le
    nlinarith only [hpre0', this]
  have hprefix' : projDist (1 : Mat d) mu' ≤ ((k : ℝ) + 1) * chop := by
    have htri := projDist_triangle hone hmuk hmu'pos
    nlinarith only [htri, hpre0', hmu'dist]
  -- the reference quantities of the coarse ellipticity datum
  have hPi : 1 ≤ aspectRatio E := one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hkap : kappaRef E ≤ 6 * aspectRatio E :=
    Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag
  -- the uniform source bound, at the reference aspect ratio
  have h2Pi : (0 : ℝ) < 2 + aspectRatio E := by linarith only [hPi]
  have hrp : (0 : ℝ) < (2 + aspectRatio E) ^ (1 - initExpRhoDr g * B / 2) :=
    Real.rpow_pos_of_pos h2Pi _
  have hunifSh : (3 : ℝ) ^ (initExpRhoDr g * (((l0 : ℕ) : ℤ) : ℝ)) * C *
          (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
          (1 + 2 / (initExpRhoDr g * Real.log 3)) *
          Real.exp (2 * chop -
            initExpRhoDr g * (((l0 : ℕ) : ℤ) : ℝ) * Real.log 3 / 2) *
        (2 + aspectRatio E) ^ (1 - initExpRhoDr g * B / 2) ≤ tauSrc := by
    rw [hcastl0]
    exact hunif (aspectRatio E) hPi
  have hunifCmp : C *
          (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
          (1 + 2 / (initExpRhoDr g * Real.log 3)) *
          Real.exp (2 * chop -
            initExpRhoDr g * (((l0 : ℕ) : ℤ) : ℝ) * Real.log 3 / 2) *
        (2 + aspectRatio E) ^ (1 - initExpRhoDr g * B / 2) ≤ tauSrc := by
    refine le_trans ?_ hunifSh
    have h3ge : (1 : ℝ) ≤ (3 : ℝ) ^ (initExpRhoDr g * (((l0 : ℕ) : ℤ) : ℝ)) := by
      have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
        (mul_nonneg hrho.le hl0R)
      rwa [Real.rpow_zero] at h
    have hXpos : (0 : ℝ) < C *
        (1 + 24 * Cd * (Cd * zetaG g) ^ 2 * (Khop * chiG g + 1)) *
        (1 + 2 / (initExpRhoDr g * Real.log 3)) *
        Real.exp (2 * chop -
          initExpRhoDr g * (((l0 : ℕ) : ℤ) : ℝ) * Real.log 3 / 2) *
        (2 + aspectRatio E) ^ (1 - initExpRhoDr g * B / 2) :=
      mul_pos (mul_pos (mul_pos (mul_pos hC hM0) hCr) (Real.exp_pos _)) hrp
    nlinarith only [h3ge, hXpos]
  -- the two-grid data at the intermediate scale
  have hgr1 : (1 : ℝ) ≤ gridRatio (roundedGrid jStar (mus k)) (roundedGrid jStar mu') :=
    Transport.one_le_gridRatio _ _
  have hlogside : C * (1 + Real.log (gridRatio (roundedGrid jStar (mus k))
      (roundedGrid jStar mu'))) ≤ (((l0 : ℕ) : ℤ) : ℝ) := by
    have hlog : Real.log (gridRatio (roundedGrid jStar (mus k)) (roundedGrid jStar mu')) ≤
        Real.log Khop := Real.log_le_log (by linarith only [hgr1]) hKfac
    have hstep := mul_le_mul_of_nonneg_left (by linarith only [hlog] :
      1 + Real.log (gridRatio (roundedGrid jStar (mus k)) (roundedGrid jStar mu')) ≤
        1 + Real.log Khop) hC.le
    linarith only [hstep, hl0logZ]
  have hdenside : C * gridRatio (roundedGrid jStar (mus k)) (roundedGrid jStar mu') *
      (3 : ℝ) ^ (-(((l0 : ℕ) : ℤ) : ℝ)) ≤ 1 / 2 := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(((l0 : ℕ) : ℤ) : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hstep := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKfac hC.le) h3.le
    linarith only [hstep, hl0halfZ]
  obtain ⟨hcmpUp, hcmpLo, hsdrift⟩ := hsd (mus k) mu' hmuk hmu'pos
    (u + ((l0 : ℕ) : ℤ)) ((l0 : ℕ) : ℤ) (by omega) hlogside hdenside
    (fun r hr j hj hj2 => hcont r hr j hj (by omega))
  have hshiftLo : u + ((l0 : ℕ) : ℤ) - ((l0 : ℕ) : ℤ) = u := by ring
  have hshiftHi : u + ((l0 : ℕ) : ℤ) + ((l0 : ℕ) : ℤ) = u + 2 * ((l0 : ℕ) : ℤ) := by ring
  rw [hshiftLo] at hcmpUp
  rw [hshiftHi] at hcmpLo
  rw [hshiftHi] at hsdrift
  -- the two casts the amortized source bounds are read through
  have hcastA : ((u + ((l0 : ℕ) : ℤ) : ℤ) : ℝ) = (u : ℝ) + (((l0 : ℕ) : ℤ) : ℝ) := by
    push_cast; ring
  have hcastB : ((u + 2 * ((l0 : ℕ) : ℤ) : ℤ) : ℝ) =
      (u : ℝ) + 2 * (((l0 : ℕ) : ℤ) : ℝ) := by push_cast; ring
  refine ⟨hmu'pos, hmu'dist, hKfac, ?_⟩
  refine shortHop_conclusion hd0 hstat hw hY hmuk hju hl0Z hcontOld hC.le hKfac
    hl0halfZ hetaPrePos.le hdeltaPos.le hetaXHi hdetTest hthr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hcmpUp hcmpLo hsdrift
  · exact zero_le_bridgeCmpRemainder hC.le hCd0 hg1 E (by omega) (mus k) mu'
  · exact bridgeCmpRemainder_le_tauSrc (Pi := aspectRatio E) (r0 := r0)
      (l0 := ((l0 : ℕ) : ℤ)) (k := k) hC.le hCd0 hg1 hrho hchop.le hmuk hmu'pos hPi hkap
      hKfac hKfac' hprefix hprefix' (by omega) (by rw [hcastA]; exact hscale) hentry
      hl0strictZ hunifCmp
  · exact zero_le_bridgeCmpRemainder hC.le hCd0 hg1 E (by omega) mu' (mus k)
  · exact bridgeCmpRemainder_le_tauSrc (Pi := aspectRatio E) (r0 := r0)
      (l0 := ((l0 : ℕ) : ℤ)) (k := k) hC.le hCd0 hg1 hrho hchop.le hmu'pos hmuk hPi hkap
      hKfac' hKfac hprefix' hprefix (by omega)
      (by rw [hcastB]; linarith only [hscale, hl0R]) hentry hl0strictZ hunifCmp
  · exact zero_le_bridgeShiftedRemainder hC.le hCd0 hg1 E (by omega) (mus k) mu'
      ((l0 : ℕ) : ℤ)
  · exact bridgeShiftedRemainder_le_tauSrc (Pi := aspectRatio E) (r0 := r0)
      (l0 := ((l0 : ℕ) : ℤ)) (k := k) hC.le hCd0 hg1 hrho hchop.le hmuk hmu'pos hPi hkap
      hKfac hKfac' hprefix hprefix' (by omega) (by rw [hcastA]; exact hscale) hentry
      hl0strictZ hunifSh
  · exact linearDrift_le_shortDriftNew hd0 hstat hw hY hmuk hju hl0Z hcontOld hrho.le
      hdeltaPos.le hshort hdetTest
  · exact linearDrift_le_shortDriftTerm hd0 hstat hw hY hmuk hju hl0Z hcontOld hrho.le
      hshort hdetTest

end

end ShortHop
end HighContrast
end Homogenization
