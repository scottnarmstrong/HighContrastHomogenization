/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchFixed
import HCPoly.Provider.Selection.HopTrace
import HCPoly.Provider.Selection.AlignedSelectionConstants
import HCPoly.Provider.Selection.TransitionGuards

/-!
# The short-hop part of the projective branch

The successful determinant test and the retained shifted-drift provider give
the geometric and drift data for the prescribed hop update.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

private theorem drift_le_of_index_zero {P : Measure (CoeffSpace d)}
    {rhoDr etaPre : ℝ} (hetaPre : 0 < etaPre) {jStar : ℤ} {S : State d}
    (hzero : driftIndex P rhoDr etaPre jStar S = 0) :
    linearDrift P rhoDr S.q jStar S.cursor ≤ etaPre := by
  rw [driftIndex] at hzero
  have hlog := Nat.ceil_eq_zero.mp hzero
  have hx : 0 < max 1 (linearDrift P rhoDr S.q jStar S.cursor / etaPre) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hmax := (Real.logb_nonpos_iff (by norm_num : (1 : ℝ) < 2) hx).mp hlog
  have hratio := (le_max_right (1 : ℝ)
    (linearDrift P rhoDr S.q jStar S.cursor / etaPre)).trans hmax
  exact (div_le_one hetaPre).mp hratio

private theorem preHopData (hd : 2 ≤ d) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P) {jStar : ℤ} {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      c.deltaShort c.deltaTerm c.l0 H .t5 S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + 2 * (c.l0 : ℤ))) :
    portableProfile P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        S.q jStar S.checkpoint (S.cursor + 2 * (c.l0 : ℤ)) ≤
        ENNReal.ofReal c.etaHop ∧
      linearDrift P (initExpRhoDr g) S.q jStar S.cursor ≤ c.etaPre ∧
      adaptedDetRoot P S.q S.cursor ≤ (1 + c.deltaShort) *
        adaptedDetRoot P S.q (S.cursor + 2 * (c.l0 : ℤ)) := by
  let t0 : ℤ := S.cursor + 2 * (c.l0 : ℤ)
  have hl0 : 1 ≤ c.l0 := c.transportData.one_le_Ltr.trans
    ((le_max_right c.Lcommon Ltr).trans c.l0_lower)
  have hjcursor := hexact.2.2.2.2.1.trans hexact.2.2.2.2.2
  rcases hsearch with ⟨-, hstart, -⟩
  rcases hguard with ⟨-, hzero, hprofile, hpass⟩
  obtain ⟨-, -, -, -, -, -, -, hprop, -⟩ :=
    c.portableData.law P inferInstance hstat hunit jStar S.q hread.rounded
      jStar S.checkpoint t0 le_rfl hexact.2.2.2.2.1
      (hexact.2.2.2.2.2.trans (by dsimp [t0]; omega))
      hread.finiteMean hread.positiveMean hread.finiteMoment
  have hprofileOne : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S ≤ 1 := hprofile.trans <| by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal c.etaReady_le_one
  have hpreRaw := hprop (2 * (c.l0 : ℤ)) S.cursor (by omega) hstart
    (by omega) hprofileOne
  have hu := posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q S.cursor)
    (hread.positiveMean S.cursor hjcursor (by omega))
  have hv := posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P S.q t0)
    (hread.positiveMean t0 (hjcursor.trans (by dsimp [t0]; omega)) le_rfl)
  have hdetTest := (shortTest_passes_iff P c.deltaShort c.l0 S
    (ShortHop.detRoot_pos hv)).mp hpass
  have huRoot : 0 < adaptedDetRoot P S.q S.cursor := by
    simpa [adaptedDetRoot] using ShortHop.detRoot_pos hu
  have hvRoot : 0 < adaptedDetRoot P S.q t0 := by
    simpa [adaptedDetRoot] using ShortHop.detRoot_pos hv
  have hloss : detLoss P S.q S.cursor t0 ≤ Real.log (1 + c.deltaShort) := by
    rw [detLoss, ← Real.log_div huRoot.ne' hvRoot.ne']
    exact Real.log_le_log (div_pos huRoot hvRoot)
      ((div_le_iff₀ hvRoot).2 (by simpa [t0] using hdetTest))
  have hinc : detIncrement P S.q S.cursor t0 ≤
      (d : ℝ) * Real.log (1 + c.deltaShort) := by
    rw [detIncrement_eq_natCast_mul_detLoss (by omega : d ≠ 0) hu hv]
    exact mul_le_mul_of_nonneg_left hloss (Nat.cast_nonneg d)
  have hexp := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hinc (Nat.cast_nonneg (initExpQ d g)))
  have hpre : portableProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) S.q jStar S.checkpoint t0 ≤ ENNReal.ofReal c.etaHop := by
    refine hpreRaw.trans ?_
    have hA : 0 ≤ c.AL (2 * (c.l0 : ℤ)) := (c.AL_pos _ (by omega)).le
    have hfirst : ENNReal.ofReal (c.AL (2 * (c.l0 : ℤ))) *
        stateProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) jStar S ≤ ENNReal.ofReal (c.etaHop / 4) := by
      calc
        _ ≤ ENNReal.ofReal (c.AL (2 * (c.l0 : ℤ))) * ENNReal.ofReal c.etaReady :=
          mul_le_mul_right hprofile _
        _ = ENNReal.ofReal (c.AL (2 * (c.l0 : ℤ)) * c.etaReady) := by
          rw [ENNReal.ofReal_mul hA]
        _ ≤ ENNReal.ofReal (c.etaHop / 4) := ENNReal.ofReal_le_ofReal c.ready_share
    have hsecond : ENNReal.ofReal (c.AL (2 * (c.l0 : ℤ)) *
        (Real.exp ((initExpQ d g : ℝ) * detIncrement P S.q S.cursor t0) - 1)) ≤
        ENNReal.ofReal (c.etaHop / 4) := ENNReal.ofReal_le_ofReal <| by
      exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1) hA).trans
        (by simpa only [mul_assoc] using c.short_det_share)
    calc
      _ ≤ ENNReal.ofReal (c.etaHop / 4) + ENNReal.ofReal (c.etaHop / 4) :=
        add_le_add hfirst hsecond
      _ = ENNReal.ofReal (c.etaHop / 2) := by
        have hquarter : 0 ≤ c.etaHop / 4 := div_nonneg c.etaHop_pos.le (by norm_num)
        rw [← ENNReal.ofReal_add hquarter hquarter]
        congr 1
        ring
      _ ≤ ENNReal.ofReal c.etaHop := ENNReal.ofReal_le_ofReal (by
        linarith only [c.etaHop_pos])
  exact ⟨by simpa only [t0] using hpre, drift_le_of_index_zero c.etaPre_pos hzero,
    by simpa only [t0] using hdetTest⟩

private theorem applyShortHopProvider
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
    {B : ℝ}
    (shortData : ShortHopProviderData d g c.chop c.etaNew c.etaX Khop Ctr Cd
      c.l0 c.tauSrc c.deltaShort c.etaPre B)
    {k : ℕ} (mus : ℕ → Mat d) (ss : ℕ → ℤ) {r0 u : ℤ}
    (hmus : ∀ i : ℕ, i ≤ k → (mus i).PosDef) (hmus0 : mus 0 = 1)
    (hjump : ∀ i : ℕ, i < k → projDist (mus i) (mus (i + 1)) ≤ c.chop)
    (hratio : ∀ i : ℕ, i < k → gridRatio (roundedGrid jStar (mus i))
      (roundedGrid jStar (mus (i + 1))) ≤ Khop)
    (hr0 : r0 ≤ ss 0) (hstep : ∀ i : ℕ, i < k → ss i + (c.l0 : ℤ) ≤ ss (i + 1))
    (hentry : B * Real.logb 3 (2 + aspectRatio E) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hsku : ss k ≤ u)
    (hdrift : linearDrift P (initExpRhoDr g) (roundedGrid jStar (mus k))
      jStar u ≤ c.etaPre)
    (hdet : adaptedDetRoot P (roundedGrid jStar (mus k)) u ≤
      (1 + c.deltaShort) * adaptedDetRoot P (roundedGrid jStar (mus k))
        (u + 2 * (c.l0 : ℤ)))
    {mu' : Mat d}
    (hmu' : mu' = projPathStep c.chop (mus k)
      (canonicalMetric (adaptedMean P (roundedGrid jStar (mus k))
        (u + 2 * (c.l0 : ℤ)))))
    (hcont : ∀ r : Mat d, r = roundedGrid jStar (mus k) ∨
      r = roundedGrid jStar mu' → ∀ j : ℤ, jStar ≤ j →
      j ≤ u + 2 * (c.l0 : ℤ) → adaptedCell r j ⊆ centeredCube d M) :
    mu'.PosDef ∧ projDist (mus k) mu' ≤ c.chop ∧
      gridRatio (roundedGrid jStar (mus k)) (roundedGrid jStar mu') ≤ Khop ∧
      BlockMatLoewnerLE (blockScale (1 - c.etaX)
        (adaptedMean P (roundedGrid jStar (mus k)) (u + 2 * (c.l0 : ℤ))))
        (adaptedMean P (roundedGrid jStar mu') (u + (c.l0 : ℤ))) ∧
      BlockMatLoewnerLE (adaptedMean P (roundedGrid jStar mu') (u + (c.l0 : ℤ)))
        (blockScale (1 + c.etaX)
          (adaptedMean P (roundedGrid jStar (mus k)) (u + 2 * (c.l0 : ℤ)))) ∧
      linearDrift P (initExpRhoDr g) (roundedGrid jStar mu') jStar
        (u + (c.l0 : ℤ)) ≤ c.etaNew := by
  exact shortData.law P E Psi K source inferInstance hstat hunit hdag jStar M hwin
    Y hY hbridge k mus ss r0 hmus hmus0 hjump hratio hr0 hstep hentry u hsku
    hdrift hdet mu' hmu' hcont

/-- The aligned shifted-drift law supplies the geometric and drift components
of the prescribed hop, together with the profile entering transport. -/
theorem branchT5Short_of_providerData (hd : 2 ≤ d)
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
    {B : ℝ}
    (shortData : ShortHopProviderData d g c.chop c.etaNew c.etaX Khop Ctr Cd
      c.l0 c.tauSrc c.deltaShort c.etaPre B)
    {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      c.deltaShort c.deltaTerm c.l0 H .t5 S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + 2 * (c.l0 : ℤ)))
    {r0 : ℤ} {k : ℕ} (cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 k)
    (hmu : cert.mus k = S.mu) (hstage : cert.starts k ≤ S.cursor)
    (hentry : B * Real.logb 3 (2 + aspectRatio E) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hcont : ∀ r : Mat d, r = S.q ∨
        r = (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          jStar c.chop c.l0 S).q → ∀ j : ℤ,
      jStar ≤ j → j ≤ S.cursor + 2 * (c.l0 : ℤ) →
        adaptedCell r j ⊆ centeredCube d M) :
    let S' := hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
      jStar c.chop c.l0 S
    portableProfile P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        S.q jStar S.checkpoint (S.cursor + 2 * (c.l0 : ℤ)) ≤ ENNReal.ofReal c.etaHop ∧
      S'.mu.PosDef ∧ projDist S.mu S'.mu ≤ c.chop ∧ gridRatio S.q S'.q ≤ Khop ∧
      BlockMatLoewnerLE (blockScale (1 - c.etaX)
        (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ))))
        (adaptedMean P S'.q (S.cursor + (c.l0 : ℤ))) ∧
      BlockMatLoewnerLE (adaptedMean P S'.q (S.cursor + (c.l0 : ℤ)))
        (blockScale (1 + c.etaX)
          (adaptedMean P S.q (S.cursor + 2 * (c.l0 : ℤ)))) ∧
      linearDrift P (initExpRhoDr g) S'.q jStar S'.cursor ≤ c.etaNew := by
  dsimp only
  let t0 : ℤ := S.cursor + 2 * (c.l0 : ℤ)
  let F : BlockMat d := adaptedMean P S.q t0
  let mu' : Mat d := projPathStep c.chop S.mu (canonicalMetric F)
  obtain ⟨hpre, hdriftOld, hdetTest⟩ :=
    preHopData (c := c) hd hstat hunit hexact hsearch hguard hread
  have hmus : S.mu.PosDef := by rw [← hmu]; exact cert.mus_pos k le_rfl
  have hratioCert : ∀ i : ℕ, i < k → gridRatio
      (roundedGrid jStar (cert.mus i)) (roundedGrid jStar (cert.mus (i + 1))) ≤ Khop := by
    intro i hi
    simpa only [cert.grids_eq i hi.le, cert.grids_eq (i + 1) (by omega)] using
      cert.grid_step i hi
  have hcont' : ∀ r : Mat d,
      r = roundedGrid jStar (cert.mus k) ∨ r = roundedGrid jStar mu' →
      ∀ j : ℤ, jStar ≤ j → j ≤ S.cursor + 2 * (c.l0 : ℤ) →
        adaptedCell r j ⊆ centeredCube d M := by
    intro r hr j hj hjt
    apply hcont r _ j hj hjt
    rcases hr with hr | hr
    · exact Or.inl (hr.trans (by rw [hmu]; exact hexact.1.symm))
    · exact Or.inr (hr.trans (by simp [hopState, mu', F, t0]))
  obtain ⟨hmu'pos, hjump, hratio, hlo, hhi, hdriftNew⟩ :=
    applyShortHopProvider (mu' := mu') hstat hunit hdag hwin hY hbridge shortData
      cert.mus cert.starts cert.mus_pos
      cert.mus_zero cert.hop_step hratioCert cert.starts_zero cert.scale_step
      hentry hstage (by simpa [hexact.1, hmu] using hdriftOld)
      (by simpa [hexact.1, hmu, t0] using hdetTest)
      (by simp [mu', F, t0, hmu, ← hexact.1]) hcont'
  refine ⟨hpre, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change mu'.PosDef
    exact hmu'pos
  · change projDist S.mu mu' ≤ c.chop
    simpa only [hmu] using hjump
  · change gridRatio S.q (roundedGrid jStar mu') ≤ Khop
    simpa only [hmu, ← hexact.1] using hratio
  · change BlockMatLoewnerLE (blockScale (1 - c.etaX) (adaptedMean P S.q t0))
      (adaptedMean P (roundedGrid jStar mu') (S.cursor + (c.l0 : ℤ)))
    simpa only [hmu, ← hexact.1] using hlo
  · change BlockMatLoewnerLE
      (adaptedMean P (roundedGrid jStar mu') (S.cursor + (c.l0 : ℤ)))
      (blockScale (1 + c.etaX) (adaptedMean P S.q t0))
    simpa only [hmu, ← hexact.1] using hhi
  · change linearDrift P (initExpRhoDr g) (roundedGrid jStar mu') jStar
      (S.cursor + (c.l0 : ℤ)) ≤ c.etaNew
    exact hdriftNew

end

end Homogenization.HighContrast.Selection
