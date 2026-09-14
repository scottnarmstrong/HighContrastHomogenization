/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.BranchHopShort

/-!
# Transported analytic data for the projective-hop branch

The grid-transport provider turns the short-hop geometry into the history and
profile bounds of the new selector state.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}

/-- Aligned short-hop and transport providers control the state prescribed by
the T5 update. -/
theorem branchT5Transport_of_alignedConstant (hd : 2 ≤ d)
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
    {S : State d}
    (hexact : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar S) (hsearch : SearchInvariant c.h S)
    (hguard : ruleGuard P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) (initExpRhoDr g) jStar c.etaReady c.etaPre
      c.deltaShort c.deltaTerm c.l0 H .t5 S)
    (hread : FixedGridReadData (g := g) P jStar S (S.cursor + 2 * (c.l0 : ℤ)))
    {r0 : ℤ} {k : ℕ} (cert : HopPrefixCertificate P jStar c.chop Khop c.l0 r0 k)
    (hmu : cert.mus k = S.mu) (hstage : cert.starts k ≤ S.cursor)
    (hentry : z.B * Real.logb 3 (2 + aspectRatio E) ≤ (r0 : ℝ) - (jStar : ℝ))
    (hcont : ∀ r : Mat d, r = S.q ∨
        r = (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
          jStar c.chop c.l0 S).q → ∀ j : ℤ,
      jStar ≤ j → j ≤ S.cursor + 2 * (c.l0 : ℤ) →
        adaptedCell r j ⊆ centeredCube d M) :
    let S' := hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
      jStar c.chop c.l0 S
    S'.mu.PosDef ∧ Matrix.PosDef (toFullBlockMat (adaptedMean P S'.q S'.cursor)) ∧
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
  let : NeZero d := ⟨by omega⟩
  let t0 : ℤ := S.cursor + 2 * (c.l0 : ℤ)
  let n : ℤ := S.cursor + (c.l0 : ℤ)
  let F : BlockMat d := adaptedMean P S.q t0
  let mu' : Mat d := projPathStep c.chop S.mu (canonicalMetric F)
  let q' : Mat d := roundedGrid jStar mu'
  obtain ⟨hpre, hmuState, hjumpState, hratioState, hloState, hhiState,
      hdriftState⟩ := branchT5Short_of_providerData hd hstat hunit hdag hwin hY
        hbridge (z.shortHopProvider hd) hexact hsearch hguard hread cert hmu hstage
        hentry hcont
  have hmus : S.mu.PosDef := by rw [← hmu]; exact cert.mus_pos k le_rfl
  have hmu'pos : mu'.PosDef := by
    simpa [hopState, t0, n, F, mu', q'] using hmuState
  have hjump : projDist S.mu mu' ≤ c.chop := by
    simpa [hopState, t0, n, F, mu', q'] using hjumpState
  have hratio : gridRatio S.q q' ≤ Khop := by
    simpa [hopState, t0, n, F, mu', q'] using hratioState
  have hlo : BlockMatLoewnerLE (blockScale (1 - c.etaX) F)
      (adaptedMean P q' n) := by
    simpa [hopState, t0, n, F, mu', q'] using hloState
  have hhi : BlockMatLoewnerLE (adaptedMean P q' n)
      (blockScale (1 + c.etaX) F) := by
    simpa [hopState, t0, n, F, mu', q'] using hhiState
  have hcont' : ∀ r : Mat d, r = roundedGrid jStar S.mu ∨ r = q' →
      ∀ j : ℤ, jStar ≤ j → j ≤ S.cursor + 2 * (c.l0 : ℤ) →
        adaptedCell r j ⊆ centeredCube d M := by
    intro r hr j hj hjt
    apply hcont r _ j hj hjt
    rcases hr with hr | hr
    · exact Or.inl (hr.trans hexact.1.symm)
    · exact Or.inr (hr.trans (by simp [hopState, q', mu', F, t0]))
  obtain ⟨hdefined, -, htransport⟩ := c.transportData.law c.l0
    ((le_max_right c.Lcommon Ltr).trans c.l0_lower) Cd hCd P E Psi K source
    inferInstance hstat hunit hdag jStar M hwin Y hY S.mu mu' hmus hmu'pos
    (by simpa [hexact.1, q'] using hratio) S.checkpoint S.cursor
    hexact.2.2.2.2.1 hexact.2.2.2.2.2 (by simpa [q'] using hcont')
  obtain ⟨hhistoryRaw, -, -, -, -, -, -⟩ :=
    htransport c.etaX c.etaX_pos.le c.etaX_le_quarter
      (by simpa [hexact.1, F, t0, n, q'] using hlo)
      (by simpa [hexact.1, F, t0, n, q'] using hhi)
  have hPi : 1 ≤ aspectRatio E := one_le_aspectRatio_of_coarseEllipticityDagger hdag
  have hKhop : 1 ≤ Khop := (Transport.one_le_gridRatio S.q q').trans hratio
  have hpref := ShortHop.projDist_prefix cert.mus_pos cert.hop_step k le_rfl
  have hprefBase : projDist 1 S.mu ≤ (k : ℝ) * c.chop := by
    simpa only [cert.mus_zero, hmu] using hpref
  have hprefOld : projDist 1 S.mu ≤ ((k : ℝ) + 1) * c.chop := by
    nlinarith only [hprefBase, c.chop_pos]
  have hprefNew : projDist 1 mu' ≤ ((k : ℝ) + 1) * c.chop := by
    have htri := projDist_triangle Matrix.PosDef.one hmus hmu'pos
    calc
      _ ≤ projDist 1 S.mu + projDist S.mu mu' := htri
      _ ≤ (k : ℝ) * c.chop + c.chop := add_le_add hprefBase hjump
      _ = ((k : ℝ) + 1) * c.chop := by ring
  have hscale : (r0 : ℝ) - (jStar : ℝ) + ((k : ℝ) + 1) * (c.l0 : ℝ) ≤
      (n : ℝ) - (jStar : ℝ) := by
    have hz : r0 + ((k : ℤ) + 1) * (c.l0 : ℤ) ≤ n := by
      calc
        _ = (r0 + (k : ℤ) * (c.l0 : ℤ)) + (c.l0 : ℤ) := by ring
        _ ≤ cert.starts k + (c.l0 : ℤ) := by
          have hk := cert.scale_lower
          omega
        _ ≤ S.cursor + (c.l0 : ℤ) := by omega
        _ = n := by rfl
    have hzR : (r0 : ℝ) + ((k : ℝ) + 1) * (c.l0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hz
    linarith only [hzR]
  have hQ : 1 ≤ initExpQ d g := (by omega : 1 ≤ 2).trans (two_le_initExpQ hg)
  have hrem := transportSrcRemainder_amortized (Ctr := Ctr) (Cd := Cd)
    (g := g) (Khop := Khop) (Pi := aspectRatio E)
    (Q := (initExpQ d g : ℝ)) (a := initExpA g) (chop := c.chop)
    (E := E) (jStar := jStar) (r0 := r0) (n := n) (l0 := (c.l0 : ℤ))
    (k := k) (mu := S.mu) (mu' := mu') c.transportData.Ctr_pos.le
    (zero_le_one.trans hCd) hg.2 (by exact_mod_cast hQ)
    (initExpA_pos hg) c.chop_pos.le hmus hmu'pos hPi
    (Initialization.kappaRef_le_six_mul_aspectRatio_of_coarseEllipticityDagger hdag)
    (by simpa [hexact.1, q'] using hratio) hprefOld hprefNew hscale
  simp only [Int.cast_natCast] at hrem
  have hboot : Ctr * (3 : ℝ) ^ (initExpA g * (c.l0 : ℝ)) *
      transportSrcRemainder Cd g (initExpQ d g : ℝ) (initExpA g) E
        jStar S.mu mu' n ≤
      transportCutoffAmplitude Ctr Cd g (initExpQ d g : ℝ) Khop c.chop *
        (2 + aspectRatio E) ^ (initExpQ d g : ℝ) *
        (3 : ℝ) ^ (-initExpA g * ((r0 : ℝ) - (jStar : ℝ))) *
        Real.exp (-(k : ℝ) * (initExpA g * (c.l0 : ℝ) * Real.log 3 -
          2 * (initExpQ d g : ℝ) * c.chop)) := by
    calc
      _ ≤ _ := hrem
      _ = _ := by rw [transportCutoffAmplitude_eq]; ring
  have hallow := z.transportAllowance hg hCd hKhop hPi hentry hboot
  have hhistory : centeredHistory P (initExpQ d g : ℝ) (initExpRhoMax d g)
        (roundedGrid jStar mu') jStar (S.cursor + (c.l0 : ℤ)) +
      nonlinearHistory P (initExpQ d g : ℝ) (initExpA g)
        (roundedGrid jStar mu') jStar (S.cursor + (c.l0 : ℤ)) ≤
        ENNReal.ofReal c.etaIn := by
    refine hhistoryRaw.trans ?_
    have hcoef : 0 ≤ Ctr * (3 : ℝ) ^ (2 * initExpA g * (c.l0 : ℝ)) :=
      mul_nonneg c.transportData.Ctr_pos.le (Real.rpow_nonneg (by norm_num) _)
    have hfirst : ENNReal.ofReal (Ctr * (3 : ℝ) ^
        (2 * initExpA g * (c.l0 : ℝ))) *
        portableProfile P (initExpQ d g : ℝ) (initExpA g)
          (initExpRhoMax d g) (roundedGrid jStar S.mu) jStar S.checkpoint
            (S.cursor + 2 * (c.l0 : ℤ)) ≤
        ENNReal.ofReal (c.etaIn / 3) := by
      calc
        _ ≤ ENNReal.ofReal _ * ENNReal.ofReal c.etaHop :=
          mul_le_mul_right (by simpa [hexact.1] using hpre) _
        _ = ENNReal.ofReal (_ * c.etaHop) := by rw [ENNReal.ofReal_mul hcoef]
        _ ≤ ENNReal.ofReal (c.etaIn / 3) :=
          ENNReal.ofReal_le_ofReal c.hop_transport_share
    calc
      _ ≤ ENNReal.ofReal (c.etaIn / 3) + ENNReal.ofReal (c.etaIn / 3) +
          ENNReal.ofReal (c.etaIn / 3) := add_le_add (add_le_add hfirst
        (ENNReal.ofReal_le_ofReal c.transport_tolerance))
        (ENNReal.ofReal_le_ofReal (hallow.trans c.tauTr_le))
      _ = ENNReal.ofReal c.etaIn := by
        have hthird : 0 ≤ c.etaIn / 3 := div_nonneg c.etaIn_pos.le (by norm_num)
        rw [← ENNReal.ofReal_add hthird hthird, ← ENNReal.ofReal_add
          (add_nonneg hthird hthird) hthird]
        congr 1
        ring
  have hq' : IsRoundedGrid jStar q' :=
    ⟨ShortHop.kZero_le_of_isCoupledWindow hwin, mu', hmu'pos, rfl⟩
  have hjcursor : jStar ≤ S.cursor :=
    hexact.2.2.2.2.1.trans hexact.2.2.2.2.2
  obtain ⟨-, -, -, hprofileEq, -, -, -, -, -⟩ :=
    c.portableData.law P inferInstance hstat hunit jStar q' hq' jStar n t0
      le_rfl (hjcursor.trans (by dsimp [n]; omega)) (by dsimp [n, t0]; omega)
      (fun j hj hjt => (hdefined q' (Or.inr rfl) j hj hjt).1)
      (fun j hj hjt => (hdefined q' (Or.inr rfl) j hj hjt).2.1)
      (fun j hj hjt => (hdefined q' (Or.inr rfl) j hj hjt).2.2)
  have hprofileState : stateProfile P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar
      (hopState P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
        jStar c.chop c.l0 S) =
      stateHistory (hopState P (initExpQ d g : ℝ) (initExpA g)
        (initExpRhoMax d g) jStar c.chop c.l0 S) := by
    simpa [hopState, stateProfile, stateHistory, portableHistory, t0, n, F, mu', q']
      using hprofileEq
  have hhistoryState : stateHistory (hopState P (initExpQ d g : ℝ)
      (initExpA g) (initExpRhoMax d g) jStar c.chop c.l0 S) ≤
      ENNReal.ofReal c.etaIn := by
    simpa [hopState, stateHistory, t0, n, F, mu', q'] using hhistory
  have hnewPos := (hdefined q' (Or.inr rfl) n
    (hjcursor.trans (by dsimp [n]; omega))
    (by dsimp [n, t0]; omega)).2.1
  have hnewFull := posDef_toFullBlockMat
    (Recurrence.isSymmetricBlockMat_adaptedMean P q' n) hnewPos
  exact ⟨hmuState, by simpa [hopState, t0, n, F, mu', q'] using hnewFull,
    hhistoryState, hdriftState, hjumpState, hratioState, hloState, hhiState,
    hprofileState⟩

end

end Homogenization.HighContrast.Selection
