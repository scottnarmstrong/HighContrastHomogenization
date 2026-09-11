/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.RunInvariants

/-!
# Determinant prefix along the actual selector run

The proof-only hop certificate extracted from the trace supplies the rounded
grids, finite means, bridge comparisons, actual tolerances, and the exact
identity-grid entry needed by the determinant telescope.
-/

namespace Homogenization.HighContrast.Selection

open MeasureTheory
open scoped ENNReal MatrixOrder Matrix

noncomputable section

variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
variable {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}

/-- Every state retained by the actual run satisfies the printed determinant
prefix bound from the identity-grid entry and its completed hop stages. -/
theorem selectionRun_state_prefixLoss_le (hd : 2 ≤ d)
    (hg : g ∈ Set.Ico (0 : ℝ) 1) (hCd : 1 ≤ Cd)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hunit : HCPoly.Frozen.IsUnitRangeLaw P)
    {E : BlockMat d} {Psi : ℝ → ℝ} {K : ℝ} {source : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Psi K source)
    {jStar Mexec : ℤ}
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar Mexec)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Psi K Cd jStar Mexec Y)
    (hbridge : ∀ mp mv : Mat d, mp.PosDef → mv.PosDef → ∀ nn l : ℤ,
      jStar ≤ nn - l →
      Ctr * (1 + Real.log (gridRatio (roundedGrid jStar mp)
        (roundedGrid jStar mv))) ≤ (l : ℝ) →
      Ctr * gridRatio (roundedGrid jStar mp) (roundedGrid jStar mv) *
        (3 : ℝ) ^ (-(l : ℝ)) ≤ 1 / 2 →
      (∀ r : Mat d, r = roundedGrid jStar mp ∨ r = roundedGrid jStar mv →
        ∀ j : ℤ, jStar ≤ j → j ≤ nn + l →
          adaptedCell r j ⊆ centeredCube d Mexec) →
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
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {Lam : ℝ} (hLam : 1 ≤ Lam) {r0 : ℤ} (hj0 : jStar ≤ r0)
    (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    {A0 : BlockMat d} {hcen hnl : ℝ≥0∞}
    (hexact0 : ExactStateData P (initExpQ d g : ℝ) (initExpA g)
      (initExpRhoMax d g) jStar (initialState r0 A0 hcen hnl))
    (hfresh0 : FreshInvariant P (initExpRhoDr g) c.etaIn c.etaNew jStar
      (initialState r0 A0 hcen hnl))
    (hentry : cc.B * Real.logb 3 (2 + aspectRatio E) ≤
      (r0 : ℝ) - (jStar : ℝ))
    (hroot0 : adaptedDetRoot P (1 : Mat d) r0 ≤ 24 * aspectRatio E)
    {T : State d}
    (hT : T ∈ (selectionRun cc P jStar Lam r0 A0 hcen hnl).states) :
    T.prefixLoss ≤ Real.log (24 * aspectRatio E) +
      2 * (T.stage : ℝ) * Real.log (1 + c.etaX) := by
  letI : NeZero d := ⟨by omega⟩
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨hexact, -, hcursor, -, -, cert, -, hq, hs, hloss, hcertBridge,
      -, -, hfinStarts, hfinTerminals, hcertEta, hstartsZero⟩ :=
    selectionRun_state_invariants hd hg hCd hstat hunit hdag hwin hY hbridge
      cc hLam hj0 hr0 hMexec hexact0 hfresh0 hentry T hT
  have hdefined := selectionRun_states_definedness_and_mean_order hd hg cc hstat
    hdag.refBlock_isSymm hLam hwin hj0 hr0 hMexec A0 hcen hnl hY
  have hjcursor : jStar ≤ T.cursor :=
    hexact.2.2.2.2.1.trans hexact.2.2.2.2.2
  have hfinCursor : HasFiniteAdaptedMean P T.q T.cursor :=
    (hdefined.1 T hT T.cursor hjcursor hcursor).1
  have hrounded : ∀ i : ℕ, i ≤ T.stage →
      IsRoundedGrid jStar (cert.grids i) := by
    intro i hi
    rw [cert.grids_eq i hi]
    exact Transport.isRoundedGrid_roundedGrid_of_isCoupledWindow hwin
      (cert.mus_pos i hi)
  have hbridgeFull : ∀ i : ℕ, i < T.stage →
      toFullBlockMat (adaptedMean P (cert.grids (i + 1))
          (cert.starts (i + 1))) ≤
        (1 + cert.eta i) •
          toFullBlockMat (adaptedMean P (cert.grids i) (cert.terminals i)) := by
    intro i hi
    have hle := le_of_blockMatLoewnerLE
      (Recurrence.isSymmetricBlockMat_adaptedMean P (cert.grids (i + 1))
        (cert.starts (i + 1)))
      (isSymmetricBlockMat_blockScale (1 + cert.eta i)
        (Recurrence.isSymmetricBlockMat_adaptedMean P (cert.grids i)
          (cert.terminals i))) (hcertBridge i hi).2
    simpa only [toFullBlockMat_blockScale] using hle
  have hpref := determinantPrefix_le hrounded hfinStarts hfinTerminals
    (by simpa only [hq] using hfinCursor) cert.eta_nonneg hbridgeFull
  have hprefixEq := cert.completedLoss_add_current T.cursor
  rw [hq, hs] at hprefixEq
  have hTPrefix : T.prefixLoss =
      determinantPrefix P cert.grids cert.starts cert.terminals T.stage T.cursor :=
    hloss.trans hprefixEq
  have hgridZero : cert.grids 0 = 1 := by
    calc
      cert.grids 0 = roundedGrid jStar (cert.mus 0) :=
        cert.grids_eq 0 (Nat.zero_le T.stage)
      _ = roundedGrid jStar 1 := by rw [cert.mus_zero]
      _ = 1 := Initialization.roundedGrid_one hwin
  have hrootEntry : adaptedDetRoot P (cert.grids 0) (cert.starts 0) ≤
      6 * (2 : ℝ) ^ 2 * aspectRatio E := by
    rw [hgridZero, hstartsZero]
    norm_num
    exact hroot0
  have hrootPos : 0 < adaptedDetRoot P (cert.grids 0) (cert.starts 0) := by
    apply ShortHop.detRoot_pos
    exact posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P (cert.grids 0) (cert.starts 0))
      (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid
        (hrounded 0 (Nat.zero_le T.stage)) _
        (hfinStarts 0 (Nat.zero_le T.stage)))
  have hbound := determinantPrefix_bound (c := (2 : ℝ))
    (Pi := aspectRatio E) hpref hrootPos hrootEntry
    (fun i hi ↦ ⟨cert.eta_nonneg i hi, hcertEta i hi⟩) c.etaX_pos.le
  calc
    T.prefixLoss =
        determinantPrefix P cert.grids cert.starts cert.terminals T.stage T.cursor :=
      hTPrefix
    _ ≤ Real.log (6 * (2 : ℝ) ^ 2 * aspectRatio E) +
        2 * (T.stage : ℝ) * Real.log (1 + c.etaX) := hbound.1
    _ = Real.log (24 * aspectRatio E) +
        2 * (T.stage : ℝ) * Real.log (1 + c.etaX) := by norm_num

end

end Homogenization.HighContrast.Selection
