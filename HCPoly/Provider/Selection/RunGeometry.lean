/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.State
import HCPoly.Provider.Selection.Transitions
import HCPoly.Provider.Selection.TransitionGuards
import HCPoly.Provider.Selection.CappedRun
import HCPoly.Provider.Selection.RunBounds
import HCPoly.Provider.Selection.EnclosureGeometry
import HCPoly.Provider.Initialization.IdentityGrid
import HCPoly.Provider.ShortHop.PathStep
import HCPoly.Provider.ShortHop.WindowGuard

/-!
# Geometry along the capped selector run

The capped run is fixed from annealed data before a window multiplier is read.
After fixing such a multiplier, one simultaneous induction proves positivity of
every retained witness, its projective prefix bound, and enclosure of every
adapted cell on every grid visited by the run.  At a grid change the old tower
is enclosed first; this makes the terminal old-grid mean positive, which in
turn makes the next projective-path witness positive and licenses its enclosure.
-/

namespace Homogenization.HighContrast.Selection
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {d H Ltr : ℕ}
variable {g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr : ℝ}
variable {c : Constants d H g epsCal etaDr etaProfBar deltaDetBar Cd Khop Ctr Ltr}
variable {alphaFresh alphaX Crad c0 Chit Bmin : ℝ}
/-- The capped execution beginning at the single initialized state. -/
def selectionRun
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    (P : Measure (CoeffSpace d)) (jStar : ℤ) (Lam : ℝ) (r0 : ℤ)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞) : CappedRun d :=
  runCapped P (initExpQ d g : ℝ) (initExpA g) (initExpRhoMax d g)
    (initExpRhoDr g) jStar c.h c.chop c.l0 H c.etaReady c.etaPre
    c.deltaShort c.deltaTerm (transitionCap cc.CN Lam)
    (initialState r0 A0 hcen hnl)
/-! ## Query and window budgets -/
/-- The actual capped run satisfies both inequalities in the query-scale
bound. -/
theorem selectionRun_queryScale_le
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    (P : Measure (CoeffSpace d)) (jStar : ℤ) {Lam : ℝ} (hLam : 1 ≤ Lam)
    (r0 : ℤ) (A0 : BlockMat d) (hcen hnl : ℝ≥0∞)
    (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam) :
    ((selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale : ℝ) ≤
        (r0 : ℝ) + cc.Lexec *
          ((transitionCap cc.CN Lam + 1 : ℕ) : ℝ) ∧
      ((selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale : ℝ) ≤
        (jStar : ℝ) + cc.Csel * Lam := by
  have hraw := runCapped_queryScale_real_le P (initExpQ d g : ℝ)
    (initExpA g) (initExpRhoMax d g) (initExpRhoDr g) jStar c.h r0
    c.chop c.l0 H c.etaReady c.etaPre c.deltaShort c.deltaTerm
    (transitionCap cc.CN Lam) (initialState r0 A0 hcen hnl)
    (le_trans zero_le_one c.one_le_h) (by simp [initialState]) (by simp [initialState])
  have hfirst :
      ((selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale : ℝ) ≤
        (r0 : ℝ) + cc.Lexec *
          ((transitionCap cc.CN Lam + 1 : ℕ) : ℝ) := by
    simpa only [selectionRun, cc.Lexec_eq, Nat.cast_add, Nat.cast_one] using hraw
  have hcap := transitionCap_add_one_le cc.CN_pos.le hLam
  have hspan : cc.Lexec * ((transitionCap cc.CN Lam + 1 : ℕ) : ℝ) ≤
      cc.Lexec * ((cc.CN + 3) * Lam) :=
    mul_le_mul_of_nonneg_left hcap cc.Lexec_pos.le
  refine ⟨hfirst, hfirst.trans ?_⟩
  calc
    (r0 : ℝ) + cc.Lexec * ((transitionCap cc.CN Lam + 1 : ℕ) : ℝ) ≤
        ((jStar : ℝ) + cc.CR * Lam) +
          cc.Lexec * ((cc.CN + 3) * Lam) := add_le_add hr0 hspan
    _ = (jStar : ℝ) + cc.Csel * Lam := by
      rw [cc.Csel_eq, selectionCoefficient_eq]
      ring
/-- The query scale plus the rounded-grid enlargement lies in the preassigned
execution window. -/
theorem selectionRun_queryScale_add_gridEnlargement_le
    (hd : 2 ≤ d)
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    (P : Measure (CoeffSpace d)) (jStar : ℤ) {Lam : ℝ} (hLam : 1 ≤ Lam)
    (r0 : ℤ) (A0 : BlockMat d) (hcen hnl : ℝ≥0∞)
    (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam) {Mexec : ℤ}
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉) :
    (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale +
        (gridEnlargement d c.chop (transitionCap cc.CN Lam) : ℤ) ≤ Mexec := by
  have hquery := (selectionRun_queryScale_le cc P jStar hLam r0 A0 hcen hnl hr0).2
  have hcap := transitionCap_add_one_le cc.CN_pos.le hLam
  have hgrid := gridEnlargement_le hd c.chop_pos.le hLam
    (transitionCap cc.CN Lam) hcap
  let Gcoef : ℝ := 2 + (1 / 2 : ℝ) * Real.logb 3 d +
    c.chop / Real.log 3 * (cc.CN + 3)
  have hcoeff : cc.Csel + Gcoef ≤ cc.CM := by
    have hceilLog : Real.logb 3 d * (1 / 2 : ℝ) ≤ (⌈Real.logb 3 d * (1 / 2 : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    dsimp [Gcoef]
    rw [cc.Csel_eq, selectionCoefficient_eq, cc.CM_eq, executionMinimum_eq]
    ring_nf
    linarith only [hceilLog]
  have hLam0 : 0 ≤ Lam := le_trans zero_le_one hLam
  have hsum :
      ((selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale : ℝ) +
          (gridEnlargement d c.chop (transitionCap cc.CN Lam) : ℝ) ≤
        (jStar : ℝ) + cc.Cexec * Lam := by
    calc
      _ ≤ ((jStar : ℝ) + cc.Csel * Lam) + Gcoef * Lam :=
        add_le_add hquery (by simpa only [Gcoef] using hgrid)
      _ = (jStar : ℝ) + (cc.Csel + Gcoef) * Lam := by ring
      _ ≤ (jStar : ℝ) + cc.CM * Lam :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoeff hLam0)
      _ ≤ (jStar : ℝ) + cc.Cexec * Lam :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right cc.CM_le_Cexec hLam0)
  have hceil : cc.Cexec * Lam ≤ (⌈cc.Cexec * Lam⌉ : ℤ) := Int.le_ceil _
  have hreal :
      ((selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale : ℝ) +
          (gridEnlargement d c.chop (transitionCap cc.CN Lam) : ℝ) ≤
        (Mexec : ℝ) := by
    rw [hMexec]
    push_cast
    exact hsum.trans (add_le_add le_rfl hceil)
  exact_mod_cast hreal
/-! ## Simultaneous geometry induction -/
private theorem eccentricity_and_cells (hd : 2 ≤ d) {jStar M Tquery : ℤ}
    {chop : ℝ} {Ncap : ℕ} {S : State d}
    (hjStar : (kZero d : ℤ) ≤ jStar) (hchop : 0 ≤ chop) (hmu : S.mu.PosDef)
    (hgrid : S.q = roundedGrid jStar S.mu)
    (hproj : projDist 1 S.mu ≤ (S.stage : ℝ) * chop)
    (hstage : S.stage ≤ Ncap + 1)
    (hbudget : Tquery + (gridEnlargement d chop Ncap : ℤ) ≤ M) :
    witnessEccentricity S.mu ≤
        Real.exp (chop * ((Ncap + 1 : ℕ) : ℝ)) ∧
      ∀ T : ℤ, jStar ≤ T → T ≤ Tquery →
        adaptedCell S.q T ⊆ centeredCube d M := by
  let : NeZero d := ⟨by omega⟩
  have hstageReal : (S.stage : ℝ) ≤ ((Ncap + 1 : ℕ) : ℝ) := by exact_mod_cast hstage
  have hprefix : projDist 1 S.mu ≤ chop * ((Ncap + 1 : ℕ) : ℝ) :=
    hproj.trans <| by
      calc
        (S.stage : ℝ) * chop = chop * (S.stage : ℝ) := mul_comm _ _
        _ ≤ chop * ((Ncap + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hstageReal hchop
  have hecc := ShortHop.witnessEccentricity_le_exp hmu hprefix
  refine ⟨hecc, ?_⟩
  intro T hjT hTq
  rw [hgrid]
  exact (roundedGrid_adaptedCell_subset_gridEnlargement hd hjStar hmu hecc).trans
    (Initialization.centeredCube_subset_centeredCube (by omega))
private theorem selectorStep_next_geometry (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q a rhoMax rhoDr g K Cd : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {jStar M Tquery h : ℤ}
    {chop : ℝ} {l0 H fuel Ncap : ℕ} {etaReady etaPre deltaShort deltaTerm : ℝ}
    (hwin : IsCoupledWindow d Q K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hh : 0 ≤ h) (hchop : 0 ≤ chop) {S Sn : State d}
    (hstage : S.stage + (fuel + 1) ≤ Ncap) (hbase : jStar ≤ S.base)
    (hbaseCursor : S.base ≤ S.cursor) (hmu : S.mu.PosDef)
    (hgrid : S.q = roundedGrid jStar S.mu)
    (hproj : projDist 1 S.mu ≤ (S.stage : ℝ) * chop)
    (hcells : ∀ T : ℤ, jStar ≤ T → T ≤ Tquery →
      adaptedCell S.q T ⊆ centeredCube d M)
    (hread : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm S).readScale ≤ Tquery)
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
      etaPre deltaShort deltaTerm S).outcome = StepOutcome.next Sn) :
    Sn.stage + fuel ≤ Ncap ∧ jStar ≤ Sn.base ∧ Sn.base ≤ Sn.cursor ∧
      Sn.mu.PosDef ∧ Sn.q = roundedGrid jStar Sn.mu ∧
      projDist 1 Sn.mu ≤ (Sn.stage : ℝ) * chop := by
  let : NeZero d := ⟨by omega⟩
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hadvance : ∀ (v : ℤ) (phase : Phase) (candidate : Option (BlockMat d)),
      S.base ≤ v →
      let Sn := advanceCursor P S v phase candidate
      Sn.stage + fuel ≤ Ncap ∧ jStar ≤ Sn.base ∧ Sn.base ≤ Sn.cursor ∧
        Sn.mu.PosDef ∧ Sn.q = roundedGrid jStar Sn.mu ∧
        projDist 1 Sn.mu ≤ (Sn.stage : ℝ) * chop := by
    intro v phase candidate hv
    simp only [advanceCursor]
    exact ⟨by omega, hbase, hv, hmu, hgrid, hproj⟩
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S with
  | t1 =>
      simp [selectorStep, hrule] at hout
      subst Sn
      exact hadvance _ _ _ (by omega)
  | t2 =>
      simp [selectorStep, hrule] at hout
      subst Sn
      exact hadvance _ _ _ (by omega)
  | t3 =>
      simp [selectorStep, hrule] at hout
      subst Sn
      exact hadvance _ _ _ (by omega)
  | t4 =>
      simp [selectorStep, hrule] at hout
      subst Sn
      exact hadvance _ _ _ (by omega)
  | t5 =>
      have ht0 : S.cursor + 2 * (l0 : ℤ) ≤ Tquery := by
        simpa only [selectorStep, hrule] using hread
      have hjt0 : jStar ≤ S.cursor + 2 * (l0 : ℤ) := by omega
      have hcontOld : ∀ T : ℤ, jStar ≤ T → T ≤ S.cursor + 2 * (l0 : ℤ) →
          adaptedCell (roundedGrid jStar S.mu) T ⊆ centeredCube d M := by
        intro T hjT hTt0
        rw [← hgrid]
        exact hcells T hjT (hTt0.trans ht0)
      have hF : (toFullBlockMat
          (adaptedMean P S.q (S.cursor + 2 * (l0 : ℤ)))).PosDef := by
        rw [hgrid]
        exact ShortHop.posDef_adaptedMean_of_window hwin hY hmu hjt0 le_rfl hcontOld
      have hmu' : (projPathStep chop S.mu
          (canonicalMetric (adaptedMean P S.q
            (S.cursor + 2 * (l0 : ℤ))))).PosDef :=
        ShortHop.posDef_projPathStep hchop hmu (ShortHop.posDef_canonicalMetric hF)
      have hjump : projDist S.mu (projPathStep chop S.mu
          (canonicalMetric (adaptedMean P S.q
            (S.cursor + 2 * (l0 : ℤ))))) ≤ chop :=
        ShortHop.projDist_projPathStep_le hchop hmu (ShortHop.posDef_canonicalMetric hF)
      have hprefix : projDist 1 (projPathStep chop S.mu
          (canonicalMetric (adaptedMean P S.q
            (S.cursor + 2 * (l0 : ℤ))))) ≤ ((S.stage + 1 : ℕ) : ℝ) * chop := by
        calc
          _ ≤ projDist 1 S.mu + projDist S.mu (projPathStep chop S.mu
              (canonicalMetric (adaptedMean P S.q
                (S.cursor + 2 * (l0 : ℤ))))) :=
            projDist_triangle Matrix.PosDef.one hmu hmu'
          _ ≤ (S.stage : ℝ) * chop + chop := add_le_add hproj hjump
          _ = ((S.stage + 1 : ℕ) : ℝ) * chop := by push_cast; ring
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [hopState]
      exact ⟨by omega, by omega, by simp, hmu', by simp, hprefix⟩
  | t6 =>
      simp [selectorStep, hrule] at hout
      subst Sn
      exact hadvance _ _ _ (by omega)
  | t7 => simp [selectorStep, hrule] at hout
private theorem runCapped_geometry_aux (hd : 2 ≤ d)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q a rhoMax rhoDr g K Cd : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {jStar M Tquery h : ℤ}
    {chop : ℝ} {l0 H fuel Ncap : ℕ} {etaReady etaPre deltaShort deltaTerm : ℝ}
    (hwin : IsCoupledWindow d Q K jStar M)
    {Y : CoeffSpace d → ℝ} (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hh : 0 ≤ h) (hchop : 0 ≤ chop) {S : State d}
    (hstage : S.stage + fuel ≤ Ncap) (hbase : jStar ≤ S.base)
    (hbaseCursor : S.base ≤ S.cursor) (hmu : S.mu.PosDef)
    (hgrid : S.q = roundedGrid jStar S.mu)
    (hproj : projDist 1 S.mu ≤ (S.stage : ℝ) * chop)
    (hquery : (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).queryScale ≤ Tquery)
    (hbudget : Tquery + (gridEnlargement d chop Ncap : ℤ) ≤ M) :
    ∀ S' ∈ (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm fuel S).states,
      S'.stage ≤ Ncap ∧ jStar ≤ S'.base ∧ S'.base ≤ S'.cursor ∧
        S'.mu.PosDef ∧ S'.q = roundedGrid jStar S'.mu ∧
        projDist 1 S'.mu ≤ (S'.stage : ℝ) * chop ∧
        witnessEccentricity S'.mu ≤ Real.exp (chop * ((Ncap + 1 : ℕ) : ℝ)) ∧
        ∀ T : ℤ, jStar ≤ T → T ≤ Tquery →
          adaptedCell S'.q T ⊆ centeredCube d M := by
  let : NeZero d := ⟨by omega⟩
  have hjStar := ShortHop.kZero_le_of_isCoupledWindow hwin
  induction fuel generalizing S with
  | zero =>
      intro S' hmem
      have hgeom := eccentricity_and_cells hd hjStar hchop hmu hgrid hproj
        (by omega) hbudget
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome <;>
        simp [runCapped, hout] at hmem
      all_goals subst S'
      all_goals exact ⟨by omega, hbase, hbaseCursor, hmu, hgrid, hproj,
        hgeom.1, hgeom.2⟩
  | succ fuel ih =>
      intro S' hmem
      have hgeom := eccentricity_and_cells hd hjStar hchop hmu hgrid hproj
        (by omega) hbudget
      cases hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).outcome with
      | terminal state =>
          simp [runCapped, hout] at hmem
          subst S'
          exact ⟨by omega, hbase, hbaseCursor, hmu, hgrid, hproj,
            hgeom.1, hgeom.2⟩
      | next Sn =>
          simp only [runCapped, hout, List.mem_cons] at hmem
          rcases hmem with rfl | htail
          · exact ⟨by omega, hbase, hbaseCursor, hmu, hgrid, hproj,
              hgeom.1, hgeom.2⟩
          · have hwhole : max
                (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                  etaPre deltaShort deltaTerm S).readScale
                (runCapped P Q a rhoMax rhoDr jStar h chop l0 H etaReady
                  etaPre deltaShort deltaTerm fuel Sn).queryScale ≤ Tquery := by
                simpa only [runCapped, hout] using hquery
            have hnext := selectorStep_next_geometry hd hwin hY hh hchop hstage
              hbase hbaseCursor hmu hgrid hproj hgeom.2
              ((le_max_left _ _).trans hwhole) hout
            rcases hnext with ⟨hstage', hbase', hcursor', hmu', hgrid', hproj'⟩
            exact ih hstage' hbase' hcursor' hmu' hgrid' hproj'
              ((le_max_right _ _).trans hwhole) S' htail
/-- Every state visited by the actual capped selection run has the rounded-grid
relation, a positive witness with its projective and eccentricity prefix
bounds, and a complete adapted-cell enclosure through the run's query scale. -/
theorem selectionRun_state_geometry (hd : 2 ≤ d)
    (cc : CutoffConstants c alphaFresh alphaX Crad c0 Chit Bmin)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K Lam : ℝ} {jStar Mexec r0 : ℤ}
    (hLam : 1 ≤ Lam)
    (hwin : IsCoupledWindow d (initExpQ d g : ℝ) K jStar Mexec)
    (hj0 : jStar ≤ r0) (hr0 : (r0 : ℝ) ≤ (jStar : ℝ) + cc.CR * Lam)
    (hMexec : Mexec = jStar + ⌈cc.Cexec * Lam⌉)
    (A0 : BlockMat d) (hcen hnl : ℝ≥0∞)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar Mexec Y) :
    ∀ S' ∈ (selectionRun cc P jStar Lam r0 A0 hcen hnl).states,
      S'.stage ≤ transitionCap cc.CN Lam ∧ jStar ≤ S'.base ∧
        S'.base ≤ S'.cursor ∧ S'.mu.PosDef ∧
        S'.q = roundedGrid jStar S'.mu ∧
        projDist 1 S'.mu ≤ (S'.stage : ℝ) * c.chop ∧
        witnessEccentricity S'.mu ≤
          Real.exp (c.chop * ((transitionCap cc.CN Lam + 1 : ℕ) : ℝ)) ∧
        ∀ T : ℤ, jStar ≤ T →
          T ≤ (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale →
          adaptedCell S'.q T ⊆ centeredCube d Mexec := by
  let : NeZero d := ⟨by omega⟩
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have hbudget := selectionRun_queryScale_add_gridEnlargement_le hd cc P jStar
    hLam r0 A0 hcen hnl hr0 hMexec
  have hgrid0 : (initialState r0 A0 hcen hnl).q =
      roundedGrid jStar (initialState r0 A0 hcen hnl).mu := by
    simp only [initialState]
    exact (Initialization.roundedGrid_one hwin).symm
  have hproj0 : projDist 1 (initialState r0 A0 hcen hnl).mu ≤
      ((initialState r0 A0 hcen hnl).stage : ℝ) * c.chop := by
    simp only [initialState, Nat.cast_zero, zero_mul]
    rw [projDist_self Matrix.PosDef.one]
  simpa only [selectionRun] using
    (runCapped_geometry_aux hd hwin hY (le_trans zero_le_one c.one_le_h) c.chop_pos.le
      (S := initialState r0 A0 hcen hnl) (Ncap := transitionCap cc.CN Lam)
      (Tquery := (selectionRun cc P jStar Lam r0 A0 hcen hnl).queryScale)
      (by simp [initialState]) hj0 (by simp [initialState])
      Matrix.PosDef.one hgrid0 hproj0 le_rfl hbudget)
end
end Homogenization.HighContrast.Selection
