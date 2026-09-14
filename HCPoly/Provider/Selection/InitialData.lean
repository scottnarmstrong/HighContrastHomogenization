/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.ChoiceData
import HCPoly.Provider.Initialization.IdentityClause
import HCPoly.Provider.Initialization.ReferenceComparison
import HCPoly.Provider.PortableHistory.Startup
import HCPoly.Provider.ShortHop.DeterminantDrift

/-!
# Identity-grid data for the initial checkpoint

The initial workload joins the portable profile to the weighted determinant
drift.  This file supplies its checkpoint seed and its one-service-step
recurrence.  Both are consequences of the portable-history estimates and the
raw identity-grid bounds.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory
open scoped ENNReal MatrixOrder

noncomputable section

variable {d : ℕ}
/-! ## The combined workload -/

/-- The workload used to select the initial identity-grid checkpoint. -/
def initialWork (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ) (q : Mat d)
    (jStar b T : ℤ) : ℝ≥0∞ :=
  portableProfile P Q a rhoMax q jStar b T +
    ENNReal.ofReal (linearDrift P rhoDr q jStar T)

/-- Defining equation for `initialWork`. -/
theorem initialWork_eq (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (q : Mat d) (jStar b T : ℤ) :
    initialWork P Q a rhoMax rhoDr q jStar b T =
      portableProfile P Q a rhoMax q jStar b T +
        ENNReal.ofReal (linearDrift P rhoDr q jStar T) := rfl
/-! ## The history at the lower endpoint -/

/-- At the lower endpoint the centered maximum has one scale and one cell, so
the complete history is bounded by the corresponding centered moment. -/
theorem portableHistory_lowerEndpoint_le_centeredMoment_rpow [NeZero d]
    {P : Measure (CoeffSpace d)} {Q a rhoMax : ℝ} (hQ : 0 < Q)
    {q : Mat d} (hq : q.PosDef) {b : ℤ}
    (hpos : Book.Ch02.BlockPosDef (adaptedMean P q b)) :
    portableHistory P Q a rhoMax q b b ≤ centeredMoment P Q q b ^ Q := by
  have hcenter : centeredHistory P Q rhoMax q b b ≤ centeredMoment P Q q b ^ Q := by
    have hpt : ∀ x : CoeffSpace d,
        (⨆ (j : ℤ) (_ : b ≤ j) (_ : j ≤ b) (w : Fin d → ℤ)
            (_ : adaptedCellCenter q j w ∈ adaptedCell q b),
          ENNReal.ofReal
            ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (j : ℝ))) *
              blockSize (blockSub (adaptedResponse q j w x) (adaptedMean P q j))
                (adaptedMean P q b))) ^ Q ≤
          ‖schattenSize Q
            (blockSub (coarseBlock (adaptedCell q b) x) (adaptedMean P q b))
              (adaptedMean P q b)‖ₑ ^ Q := by
      intro x
      refine ENNReal.rpow_le_rpow ?_ hQ.le
      refine iSup_le fun j => iSup_le fun hbj => iSup_le fun hjb => ?_
      have hj : j = b := by omega
      subst j
      refine iSup_le fun w => iSup_le fun hw => ?_
      have hw' := (Recurrence.adaptedCellCenter_mem_adaptedCell_iff hq (le_refl b) w).mp hw
      have hw0 : w = 0 := by
        funext i
        have hi := hw' i
        simp only [sub_self, Int.toNat_zero, pow_zero] at hi
        have habs : 0 ≤ |w i| := abs_nonneg _
        have : |w i| = 0 := by omega
        exact abs_eq_zero.mp this
      subst w
      have hweight : (3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (b : ℝ))) = 1 := by
        rw [show -rhoMax * ((b : ℝ) - (b : ℝ)) = 0 by ring, Real.rpow_zero]
      rw [hweight, one_mul, adaptedResponse, PortableHistory.adaptedCellAt_zero]
      have hs0 : 0 ≤ schattenSize Q
          (blockSub (coarseBlock (adaptedCell q b) x) (adaptedMean P q b))
          (adaptedMean P q b) :=
        Recurrence.zero_le_schattenNorm (isSymmetricBlockMat_normalizedBlock
          (isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock _ x)
            (Recurrence.isSymmetricBlockMat_adaptedMean P q b))) Q
      rw [Real.enorm_eq_ofReal hs0]
      apply ENNReal.ofReal_le_ofReal
      exact PortableHistory.blockSize_le_schattenSize
        (isSymmetricBlockMat_blockSub (isSymmetricBlockMat_coarseBlock _ x)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q b))
        (Recurrence.isSymmetricBlockMat_adaptedMean P q b) hpos hQ
    have hp0 : ENNReal.ofReal Q ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hQ
    rw [centeredHistory, centeredMoment, lqSchattenSize,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hQ.le, ← ENNReal.rpow_mul, one_div,
      inv_mul_cancel₀ (ne_of_gt hQ), ENNReal.rpow_one]
    exact lintegral_mono hpt
  rw [portableHistory, nonlinearHistory, Finset.Ico_self, Finset.sum_empty, add_zero]
  exact hcenter

/-! ## Drift over one service step -/

/-- The weighted determinant drift obeys the same charged service estimate as
the portable profile, with its own geometric contraction. -/
theorem linearDrift_service {P : Measure (CoeffSpace d)} [NeZero d]
    [IsProbabilityMeasure P] {Q rhoDr : ℝ} (hQ : 1 ≤ Q) (hrho : 0 ≤ rhoDr)
    {l : ℤ} {q : Mat d} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hq : IsRoundedGrid l q) {jStar TMax h T : ℤ} (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ TMax →
      Book.Ch02.BlockPosDef (adaptedMean P q j))
    (hmono : ∀ s t : ℤ, jStar ≤ s → s ≤ t → t ≤ TMax →
      toFullBlockMat (adaptedMean P q t) ≤ toFullBlockMat (adaptedMean P q s))
    (hh : 1 ≤ h) (hlow : jStar ≤ T + 1 - h) (hhigh : T + h ≤ TMax) :
    linearDrift P rhoDr q jStar (T + h) ≤
      Real.exp (Q * synchCharge P q h T) *
          (3 : ℝ) ^ (-(h : ℝ) * rhoDr) * linearDrift P rhoDr q jStar T +
        2 * (d : ℝ) * (Real.exp (Q * synchCharge P q h T) - 1) := by
  have hT : jStar ≤ T := by omega
  have hTmax : T ≤ TMax := by omega
  have hprop := ShortHop.linearDrift_propagation (P := P) (u := T) (v := T + h)
    hrho hT (by omega)
    (fun j hj _ => posDef_toFullBlockMat
      (Recurrence.isSymmetricBlockMat_adaptedMean P q j) (hpos j hj (by omega)))
    (fun s t hs hst _ => hmono s t hs hst (by omega))
  have hratio :
      (toFullBlockMat (adaptedMean P q T)).det /
          (toFullBlockMat (adaptedMean P q (T + h))).det =
        Real.exp (detIncrement P q T (T + h)) := by
    rw [detIncrement, Real.exp_sub]
    simp only [blockLogDet,
      Real.exp_log (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q T)
        (hpos T hT hTmax)).det_pos,
      Real.exp_log (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q (T + h))
        (hpos (T + h) (by omega) hhigh)).det_pos]
  rw [hratio] at hprop
  have hstep := PortableHistory.detIncrement_le_synchCharge_step hstat hq hlj hfin hh hlow hhigh
  have hdet0 := Recurrence.detIncrement_nonneg (p := T + h) hstat hq (hlj.trans hT) (by omega)
    (hfin T hT hTmax) (hfin (T + h) (by omega) hhigh)
  have hcharge0 : 0 ≤ synchCharge P q h T := hdet0.trans hstep
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hexp : Real.exp (detIncrement P q T (T + h)) ≤
      Real.exp (Q * synchCharge P q h T) := by
    apply Real.exp_le_exp.mpr
    calc
      detIncrement P q T (T + h) ≤ synchCharge P q h T := hstep
      _ ≤ Q * synchCharge P q h T := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ hcharge0
  have hD0 : 0 ≤ linearDrift P rhoDr q jStar T :=
    ShortHop.linearDrift_nonneg
      (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q T) (hpos T hT hTmax))
      (fun r hr1 hr2 => hmono (r - 1) r (by omega) (by omega) (hr2.trans hTmax))
  have hw0 : 0 ≤ (3 : ℝ) ^ (-(h : ℝ) * rhoDr) := by positivity
  have hdim0 : 0 ≤ 2 * (d : ℝ) := by positivity
  calc
    linearDrift P rhoDr q jStar (T + h) ≤
        Real.exp (detIncrement P q T (T + h)) *
            (3 : ℝ) ^ (-rhoDr * (((T + h : ℤ) : ℝ) - (T : ℝ))) *
            linearDrift P rhoDr q jStar T +
          2 * (d : ℝ) * (Real.exp (detIncrement P q T (T + h)) - 1) := hprop
    _ ≤ Real.exp (Q * synchCharge P q h T) *
            (3 : ℝ) ^ (-(h : ℝ) * rhoDr) * linearDrift P rhoDr q jStar T +
          2 * (d : ℝ) * (Real.exp (Q * synchCharge P q h T) - 1) := by
      have hwEq : -rhoDr * (((T + h : ℤ) : ℝ) - (T : ℝ)) = -(h : ℝ) * rhoDr := by
        push_cast; ring
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hexp hw0) hD0
      have hadd := mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1) hdim0
      rw [hwEq]; exact add_le_add hmul hadd

/-! ## Combining the two service estimates -/

/-- Portable-profile service and drift service combine into one recurrence with
contraction one quarter. -/
theorem initialWork_service_of_bounds
    {P : Measure (CoeffSpace d)} {Q a rhoMax rhoDr : ℝ} {q : Mat d}
    {jStar b h T : ℤ} {lambda Csvc : ℝ}
    (hQ : 0 ≤ Q) (hlambda : lambda ≤ 1 / 4)
    (hCsvc : 0 ≤ Csvc) (hdiscount : (3 : ℝ) ^ (-(h : ℝ) * rhoDr) ≤ 1 / 8)
    (hcharge : 0 ≤ synchCharge P q h T)
    (hD : 0 ≤ linearDrift P rhoDr q jStar T)
    (hprofile : portableProfile P Q a rhoMax q jStar b (T + h) ≤
      ENNReal.ofReal (lambda * Real.exp (Q * synchCharge P q h T)) *
          portableProfile P Q a rhoMax q jStar b T +
        ENNReal.ofReal (Csvc * (Real.exp (Q * synchCharge P q h T) - 1)))
    (hdrift : linearDrift P rhoDr q jStar (T + h) ≤
      Real.exp (Q * synchCharge P q h T) *
          (3 : ℝ) ^ (-(h : ℝ) * rhoDr) * linearDrift P rhoDr q jStar T +
        2 * (d : ℝ) * (Real.exp (Q * synchCharge P q h T) - 1)) :
    initialWork P Q a rhoMax rhoDr q jStar b (T + h) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) * Real.exp (Q * synchCharge P q h T)) *
          initialWork P Q a rhoMax rhoDr q jStar b T +
        ENNReal.ofReal ((Csvc + 2 * (d : ℝ)) *
          (Real.exp (Q * synchCharge P q h T) - 1)) := by
  have hE0 : 0 ≤ Real.exp (Q * synchCharge P q h T) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hQ hcharge))
  have hcoef0 : 0 ≤ (1 / 4 : ℝ) * Real.exp (Q * synchCharge P q h T) := by positivity
  have hprofCoef : lambda * Real.exp (Q * synchCharge P q h T) ≤
      (1 / 4 : ℝ) * Real.exp (Q * synchCharge P q h T) := by gcongr
  have hdriftCoef : Real.exp (Q * synchCharge P q h T) *
      (3 : ℝ) ^ (-(h : ℝ) * rhoDr) ≤
        (1 / 4 : ℝ) * Real.exp (Q * synchCharge P q h T) := by
    have : (3 : ℝ) ^ (-(h : ℝ) * rhoDr) ≤ 1 / 4 :=
      hdiscount.trans (by norm_num)
    nlinarith only [this, Real.exp_pos (Q * synchCharge P q h T)]
  have hdrift' : ENNReal.ofReal (linearDrift P rhoDr q jStar (T + h)) ≤
      ENNReal.ofReal ((1 / 4 : ℝ) * Real.exp (Q * synchCharge P q h T)) *
          ENNReal.ofReal (linearDrift P rhoDr q jStar T) +
        ENNReal.ofReal (2 * (d : ℝ) * (Real.exp (Q * synchCharge P q h T) - 1)) := by
    refine (ENNReal.ofReal_le_ofReal hdrift).trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (by norm_num) _)) hD) (mul_nonneg (by positivity) hE0),
      ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg (by norm_num) _))]
    exact add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hdriftCoef) le_rfl) le_rfl
  rw [initialWork_eq, initialWork_eq]
  refine (add_le_add hprofile hdrift').trans ?_
  calc
    _ ≤ (ENNReal.ofReal ((1 / 4 : ℝ) * Real.exp (Q * synchCharge P q h T)) *
          portableProfile P Q a rhoMax q jStar b T +
          ENNReal.ofReal (Csvc * (Real.exp (Q * synchCharge P q h T) - 1))) +
        (ENNReal.ofReal ((1 / 4 : ℝ) * Real.exp (Q * synchCharge P q h T)) *
          ENNReal.ofReal (linearDrift P rhoDr q jStar T) +
          ENNReal.ofReal (2 * (d : ℝ) * (Real.exp (Q * synchCharge P q h T) - 1))) := by
      gcongr
    _ = ENNReal.ofReal ((1 / 4 : ℝ) * Real.exp (Q * synchCharge P q h T)) *
          initialWork P Q a rhoMax rhoDr q jStar b T +
        ENNReal.ofReal ((Csvc + 2 * (d : ℝ)) *
          (Real.exp (Q * synchCharge P q h T) - 1)) := by
      rw [initialWork_eq, mul_add,
        show (Csvc + 2 * (d : ℝ)) * (Real.exp (Q * synchCharge P q h T) - 1) =
          Csvc * (Real.exp (Q * synchCharge P q h T) - 1) +
            2 * (d : ℝ) * (Real.exp (Q * synchCharge P q h T) - 1) by ring,
        ENNReal.ofReal_add (mul_nonneg hCsvc hE0) (mul_nonneg (by positivity) hE0)]
      abel

/-! ## A bounded seed interval -/

/-- On a bounded number of scales, one common bound for the checkpoint history
and the powered centered moments gives an explicit initial workload bound. -/
theorem initialWork_seed_le {P : Measure (CoeffSpace d)} [NeZero d]
    [IsProbabilityMeasure P] {Q a rhoMax rhoDr V D : ℝ}
    (hQ : 1 ≤ Q) (ha : 0 < a) (hrho : 0 ≤ rhoDr) (hV : 0 ≤ V) (hD : 0 ≤ D)
    {l : ℤ} {q : Mat d} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hq : IsRoundedGrid l q) {jStar TMax b L : ℤ} (hlj : l ≤ jStar)
    (hfin : ∀ j : ℤ, jStar ≤ j → j ≤ TMax → HasFiniteAdaptedMean P q j)
    (hpos : ∀ j : ℤ, jStar ≤ j → j ≤ TMax →
      Book.Ch02.BlockPosDef (adaptedMean P q j))
    (hL : 1 ≤ L) (hb : jStar ≤ b) (hbEq : jStar = b) (hbL : b + L ≤ TMax)
    (hhist : portableHistory P Q a rhoMax q jStar b ≤ ENNReal.ofReal V)
    (hmoment : ∀ j : ℤ, b + 1 ≤ j → j ≤ b + L →
      centeredMoment P Q q j ^ Q ≤ ENNReal.ofReal V)
    (hdet : detIncrement P q b (b + L) ≤ D) :
    initialWork P Q a rhoMax rhoDr q jStar b (b + L) ≤
      ENNReal.ofReal (((1 + (L : ℝ)) * (1 + V) * Real.exp (Q * D)) +
        2 * (d : ℝ) * (Real.exp D - 1)) := by
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ
  have hL0 : 0 ≤ (L : ℝ) := by exact_mod_cast le_trans zero_le_one hL
  have hE1 : 1 ≤ Real.exp (Q * D) := Real.one_le_exp (mul_nonneg hQ0 hD)
  have hED1 : 1 ≤ Real.exp D := Real.one_le_exp hD
  have hinherited := PortableHistory.startup_inherited (rhoMax := rhoMax) hQ0 ha hstat hq hlj hfin hL hb hbL
  have hexp : Real.exp (Q * detIncrement P q b (b + L)) ≤ Real.exp (Q * D) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdet hQ0)
  have hI : ENNReal.ofReal ((3 : ℝ) ^
          (-a * (((b + L : ℤ) : ℝ) - (b : ℝ))) *
          (1 + frakH Q (relMean P q b (b + L)))) *
        portableHistory P Q a rhoMax q jStar b ≤
      ENNReal.ofReal (Real.exp (Q * D) * V) := by
    refine hinherited.trans ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) hhist
  have hcenterTerm : ∀ j ∈ Finset.Icc (b + 1) (b + L),
      ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
          Real.exp (Q * detIncrement P q j (b + L))) * centeredMoment P Q q j ^ Q ≤
        ENNReal.ofReal (Real.exp (Q * D) * V) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hbj : b ≤ j := by omega
    have hearly := Recurrence.detIncrement_nonneg (p := j) hstat hq (hlj.trans hb) hbj
      (hfin b hb (by omega)) (hfin j (by omega) (by omega))
    have hsplit := PortableHistory.detIncrement_add P q b j (b + L)
    have hjdet : detIncrement P q j (b + L) ≤ D := by
      linarith only [hsplit, hearly, hdet]
    have hw : (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : (j : ℝ) ≤ ((b + L : ℤ) : ℝ) := by exact_mod_cast hj.2
      nlinarith only [this, ha]
    have hcoef : (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
        Real.exp (Q * detIncrement P q j (b + L)) ≤ Real.exp (Q * D) := by
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hjdet hQ0)
      have hw0 : 0 ≤ (3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) := by positivity
      nlinarith only [hw, hw0, he, Real.exp_pos (Q * detIncrement P q j (b + L))]
    rw [ENNReal.ofReal_mul (Real.exp_pos (Q * D)).le]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) (hmoment j hj.1 hj.2)
  have hcenter : (∑ j ∈ Finset.Icc (b + 1) (b + L),
      ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - (j : ℝ))) *
        Real.exp (Q * detIncrement P q j (b + L))) * centeredMoment P Q q j ^ Q) ≤
      ENNReal.ofReal ((L : ℝ) * Real.exp (Q * D) * V) := by
    calc
      _ ≤ ∑ _j ∈ Finset.Icc (b + 1) (b + L),
          ENNReal.ofReal (Real.exp (Q * D) * V) := Finset.sum_le_sum hcenterTerm
      _ = ENNReal.ofReal ((L : ℝ) * Real.exp (Q * D) * V) := by
        rw [Finset.sum_const, Int.card_Icc, show (b + L + 1 - (b + 1)).toNat = L.toNat by congr 1; ring,
          nsmul_eq_mul, ← ENNReal.ofReal_natCast]
        have hcast : ((L.toNat : ℕ) : ℝ) = (L : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ L)
        rw [hcast, ← ENNReal.ofReal_mul hL0]
        congr 1; ring
  have hnonlinear := PortableHistory.startup_nonlinear hQ0 ha hstat hq hlj hfin hL hb hbL
  have hN : (∑ j ∈ Finset.Ico b (b + L),
      ENNReal.ofReal ((3 : ℝ) ^ (-a * (((b + L : ℤ) : ℝ) - 1 - (j : ℝ))) *
        frakH Q (relMean P q j (b + L)))) ≤ ENNReal.ofReal ((L : ℝ) * Real.exp (Q * D)) := by
    refine hnonlinear.trans (ENNReal.ofReal_le_ofReal ?_)
    have : Real.exp (Q * detIncrement P q b (b + L)) - 1 ≤ Real.exp (Q * D) := by
      linarith only [hexp, Real.exp_pos (Q * detIncrement P q b (b + L))]
    exact mul_le_mul_of_nonneg_left this hL0
  have hdriftProp := ShortHop.linearDrift_propagation (P := P) (u := b) (v := b + L)
    hrho hb (by omega)
    (fun j hj _ => posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q j)
      (hpos j hj (by omega)))
    (fun s t hs hst _ => Recurrence.toFullBlockMat_adaptedMean_le hstat hq (hlj.trans hs) hst
      (hfin s hs (by omega)) (hfin t (hs.trans hst) (by omega)))
  have hdrift : linearDrift P rhoDr q jStar (b + L) ≤ 2 * (d : ℝ) * (Real.exp D - 1) := by
    have hratio : (toFullBlockMat (adaptedMean P q b)).det /
          (toFullBlockMat (adaptedMean P q (b + L))).det =
        Real.exp (detIncrement P q b (b + L)) := by
      rw [detIncrement, Real.exp_sub]
      simp only [blockLogDet,
        Real.exp_log (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q b)
          (hpos b hb (by omega))).det_pos,
        Real.exp_log (posDef_toFullBlockMat (Recurrence.isSymmetricBlockMat_adaptedMean P q (b + L))
          (hpos (b + L) (by omega) hbL)).det_pos]
    have hbase : linearDrift P rhoDr q jStar b = 0 := by subst jStar; simp [linearDrift]
    rw [hratio, hbase] at hdriftProp
    simp only [mul_zero, zero_add] at hdriftProp
    exact hdriftProp.trans (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.exp_le_exp.mpr hdet) 1) (by positivity))
  rw [initialWork_eq, portableProfile]
  refine (add_le_add (add_le_add (add_le_add hI hcenter) hN)
    (ENNReal.ofReal_le_ofReal hdrift)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hED1))]
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [hV, hL0, hE1, hED1]
end
end Selection
end HighContrast
end Homogenization
