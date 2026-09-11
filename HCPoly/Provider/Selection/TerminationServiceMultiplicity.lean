/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Selection.TerminationChargeBounds

/-!
# Synchronized-service multiplicity on selector traces

The synchronized charge is the drop of a moving window of determinant-root
logs.  Service cursors are separated by the service length, while every other
same-grid move only shifts this window forward.  This gives the factor `h`
against the exact determinant prefix without any cross-grid comparison.
-/

namespace Homogenization
namespace HighContrast
namespace Selection

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The length-`h` window of determinant-root logarithms ending at `u`. -/
def detRootWindow (P : Measure (CoeffSpace d)) (q : Mat d) (h u : ℤ) : ℝ :=
  ∑ j ∈ Finset.Icc (u + 1 - h) u, Real.log (adaptedDetRoot P q j)

/-- Defining equation for the determinant-root window. -/
theorem detRootWindow_eq (P : Measure (CoeffSpace d)) (q : Mat d) (h u : ℤ) :
    detRootWindow P q h u =
      ∑ j ∈ Finset.Icc (u + 1 - h) u,
        Real.log (adaptedDetRoot P q j) := rfl

/-- A service charge is exactly the drop of its moving determinant-root
window. -/
theorem serviceWindowCharge_eq_detRootWindow_sub
    (P : Measure (CoeffSpace d)) (q : Mat d) (h u : ℤ) :
    serviceWindowCharge P q h u =
      detRootWindow P q h u - detRootWindow P q h (u + h) := by
  have hshift : ∑ j ∈ Finset.Icc (u + 1) (u + h),
      Real.log (adaptedDetRoot P q (j - h)) =
      ∑ j ∈ Finset.Icc (u + 1 - h) u,
        Real.log (adaptedDetRoot P q j) := by
    have hmap : (Finset.Icc (u + 1 - h) u).map (addRightEmbedding h) =
        Finset.Icc (u + 1) (u + h) := by
      rw [Finset.map_add_right_Icc]
      congr 1
      ring
    rw [← hmap, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    simp [addRightEmbedding]
  have hidx : u + h + 1 - h = u + 1 := by ring
  rw [serviceWindowCharge_eq, detRootWindow_eq, detRootWindow_eq, hidx]
  simp only [detLoss, Finset.sum_sub_distrib, hshift]

private theorem detRootWindow_le_base {P : Measure (CoeffSpace d)}
    {q : Mat d} {h base u : ℤ} (hh : 1 ≤ h) (hbase : base + h ≤ u)
    (hmono : ∀ j : ℤ, base ≤ j → j ≤ u →
      Real.log (adaptedDetRoot P q j) ≤
        Real.log (adaptedDetRoot P q base)) :
    detRootWindow P q h u ≤
      (h : ℝ) * Real.log (adaptedDetRoot P q base) := by
  have hcard : (Finset.Icc (u + 1 - h) u).card = h.toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have hbound : ∀ j ∈ Finset.Icc (u + 1 - h) u,
      Real.log (adaptedDetRoot P q j) ≤
        Real.log (adaptedDetRoot P q base) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact hmono j (by omega) hj'.2
  have hsum := Finset.sum_le_card_nsmul _ _ _ hbound
  have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ h)
  rw [hcard, nsmul_eq_mul, hcast] at hsum
  rw [detRootWindow_eq]
  exact hsum

/-- A decreasing determinant-root profile bounds the moving window below by
`h` copies of its right endpoint. -/
theorem mul_log_le_detRootWindow {P : Measure (CoeffSpace d)}
    {q : Mat d} {h base u : ℤ} (hh : 1 ≤ h) (hbase : base + h ≤ u)
    (hmono : ∀ j : ℤ, base ≤ j → j ≤ u →
      Real.log (adaptedDetRoot P q u) ≤
        Real.log (adaptedDetRoot P q j)) :
    (h : ℝ) * Real.log (adaptedDetRoot P q u) ≤
      detRootWindow P q h u := by
  have hcard : (Finset.Icc (u + 1 - h) u).card = h.toNat := by
    rw [Int.card_Icc]
    congr 1
    ring
  have hbound : ∀ j ∈ Finset.Icc (u + 1 - h) u,
      Real.log (adaptedDetRoot P q u) ≤
        Real.log (adaptedDetRoot P q j) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact hmono j (by omega) hj'.2
  have hsum := Finset.card_nsmul_le_sum _ _ _ hbound
  have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ h)
  rw [hcard, nsmul_eq_mul, hcast] at hsum
  rw [detRootWindow_eq]
  exact hsum

private theorem detRootWindow_antitone {P : Measure (CoeffSpace d)}
    {q : Mat d} {h base u v : ℤ} (hbase : base + h ≤ u)
    (huv : u ≤ v)
    (hmono : ∀ x y : ℤ, base ≤ x → x ≤ y → y ≤ v →
      Real.log (adaptedDetRoot P q y) ≤
        Real.log (adaptedDetRoot P q x)) :
    detRootWindow P q h v ≤ detRootWindow P q h u := by
  have hmap : (Finset.Icc (u + 1 - h) u).map (addRightEmbedding (v - u)) =
      Finset.Icc (v + 1 - h) v := by
    rw [Finset.map_add_right_Icc]
    congr 1 <;> ring
  rw [detRootWindow_eq, detRootWindow_eq, ← hmap, Finset.sum_map]
  apply Finset.sum_le_sum
  intro x hx
  have hxu := (Finset.mem_Icc.mp hx).2
  simp only [addRightEmbedding_apply]
  apply hmono
  · rw [Finset.mem_Icc] at hx
    omega
  · omega
  · omega

/-- The service account at a reached state: during search it retains one
moving window, while fresh and terminal states have no outstanding window. -/
def ServiceAccount (P : Measure (CoeffSpace d)) (h : ℤ)
    (completed service : ℝ) (S : State d) : Prop :=
  match S.phase with
  | .search =>
      service + detRootWindow P S.q h S.cursor ≤
          (h : ℝ) * completed +
            (h : ℝ) * Real.log (adaptedDetRoot P S.q S.base) ∧
        S.base + h ≤ S.cursor
  | _ => service ≤ (h : ℝ) * completed ∧ S.base = S.cursor

/-- Defining equation for the service account. -/
theorem serviceAccount_eq (P : Measure (CoeffSpace d)) (h : ℤ)
    (completed service : ℝ) (S : State d) :
    ServiceAccount P h completed service S =
      match S.phase with
      | .search =>
          service + detRootWindow P S.q h S.cursor ≤
              (h : ℝ) * completed +
                (h : ℝ) * Real.log (adaptedDetRoot P S.q S.base) ∧
            S.base + h ≤ S.cursor
      | _ => service ≤ (h : ℝ) * completed ∧ S.base = S.cursor := rfl

/-- Every nonterminal selector step updates the completed and synchronized
charges while preserving the service account. -/
theorem selectorStep_next_serviceAccount
    (P : Measure (CoeffSpace d)) (Q a rhoMax rhoDr : ℝ)
    (jStar h : ℤ) (chop : ℝ) (l0 H : ℕ)
    (etaReady etaPre deltaShort deltaTerm completed service : ℝ)
    (S Sn : State d) (hh : 1 ≤ h)
    (haccount : ServiceAccount P h completed service S)
    (hmono : ∀ u v : ℤ, S.base ≤ u → u ≤ v →
      v ≤ (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady
        etaPre deltaShort deltaTerm S).readScale →
      Real.log (adaptedDetRoot P S.q v) ≤ Real.log (adaptedDetRoot P S.q u))
    (hout : (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
      deltaShort deltaTerm S).outcome = StepOutcome.next Sn) :
    ServiceAccount P h
      (completed + completedStageCharge P l0 S
        (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
          deltaShort deltaTerm S).rule)
      (service + serviceTransitionCharge P h S
        (selectorStep P Q a rhoMax rhoDr jStar h chop l0 H etaReady etaPre
          deltaShort deltaTerm S).rule) Sn := by
  cases hrule : selectedRule P Q a rhoMax rhoDr jStar etaReady etaPre
      deltaShort deltaTerm l0 H S with
  | t1 =>
      have hguard := selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
        etaPre deltaShort deltaTerm l0 H S
      rw [hrule] at hguard
      simp only [ruleGuard] at hguard
      simp only [selectorStep, hrule] at hmono
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [ServiceAccount, advanceCursor, completedStageCharge,
        serviceTransitionCharge, selectorStep, hrule]
      simp only [ServiceAccount, hguard] at haccount
      have hwindow := detRootWindow_le_base hh (by omega)
        (fun j hj hj' => hmono S.base j le_rfl hj hj')
      exact ⟨by linarith only [haccount.1, hwindow], by omega⟩
  | t2 =>
      have hguard := selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
        etaPre deltaShort deltaTerm l0 H S
      rw [hrule] at hguard
      simp only [ruleGuard] at hguard
      simp only [selectorStep, hrule] at hmono
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [ServiceAccount, advanceCursor, completedStageCharge,
        serviceTransitionCharge, selectorStep, hrule]
      simp only [ServiceAccount, hguard.1] at haccount
      rw [serviceWindowCharge_eq_detRootWindow_sub]
      exact ⟨by linarith only [haccount.1], by omega⟩
  | t3 =>
      have hguard := selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
        etaPre deltaShort deltaTerm l0 H S
      rw [hrule] at hguard
      simp only [ruleGuard] at hguard
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [ServiceAccount, advanceCursor, completedStageCharge,
        serviceTransitionCharge, selectorStep, hrule]
      simp only [ServiceAccount, hguard.1] at haccount
      rw [serviceWindowCharge_eq_detRootWindow_sub]
      exact ⟨by linarith only [haccount.1], by omega⟩
  | t4 =>
      have hguard := selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
        etaPre deltaShort deltaTerm l0 H S
      rw [hrule] at hguard
      simp only [ruleGuard] at hguard
      simp only [selectorStep, hrule] at hmono
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [ServiceAccount, advanceCursor, completedStageCharge,
        serviceTransitionCharge, selectorStep, hrule]
      simp only [ServiceAccount, hguard.1] at haccount
      have hwindow := detRootWindow_antitone haccount.2 (by omega)
        (fun x y hx hxy hyv => hmono x y hx hxy hyv)
      exact ⟨by linarith only [haccount.1, hwindow], by omega⟩
  | t5 =>
      have hguard := selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
        etaPre deltaShort deltaTerm l0 H S
      rw [hrule] at hguard
      simp only [ruleGuard] at hguard
      simp only [selectorStep, hrule] at hmono
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [ServiceAccount, hguard.1] at haccount
      have hwindow := detRootWindow_antitone haccount.2 (by omega)
        (fun x y hx hxy hyv => hmono x y hx hxy hyv)
      have hlower := mul_log_le_detRootWindow hh (by omega)
        (fun j hj hj' => hmono j (S.cursor + 2 * (l0 : ℤ)) hj hj'
          le_rfl)
      by_cases hfinal : projDist S.mu
          (canonicalMetric (adaptedMean P S.q
            (S.cursor + 2 * (l0 : ℤ)))) ≤ chop
      · simp only [ServiceAccount, hopState, hfinal, if_pos,
          completedStageCharge, serviceTransitionCharge, selectorStep, hrule,
          add_zero]
        constructor
        · rw [detLoss]
          linarith only [haccount.1, hwindow, hlower]
        · exact True.intro
      · simp only [ServiceAccount, hopState, hfinal,
          completedStageCharge, serviceTransitionCharge, selectorStep, hrule,
          add_zero]
        constructor
        · rw [detLoss]
          linarith only [haccount.1, hwindow, hlower]
        · exact True.intro
  | t6 =>
      have hguard := selectedRule_guard P Q a rhoMax rhoDr jStar etaReady
        etaPre deltaShort deltaTerm l0 H S
      rw [hrule] at hguard
      simp only [ruleGuard] at hguard
      simp only [selectorStep, hrule] at hmono
      simp [selectorStep, hrule] at hout
      subst Sn
      simp only [ServiceAccount, advanceCursor, completedStageCharge,
        serviceTransitionCharge, selectorStep, hrule]
      simp only [ServiceAccount, hguard.1] at haccount
      have hwindow := detRootWindow_le_base hh (by omega)
        (fun j hj hj' => hmono S.base j le_rfl hj hj')
      exact ⟨by linarith only [haccount.1, hwindow], by omega⟩
  | t7 => simp [selectorStep, hrule] at hout

end

end Selection
end HighContrast
end Homogenization
