/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.ScaleMeasurability

/-!
# The stopped window scale and multiplier

The stopped offset is the least nonnegative generation at which the strict
successor fits inside the enlarged window.  The empty set is assigned offset
zero; the successor tail later shows that this exceptional branch is null.
-/

namespace Homogenization
namespace HighContrast
namespace Window

open MeasureTheory

open scoped ENNReal

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-- The least enlargement `ℓ_P` for which the strict successor fits in the
enlarged window, with value zero when no enlargement exists. -/
def windowScaleOffset (g : ℝ) (E : BlockMat d) (jStar M : ℤ)
    (a : CoeffSpace d) : ℕ :=
  sInf {ℓ : ℕ | successorScale g E (M - jStar) a ≤
    ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ)))}

/-- The stopped multiplier `Y_P = 3^{g ℓ_P}`. -/
def windowMultiplier (g : ℝ) (E : BlockMat d) (jStar M : ℤ)
    (a : CoeffSpace d) : ℝ :=
  (3 : ℝ) ^ (g * (windowScaleOffset g E jStar M a : ℝ))

private theorem offsetPredicate_upwardClosed (g : ℝ) (E : BlockMat d)
    (jStar M : ℤ) (a : CoeffSpace d) :
    ∀ ℓ₁ ℓ₂ : ℕ, ℓ₁ ≤ ℓ₂ →
      ℓ₁ ∈ {ℓ : ℕ | successorScale g E (M - jStar) a ≤
        ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ)))} →
      ℓ₂ ∈ {ℓ : ℕ | successorScale g E (M - jStar) a ≤
        ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ)))} := by
  intro ℓ₁ ℓ₂ hℓ hmem
  have hcast : (ℓ₁ : ℤ) ≤ (ℓ₂ : ℤ) := by exact_mod_cast hℓ
  have hexp : M + (ℓ₁ : ℤ) ≤ M + (ℓ₂ : ℤ) := by omega
  have hpow : (3 : ℝ) ^ (M + (ℓ₁ : ℤ)) ≤ (3 : ℝ) ^ (M + (ℓ₂ : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) hexp
  exact hmem.trans (ENNReal.ofReal_le_ofReal hpow)

/-- The stopped offset realizes its threshold whenever some threshold is
available. -/
theorem successorScale_le_stoppedThreshold {g : ℝ} {E : BlockMat d}
    {jStar M : ℤ} {a : CoeffSpace d}
    (hfinite : ∃ ℓ : ℕ, successorScale g E (M - jStar) a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ)))) :
    successorScale g E (M - jStar) a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (M + (windowScaleOffset g E jStar M a : ℤ))) := by
  exact Nat.sInf_mem hfinite

/-- Every finite strict successor reaches one of the nonnegative enlargement
thresholds. -/
theorem exists_stoppedThreshold_of_ne_top {g : ℝ} {E : BlockMat d}
    {jStar M : ℤ} {a : CoeffSpace d}
    (hfinite : successorScale g E (M - jStar) a ≠ ⊤) :
    ∃ ℓ : ℕ, successorScale g E (M - jStar) a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ))) := by
  let T : ℝ := (successorScale g E (M - jStar) a).toReal
  have hbase : 0 < (3 : ℝ) ^ M := by positivity
  obtain ⟨ℓ, hℓ⟩ := pow_unbounded_of_one_lt (T / (3 : ℝ) ^ M)
    (by norm_num : (1 : ℝ) < 3)
  refine ⟨ℓ, ?_⟩
  rw [← ENNReal.ofReal_toReal hfinite]
  refine ENNReal.ofReal_le_ofReal ?_
  have hscaled : T < (3 : ℝ) ^ ℓ * (3 : ℝ) ^ M := by
    calc
      T = (T / (3 : ℝ) ^ M) * (3 : ℝ) ^ M := by field_simp
      _ < (3 : ℝ) ^ ℓ * (3 : ℝ) ^ M :=
        mul_lt_mul_of_pos_right hℓ hbase
  calc
    T ≤ (3 : ℝ) ^ ℓ * (3 : ℝ) ^ M := hscaled.le
    _ = (3 : ℝ) ^ (M + (ℓ : ℤ)) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
      ring

/-- Before a positive stopped offset, the preceding threshold still fails. -/
theorem stoppedThreshold_lt_successorScale {g : ℝ} {E : BlockMat d}
    {jStar M : ℤ} {a : CoeffSpace d}
    (hoff : 0 < windowScaleOffset g E jStar M a) :
    ENNReal.ofReal
        ((3 : ℝ) ^ (M + ((windowScaleOffset g E jStar M a - 1 : ℕ) : ℤ))) <
      successorScale g E (M - jStar) a := by
  have hpred : windowScaleOffset g E jStar M a - 1 <
      windowScaleOffset g E jStar M a := Nat.sub_one_lt hoff.ne'
  have hnot := Nat.notMem_of_lt_sInf (s := {ℓ : ℕ |
    successorScale g E (M - jStar) a ≤
      ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ)))}) hpred
  exact lt_of_not_ge hnot

/-- The stopped offset is measurable. -/
theorem measurable_windowScaleOffset (g : ℝ) (E : BlockMat d)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (jStar M : ℤ) : Measurable (windowScaleOffset g E jStar M) := by
  let p : CoeffSpace d → ℕ → Prop := fun a ℓ =>
    successorScale g E (M - jStar) a ≤ ENNReal.ofReal ((3 : ℝ) ^ (M + (ℓ : ℤ)))
  have hp : ∀ ℓ, MeasurableSet {a : CoeffSpace d | p a ℓ} := by
    intro ℓ
    exact measurableSet_le (measurable_successorScale g E hE hEpd (M - jStar))
      measurable_const
  refine measurable_to_countable' fun n => ?_
  cases n with
  | zero =>
      have heq : windowScaleOffset g E jStar M ⁻¹' {0} =
          {a : CoeffSpace d | p a 0} ∪ ⋂ ℓ : ℕ, {a : CoeffSpace d | ¬p a ℓ} := by
        ext a
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
          Set.mem_setOf_eq, Set.mem_iInter]
        rw [windowScaleOffset, Nat.sInf_eq_zero]
        simp only [Set.mem_setOf_eq, Set.eq_empty_iff_forall_notMem]
        rfl
      rw [heq]
      exact (hp 0).union (MeasurableSet.iInter fun ℓ => (hp ℓ).compl)
  | succ n =>
      have heq : windowScaleOffset g E jStar M ⁻¹' {n + 1} =
          {a : CoeffSpace d | p a (n + 1)} \ {a : CoeffSpace d | p a n} := by
        ext a
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]
        change sInf {ℓ : ℕ | p a ℓ} = n + 1 ↔ p a (n + 1) ∧ ¬p a n
        exact Nat.sInf_upward_closed_eq_succ_iff
          (offsetPredicate_upwardClosed g E jStar M a) n
      rw [heq]
      exact (hp (n + 1)).diff (hp n)

/-- The stopped multiplier is measurable. -/
theorem measurable_windowMultiplier (g : ℝ) (E : BlockMat d)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (jStar M : ℤ) : Measurable (windowMultiplier g E jStar M) := by
  have hcast : Measurable fun n : ℕ => (n : ℝ) := measurable_from_nat
  have hexp : Measurable fun a : CoeffSpace d =>
      g * (windowScaleOffset g E jStar M a : ℝ) :=
    (hcast.comp (measurable_windowScaleOffset g E hE hEpd jStar M)).const_mul g
  exact (Real.continuous_const_rpow (by norm_num : (3 : ℝ) ≠ 0)).measurable.comp hexp

/-- The stopped multiplier is at least one for nonnegative source exponent. -/
theorem one_le_windowMultiplier {g : ℝ} (hg : 0 ≤ g) (E : BlockMat d)
    (jStar M : ℤ) (a : CoeffSpace d) : 1 ≤ windowMultiplier g E jStar M a := by
  rw [windowMultiplier]
  exact Real.one_le_rpow (by norm_num) (mul_nonneg hg (Nat.cast_nonneg _))

/-- At exponent zero the stopped multiplier is identically one. -/
theorem windowMultiplier_eq_one (E : BlockMat d) (jStar M : ℤ) (a : CoeffSpace d) :
    windowMultiplier 0 E jStar M a = 1 := by
  simp [windowMultiplier]

end

end Window
end HighContrast
end Homogenization
