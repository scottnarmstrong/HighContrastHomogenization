/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.CenteredResponseAbsolute
import HCPoly.Provider.Response.ConstantSkewAdjoint

/-!
# Mixed pre-Young insertion

The two extended-nonnegative compact bounds are combined before returning to
the real-valued normalized response supremum.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory Set

open scoped ENNReal Matrix

noncomputable section

/-- Two mixed extended-nonnegative pre-Young bounds combine without taking
`toReal` of either row or weak term. -/
theorem response_pair_le_of_pre_young {Jminus Jplus omega kappa : ℝ}
    {preYoungMinus preYoungPlus : ℝ≥0∞}
    (hpreYoungMinus : ENNReal.ofReal |Jminus| ≤ preYoungMinus)
    (hpreYoungPlus : ENNReal.ofReal |Jplus| ≤ preYoungPlus)
    (hallocation : preYoungMinus + preYoungPlus ≤
      ENNReal.ofReal (omega * kappa))
    (hnonneg : 0 ≤ omega * kappa) :
    |Jminus| + |Jplus| ≤ omega * kappa := by
  apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
  rw [ENNReal.ofReal_add (abs_nonneg Jminus) (abs_nonneg Jplus)]
  exact (add_le_add hpreYoungMinus hpreYoungPlus).trans hallocation

/-- Pointwise mixed pre-Young allocations at the true Schur loads give the
literal response supremum consumed by the terminal endgame. -/
theorem centered_response_sup_le_of_pre_young {d : ℕ} [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) {S SStar K : Mat d}
    {omega kappa : ℝ} (hnonneg : 0 ≤ omega * kappa)
    (preYoungMinus preYoungPlus : Vec d → ℝ≥0∞)
    (hpreYoungMinus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      ENNReal.ofReal
          |centeredResponse P U (centeredResponseLoadP S SStar K e)
            (centeredResponseLoadQ S SStar K e -
              responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| ≤
        preYoungMinus e)
    (hpreYoungPlus : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      ENNReal.ofReal
          |centeredAdjointResponse P U
            (centeredResponseLoadP S SStar K e)
            (centeredResponseLoadQ S SStar K e +
              responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| ≤
        preYoungPlus e)
    (hallocation : ∀ e : Vec d, e ⬝ᵥ e = 1 →
      preYoungMinus e + preYoungPlus e ≤ ENNReal.ofReal (omega * kappa)) :
    sSup
        ((fun e : Vec d ↦
            |centeredResponse P U (centeredResponseLoadP S SStar K e)
                (centeredResponseLoadQ S SStar K e -
                  responseSkew K *ᵥ centeredResponseLoadP S SStar K e)| +
              |centeredAdjointResponse P U
                (centeredResponseLoadP S SStar K e)
                (centeredResponseLoadQ S SStar K e +
                  responseSkew K *ᵥ centeredResponseLoadP S SStar K e)|) ''
          {e : Vec d | e ⬝ᵥ e = 1}) ≤ omega * kappa := by
  apply csSup_le
  · have i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    let e0 : Vec d := Pi.single i0 1
    have he0 : e0 ⬝ᵥ e0 = 1 := by
      simp [e0, dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
    exact ⟨_, ⟨e0, he0, rfl⟩⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := hx
    exact response_pair_le_of_pre_young (hpreYoungMinus e he)
      (hpreYoungPlus e he) (hallocation e he) hnonneg

end


end Homogenization.HighContrast.Response
