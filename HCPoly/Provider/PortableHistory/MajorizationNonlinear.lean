/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PortableHistory.Geometric
import HCPoly.Provider.PortableHistory.Transport

/-!
# The nonlinear half of the majorization

The third display of the majorization step of `p.fixed.geometry.one.grid.propagation` transports
the nonlinear history accumulated before the checkpoint to the terminal scale.
By `e.two.grid.mean.split` at the middle scale `b`,

`Σ_{j=j_*}^{b-1} 3^{-a(T-1-j)} 𝔥_Q(P_{j,T}^q)`
`  ≤ 3^{-a(T-b)}(1 + 𝔥_Q(P_{b,T}^q)) 𝓗_q^nl(b)`
`    + 3^{-a(T-b)} 𝔥_Q(P_{b,T}^q) (1 - 3^{-a})^{-1}`,

the second term coming from the geometric total weight of a nonlinear row.  In
the assembled majorization that term is absorbed, up to a constant depending only
on `a`, by the `j = b` term of the last row of
`e.scale.selection.complete.profile`.
-/

namespace Homogenization
namespace HighContrast
namespace PortableHistory

open MeasureTheory

open scoped ENNReal

noncomputable section

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q : Mat d} {jStar TMax : ℤ}

/-- **The nonlinear history accumulated before the checkpoint, transported to the
terminal scale.** -/
theorem nonlinear_low_le [NeZero d] [IsProbabilityMeasure P] {Q a : ℝ} (hQ : 0 ≤ Q)
    (ha : 0 < a) (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q)
    (hlj : l ≤ jStar) (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ TMax → HasFiniteAdaptedMean P q r)
    {b T : ℤ} (hjb : jStar ≤ b) (hbT : b ≤ T) (hT : T ≤ TMax) :
    ∑ j ∈ Finset.Ico jStar b,
        ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j T)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
            (1 + frakH Q (relMean P q b T))) *
          nonlinearHistory P Q a q jStar b +
        ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * frakH Q (relMean P q b T) *
          (1 / (1 - (3 : ℝ) ^ (-a)))) := by
  classical
  have hbTM : b ≤ TMax := le_trans hbT hT
  have hbT0 : (0 : ℝ) ≤ frakH Q (relMean P q b T) :=
    frakH_relMean_nonneg hQ hP hq hlj hfin hjb hbT hT
  have hcoef0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
      (1 + frakH Q (relMean P q b T)) := by positivity
  have hterm : ∀ j ∈ Finset.Ico jStar b,
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) *
          frakH Q (relMean P q j T)) ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
              (1 + frakH Q (relMean P q b T))) *
            ENNReal.ofReal ((3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) *
              frakH Q (relMean P q j b)) +
          ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
            frakH Q (relMean P q b T) * (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ)))) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hjb' : j ≤ b := le_of_lt hj.2
    have hjb0 : (0 : ℝ) ≤ frakH Q (relMean P q j b) :=
      frakH_relMean_nonneg hQ hP hq hlj hfin hj.1 hjb' hbTM
    have htr := frakH_transport_nonlinear hQ hP hq hlj hfin hj.1 hjb' hbT hT
    have hw : (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) =
        (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
          (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring_nf
    have hreal : (3 : ℝ) ^ (-a * ((T : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T) ≤
        (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * (1 + frakH Q (relMean P q b T)) *
            ((3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j b)) +
          (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * frakH Q (relMean P q b T) *
            (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) := by
      have hc : (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
          (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) := by positivity
      rw [hw]
      calc (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
              (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) * frakH Q (relMean P q j T)
          ≤ (3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) *
              (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) *
              ((1 + frakH Q (relMean P q b T)) * frakH Q (relMean P q j b) +
                frakH Q (relMean P q b T)) := mul_le_mul_of_nonneg_left htr hc
        _ = _ := by ring
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hcoef0]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add le_rfl ?_
  have hgeom : ∑ j ∈ Finset.Ico jStar b,
      (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ))) ≤ 1 / (1 - (3 : ℝ) ^ (-a)) :=
    sum_geom_Ico_le ha jStar b
  have hsum : ∑ j ∈ Finset.Ico jStar b,
        ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * frakH Q (relMean P q b T) *
          (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ)))) =
      ENNReal.ofReal ((3 : ℝ) ^ (-a * ((T : ℝ) - (b : ℝ))) * frakH Q (relMean P q b T) *
        ∑ j ∈ Finset.Ico jStar b, (3 : ℝ) ^ (-a * ((b : ℝ) - 1 - (j : ℝ)))) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
    intro j _
    positivity
  rw [hsum]
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_left hgeom (by positivity)

end Window

end

end PortableHistory
end HighContrast
end Homogenization
