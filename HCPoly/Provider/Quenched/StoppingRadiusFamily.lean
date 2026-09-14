/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Window.SharperSuccessorTail
import HCPoly.Provider.Window.Successor
import HCPoly.Provider.Quenched.QuenchedPolynomialNormalizer

/-!
# The generation-indexed family of quenched stopping radii

The endgame replays the window construction once for every generation, against a
reference block that shrinks with the generation, and collects the resulting
strict successors into one family of bad radii, one for each replay of the
quenched construction of `ss.random.dirichlet`.  This file builds that family from
a generation-indexed coarse-ellipticity datum, transports the window's shifted
tail to it, and records the two facts the row estimate needs: the family is
almost everywhere finite, and below it every cell of every inner generation obeys
the discounted Loewner bound.
-/

namespace Homogenization
namespace HighContrast
namespace Quenched

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The growth witness of the window is at least two. -/
private theorem two_le_growthBar (K : ℝ) : (2 : ℝ) ≤ growthBar K := by
  rw [growthBar]
  exact le_max_left _ _

/-- The shifted window tail, transported to a generation-indexed family and read
against a gauge dominating the powered Gaussian one. -/
theorem measureReal_successorScale_gt_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {gg : ℝ} {Eref : ℕ → BlockMat d} {Ψ : ℝ → ℝ} {K Q : ℝ}
    {Shat : CoeffSpace d → ℝ} {jStar M : ℤ} {nstar b : ℕ}
    {mu cd cgauge : ℝ}
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hdag : ∀ n : ℕ, nstar ≤ n →
      HCPoly.Frozen.CoarseEllipticityDagger P gg (Eref n) Ψ K Shat)
    (hmu : 0 < mu) (hcd : 0 < cd)
    (hM : M ≤ (nstar : ℤ)) (hshift : M - jStar + 1 ≤ (nstar : ℤ) + (b : ℤ))
    (hburn : growthBar K ^ (4 * (d + 1)) ≤
      (3 : ℝ) ^ ((nstar : ℝ) + (b : ℝ) - ((M : ℝ) - (jStar : ℝ))))
    (hgauge : ∀ t : ℝ, 1 ≤ t → Real.exp (cgauge * t ^ (2 * mu)) ≤ Ψ t)
    (hcdle : cd ≤ cgauge * ((growthBar K ^ (4 * (d + 1)))⁻¹) ^ (2 * mu) *
      (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + (b : ℝ) - ((M : ℝ) - (jStar : ℝ)))))
    (n q : ℕ) (hn : nstar ≤ n) :
    P.real {a : CoeffSpace d |
        ENNReal.ofReal ((3 : ℝ) ^ (n + q + b)) <
          successorScale gg (Eref n) (M - jStar) a} ≤
      Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))) := by
  have hKc2 : (2 : ℝ) ≤ growthBar K := two_le_growthBar K
  set Kc : ℝ := growthBar K ^ (4 * (d + 1)) with hKcdef
  have hKcpos : 0 < Kc := by
    rw [hKcdef]
    exact pow_pos (by linarith only [hKc2]) _
  set N : ℤ := ((n + q + b : ℕ) : ℤ) with hNdef
  have hMN : M ≤ N := by
    have hcast : (nstar : ℤ) ≤ N := by
      rw [hNdef]
      exact_mod_cast (by omega : nstar ≤ n + q + b)
    exact le_trans hM hcast
  have hland := Window.measureReal_successorScale_gt_zpow_le_sharp
    hstat (hdag n hn) hQ hw hMN
  have hpowcast : (3 : ℝ) ^ N = (3 : ℝ) ^ (n + q + b) := by
    rw [hNdef, zpow_natCast]
  rw [hpowcast] at hland
  refine hland.trans ?_
  -- the shift of the window
  set D : ℤ := N - (M - jStar) with hDdef
  have hD1 : 1 ≤ D := by
    have hbase : (nstar : ℤ) + (b : ℤ) ≤ N := by
      rw [hNdef]
      have : nstar + b ≤ n + q + b := by omega
      exact_mod_cast this
    omega
  have hDreal : (D : ℝ) =
      (n : ℝ) + (q : ℝ) + (b : ℝ) - ((M : ℝ) - (jStar : ℝ)) := by
    rw [hDdef, hNdef]
    push_cast
    ring
  have hDrpow : (3 : ℝ) ^ D = (3 : ℝ) ^ ((D : ℝ)) := (Real.rpow_intCast 3 D).symm
  have hDpos : (0 : ℝ) < (3 : ℝ) ^ D := by positivity
  -- the prefactor is harmless
  have hprefac : (3 / 2 : ℝ) * (3 : ℝ) ^ (-D) ≤ 1 := by
    have hge : (3 : ℝ) ^ (1 : ℤ) ≤ (3 : ℝ) ^ D :=
      zpow_le_zpow_right₀ (by norm_num) hD1
    rw [zpow_one] at hge
    have hinv : (3 : ℝ) ^ (-D) = ((3 : ℝ) ^ D)⁻¹ := zpow_neg 3 D
    rw [hinv]
    have hle : ((3 : ℝ) ^ D)⁻¹ ≤ (3 : ℝ)⁻¹ := by
      rw [inv_le_inv₀ hDpos (by norm_num)]
      exact hge
    nlinarith only [hle, hDpos]
  -- the gauge argument is at least one
  have hburnD : Kc ≤ (3 : ℝ) ^ D := by
    refine le_trans hburn ?_
    rw [hDrpow]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hnr : (nstar : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    have hqr : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    rw [hDreal]
    linarith only [hnr, hqr]
  have hx1 : (1 : ℝ) ≤ Kc⁻¹ * (3 : ℝ) ^ D := by
    rw [← inv_mul_cancel₀ (ne_of_gt hKcpos)]
    exact mul_le_mul_of_nonneg_left hburnD (inv_nonneg.2 hKcpos.le)
  have hxpos : (0 : ℝ) < Kc⁻¹ * (3 : ℝ) ^ D := lt_of_lt_of_le zero_lt_one hx1
  -- the gauge dominates the powered Gaussian one
  have hgaugeApp :
      (Ψ (Kc⁻¹ * (3 : ℝ) ^ D))⁻¹ ≤
        Real.exp (-(cgauge * (Kc⁻¹ * (3 : ℝ) ^ D) ^ (2 * mu))) := by
    have hle := hgauge (Kc⁻¹ * (3 : ℝ) ^ D) hx1
    have hpos : (0 : ℝ) <
        Real.exp (cgauge * (Kc⁻¹ * (3 : ℝ) ^ D) ^ (2 * mu)) := Real.exp_pos _
    have hinv := inv_anti₀ hpos hle
    rwa [← Real.exp_neg] at hinv
  -- the exponent dominates the target one
  have hmu2 : (0 : ℝ) ≤ 2 * mu := by linarith only [hmu]
  have hsplit : (Kc⁻¹ * (3 : ℝ) ^ D) ^ (2 * mu) =
      (Kc⁻¹) ^ (2 * mu) *
        ((3 : ℝ) ^ (2 * mu * (q : ℝ)) *
          (3 : ℝ) ^ (2 * mu * ((n : ℝ) + (b : ℝ) -
            ((M : ℝ) - (jStar : ℝ))))) := by
    rw [Real.mul_rpow (inv_nonneg.2 hKcpos.le) hDpos.le, hDrpow,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), ← Real.rpow_add (by norm_num)]
    congr 2
    rw [hDreal]
    ring
  have hshiftMono :
      (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + (b : ℝ) -
          ((M : ℝ) - (jStar : ℝ)))) ≤
        (3 : ℝ) ^ (2 * mu * ((n : ℝ) + (b : ℝ) -
          ((M : ℝ) - (jStar : ℝ)))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hnr : (nstar : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    exact mul_le_mul_of_nonneg_left (by linarith only [hnr]) hmu2
  have hexpArg :
      cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)) ≤
        cgauge * (Kc⁻¹ * (3 : ℝ) ^ D) ^ (2 * mu) := by
    have hqpos : (0 : ℝ) < (3 : ℝ) ^ (2 * mu * (q : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hcginv : (0 : ℝ) ≤ cgauge * (Kc⁻¹) ^ (2 * mu) := by
      have hcg : 0 < cgauge := by
        by_contra hcon
        push Not at hcon
        have hbad : cgauge * ((Kc⁻¹) ^ (2 * mu) *
            (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + (b : ℝ) -
              ((M : ℝ) - (jStar : ℝ))))) ≤ 0 := by
          have hfac : (0 : ℝ) ≤ (Kc⁻¹) ^ (2 * mu) *
              (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + (b : ℝ) -
                ((M : ℝ) - (jStar : ℝ)))) := by positivity
          exact mul_nonpos_of_nonpos_of_nonneg hcon hfac
        nlinarith only [hcdle, hbad, hcd]
      positivity
    have hstep : cgauge * (Kc⁻¹) ^ (2 * mu) *
        (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + (b : ℝ) -
          ((M : ℝ) - (jStar : ℝ)))) ≤
        cgauge * (Kc⁻¹) ^ (2 * mu) *
          (3 : ℝ) ^ (2 * mu * ((n : ℝ) + (b : ℝ) -
            ((M : ℝ) - (jStar : ℝ)))) :=
      mul_le_mul_of_nonneg_left hshiftMono hcginv
    have hcd' : cd ≤ cgauge * (Kc⁻¹) ^ (2 * mu) *
        (3 : ℝ) ^ (2 * mu * ((n : ℝ) + (b : ℝ) -
          ((M : ℝ) - (jStar : ℝ)))) := by
      exact le_trans hcdle hstep
    have hmul := mul_le_mul_of_nonneg_right hcd' hqpos.le
    rw [hsplit]
    calc
      cd * (3 : ℝ) ^ (2 * mu * (q : ℝ))
          ≤ cgauge * (Kc⁻¹) ^ (2 * mu) *
              (3 : ℝ) ^ (2 * mu * ((n : ℝ) + (b : ℝ) -
                ((M : ℝ) - (jStar : ℝ)))) *
              (3 : ℝ) ^ (2 * mu * (q : ℝ)) := hmul
      _ = cgauge * ((Kc⁻¹) ^ (2 * mu) *
              ((3 : ℝ) ^ (2 * mu * (q : ℝ)) *
                (3 : ℝ) ^ (2 * mu * ((n : ℝ) + (b : ℝ) -
                  ((M : ℝ) - (jStar : ℝ)))))) := by ring
  -- assemble
  have hgaugeNonneg : (0 : ℝ) ≤ (Ψ (Kc⁻¹ * (3 : ℝ) ^ D))⁻¹ := by
    have hle := hgauge (Kc⁻¹ * (3 : ℝ) ^ D) hx1
    have hpos : (0 : ℝ) < Ψ (Kc⁻¹ * (3 : ℝ) ^ D) :=
      lt_of_lt_of_le (Real.exp_pos _) hle
    exact (inv_pos.2 hpos).le
  calc
    (3 / 2 : ℝ) * (3 : ℝ) ^ (-D) * (Ψ (Kc⁻¹ * (3 : ℝ) ^ D))⁻¹
        ≤ 1 * (Ψ (Kc⁻¹ * (3 : ℝ) ^ D))⁻¹ :=
      mul_le_mul_of_nonneg_right hprefac hgaugeNonneg
    _ = (Ψ (Kc⁻¹ * (3 : ℝ) ^ D))⁻¹ := one_mul _
    _ ≤ Real.exp (-(cgauge * (Kc⁻¹ * (3 : ℝ) ^ D) ^ (2 * mu))) := hgaugeApp
    _ ≤ Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))) :=
      Real.exp_le_exp.mpr (neg_le_neg hexpArg)

/-- The stopping radius of every admissible generation is almost everywhere
finite. -/
theorem ae_successorScale_ne_top [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {gg : ℝ} {Eref : ℕ → BlockMat d} {Ψ : ℝ → ℝ} {K Q : ℝ}
    {Shat : CoeffSpace d → ℝ} {jStar M : ℤ} {nstar b : ℕ}
    {mu cd cgauge : ℝ}
    (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    (hdag : ∀ n : ℕ, nstar ≤ n →
      HCPoly.Frozen.CoarseEllipticityDagger P gg (Eref n) Ψ K Shat)
    (hmu : 0 < mu) (hcd : 0 < cd)
    (hM : M ≤ (nstar : ℤ)) (hshift : M - jStar + 1 ≤ (nstar : ℤ) + (b : ℤ))
    (hburn : growthBar K ^ (4 * (d + 1)) ≤
      (3 : ℝ) ^ ((nstar : ℝ) + (b : ℝ) - ((M : ℝ) - (jStar : ℝ))))
    (hgauge : ∀ t : ℝ, 1 ≤ t → Real.exp (cgauge * t ^ (2 * mu)) ≤ Ψ t)
    (hcdle : cd ≤ cgauge * ((growthBar K ^ (4 * (d + 1)))⁻¹) ^ (2 * mu) *
      (3 : ℝ) ^ (2 * mu * ((nstar : ℝ) + (b : ℝ) - ((M : ℝ) - (jStar : ℝ)))))
    (n : ℕ) (hn : nstar ≤ n) :
    ∀ᵐ a ∂P, successorScale gg (Eref n) (M - jStar) a ≠ ⊤ := by
  set T : Set (CoeffSpace d) :=
    {a | successorScale gg (Eref n) (M - jStar) a = ⊤} with hT
  have hbound : ∀ q : ℕ,
      P.real T ≤ Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))) := by
    intro q
    have hsub : T ⊆ {a : CoeffSpace d |
        ENNReal.ofReal ((3 : ℝ) ^ (n + q + b)) <
          successorScale gg (Eref n) (M - jStar) a} := by
      intro a ha
      simp only [hT, Set.mem_ofPred_eq] at ha
      simp only [Set.mem_ofPred_eq, ha]
      exact ENNReal.ofReal_lt_top
    exact (measureReal_mono hsub).trans
      (measureReal_successorScale_gt_le hstat hQ hw hdag hmu hcd hM hshift hburn
        hgauge hcdle n q hn)
  have hzero : P.real T ≤ 0 := by
    have hpow : _root_.Filter.Tendsto
        (fun q : ℕ => cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))
        _root_.Filter.atTop _root_.Filter.atTop := by
      have hcast : _root_.Filter.Tendsto (fun q : ℕ => (q : ℝ))
          _root_.Filter.atTop _root_.Filter.atTop := tendsto_natCast_atTop_atTop
      have hlin : _root_.Filter.Tendsto (fun q : ℕ => 2 * mu * (q : ℝ))
          _root_.Filter.atTop _root_.Filter.atTop :=
        _root_.Filter.Tendsto.const_mul_atTop (by linarith only [hmu]) hcast
      have hexp : _root_.Filter.Tendsto (fun x : ℝ => (3 : ℝ) ^ x)
          _root_.Filter.atTop _root_.Filter.atTop := by
        have hrw : (fun x : ℝ => (3 : ℝ) ^ x) =
            fun x : ℝ => Real.exp (Real.log 3 * x) := by
          funext x
          exact Real.rpow_def_of_pos (by norm_num) x
        rw [hrw]
        exact Real.tendsto_exp_atTop.comp
          (_root_.Filter.Tendsto.const_mul_atTop (Real.log_pos (by norm_num))
            _root_.Filter.tendsto_id)
      exact _root_.Filter.Tendsto.const_mul_atTop hcd (hexp.comp hlin)
    have htend : _root_.Filter.Tendsto
        (fun q : ℕ => Real.exp (-(cd * (3 : ℝ) ^ (2 * mu * (q : ℝ)))))
        _root_.Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp (_root_.Filter.tendsto_neg_atTop_atBot.comp hpow)
    exact ge_of_tendsto htend (_root_.Filter.Eventually.of_forall hbound)
  have hmeasure : P T = 0 := by
    have hnonneg : (0 : ℝ) ≤ P.real T := measureReal_nonneg
    have hreal : P.real T = 0 := le_antisymm hzero hnonneg
    rcases (ENNReal.toReal_eq_zero_iff (P T)).1 hreal with hz | hz
    · exact hz
    · exact absurd hz (measure_ne_top P T)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hmeasure] with a ha
  exact ha

end

end Quenched
end HighContrast
end Homogenization
