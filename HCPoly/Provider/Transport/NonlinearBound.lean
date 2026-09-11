/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.NonlinearRowSum
import HCPoly.Provider.PortableHistory.MajorizationAssembly

/-!
# The transported nonlinear history

The last display of the nonlinear half of the transport,
`e.two.grid.profile`, says that the whole nonlinear history of
the new grid at the new terminal scale is paid for by the portable profile of
the old grid carried from the checkpoint, together with the bridge error and the
transported source rows:

`𝓗_{q'}^nl(n) ≤ C3^{2aℓ₀}𝒫_q(t;b) + Cη_x + C𝓔_src`.

Nothing of the history accumulated before the checkpoint is discarded.  The
argument is the row of `e.two.grid.whitney.mean.bound` at every continued
target level, weighted by `w_n(j)` and summed; the two convolutions convert the
result into the nonlinear history of the old grid at the old terminal scale,
which `e.fixed.geometry.profile.majorization` majorizes by the profile.

The first `ℓ₀` target levels are charged separately.  There the target cell is
one whole-source residual, so by `e.two.grid.whitney.fine.bound` its gain is
paid by the early source coefficient alone, and it carries neither an old gain
nor a boundary row.  The two regimes meet in the single source total on the
right, which runs over every target level.

The passage to `ℝ≥0∞` is done once, on the sum of the rows: each weighted row is
a nonnegative real, so the sum of its images is the image of its sum, and the
real estimate transfers.  The profile is the only summand that can be infinite,
and it enters only through the majorization, on the right.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

section Window

variable {d : ℕ} {P : Measure (CoeffSpace d)} {l : ℤ} {q q' : Mat d} {jStar TMax : ℤ}

/-- **`e.two.grid.profile`.**  The nonlinear history of the new
grid at the new terminal scale is bounded by the portable profile of the old
grid carried from the checkpoint, with the buffer factor `3^{2aℓ₀}`, together
with the bridge error and the weighted source rows, all with one constant.

The rows are the hypothesis, one for each of the two regimes of
`e.two.grid.whitney.fine.bound`.  At a continued target level `j ≥ j_*+ℓ₀`
the gain of the new relative mean is charged to the gain of the old relative
mean at the shifted scale, to the boundary row of the lower scales, to the
bridge error and to the source term `src j`, which stands for the printed
`ε_j + ε_j^Q`.  At an early level `j_* ≤ j < j_*+ℓ₀` the whole target cell is one
source residual and the gain is charged to `src j` alone.  The admissible
constant is exhibited: any `Ctr` above
`(2C_1 + C_2 3^{-(1-g-a)}(1 - 3^{-(1-g-a)})^{-1} + C_3 + C_4)(1 - 3^{-a})^{-1}`
works. -/
theorem nonlinear_bound [NeZero d] [IsProbabilityMeasure P] {Q a g rhoMax : ℝ}
    {C1 C2 C3 C4 Ctr etaX : ℝ} {src : ℤ → ℝ} {lam : ℤ → ℤ} {l0 b n t : ℤ}
    (hQ : 0 < Q) (ha : 0 < a) (hahi : a < 1 - g) (hadm : a ≤ Q * rhoMax - (d : ℝ))
    (hl0 : 1 ≤ l0) (ht : t = n + l0)
    (hP : HCPoly.Frozen.IsStationaryLaw P) (hq : IsRoundedGrid l q) (hlj : l ≤ jStar)
    (hfin : ∀ r : ℤ, jStar ≤ r → r ≤ TMax → HasFiniteAdaptedMean P q r)
    (hjb : jStar ≤ b) (hbt : b ≤ t) (htT : t ≤ TMax)
    (hlam : ∀ j, lam j = 1 ∨ lam j = l0)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (heta : 0 ≤ etaX) (hsrc : ∀ j, 0 ≤ src j)
    (hCtr : (2 * C1 + C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a)))) +
        C3 + C4) / (1 - (3 : ℝ) ^ (-a)) ≤ Ctr)
    (hearly : ∀ j ∈ Finset.Ico jStar (jStar + l0),
      frakH Q (relMean P q' j n) ≤ C4 * src j)
    (hrow : ∀ j ∈ Finset.Ico (jStar + l0) n, frakH Q (relMean P q' j n) ≤
      C1 * frakH Q (relMean P q (j - lam j) t) +
        C2 * ∑ r ∈ Finset.Ico jStar (j - lam j),
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (relMean P q r t) +
        C3 * etaX + C4 * src j) :
    nonlinearHistory P Q a q' jStar n ≤
      ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
          portableProfile P Q a rhoMax q jStar b t +
        ENNReal.ofReal (Ctr * etaX) +
        ENNReal.ofReal (Ctr * ∑ j ∈ Finset.Ico jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j) := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hQ0 : (0 : ℝ) ≤ Q := hQ.le
  have hgeom : (0 : ℝ) < (3 : ℝ) ^ (-a) := PortableHistory.geom_ratio_pos a
  have hdena : (0 : ℝ) < 1 - (3 : ℝ) ^ (-a) := by
    have hr1 := PortableHistory.geom_ratio_lt_one ha
    linarith only [hr1]
  have hc : 0 < 1 - g - a := by linarith only [hahi]
  have hdenb : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 - g - a)) := by
    have hlt := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (by norm_num)
      (neg_neg_iff_pos.mpr hc)
    linarith only [hlt]
  have hkappa : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))) :=
    div_nonneg (Real.rpow_nonneg h3.le _) hdenb.le
  have hbuf : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * a * (l0 : ℝ)) := Real.rpow_nonneg h3.le _
  have hwn : ∀ j : ℤ, (0 : ℝ) ≤ (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) := fun _ =>
    Real.rpow_nonneg h3.le _
  have hlead : (0 : ℝ) ≤ 2 * C1 +
      C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a)))) := by
    have hcc : (0 : ℝ) ≤ C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a)))) :=
      mul_nonneg hC2 hkappa
    linarith only [hC1, hcc]
  -- the old gains are nonnegative on the window
  have hold0 : ∀ r ∈ Finset.Ico jStar t, 0 ≤ frakH Q (relMean P q r t) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.mp hr
    exact PortableHistory.frakH_relMean_nonneg hQ0 hP hq hlj hfin hr1 (le_of_lt hr2) htT
  -- the shifted scale of a continued level lies in the old window
  have hdepth : ∀ j ∈ Finset.Ico (jStar + l0) n,
      jStar ≤ j - lam j ∧ j - lam j < t := by
    intro j hj
    have hmem := Finset.mem_Ico.mp hj
    have hd := one_le_depth_and_le hl0 hlam j
    omega
  -- the majorant of the row, one branch for each regime
  obtain ⟨maj, hmajE, hmajK⟩ : ∃ maj : ℤ → ℝ,
      (∀ j, j < jStar + l0 → maj j = C4 * src j) ∧
        (∀ j, ¬ j < jStar + l0 → maj j =
          C1 * frakH Q (relMean P q (j - lam j) t) +
            C2 * ∑ r ∈ Finset.Ico jStar (j - lam j),
              (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (relMean P q r t) +
            C3 * etaX + C4 * src j) :=
    ⟨fun j => if j < jStar + l0 then C4 * src j else
      C1 * frakH Q (relMean P q (j - lam j) t) +
        C2 * ∑ r ∈ Finset.Ico jStar (j - lam j),
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (relMean P q r t) +
        C3 * etaX + C4 * src j,
      fun _ hj => if_pos hj, fun _ hj => if_neg hj⟩
  have hmajKmem : ∀ j ∈ Finset.Ico (jStar + l0) n, maj j =
      C1 * frakH Q (relMean P q (j - lam j) t) +
        C2 * ∑ r ∈ Finset.Ico jStar (j - lam j),
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (relMean P q r t) +
        C3 * etaX + C4 * src j := by
    intro j hj
    have hmem := Finset.mem_Ico.mp hj
    exact hmajK j (by omega)
  -- the majorant dominates the row at every target level
  have hrowmaj : ∀ j ∈ Finset.Ico jStar n, frakH Q (relMean P q' j n) ≤ maj j := by
    intro j hj
    have hmem := Finset.mem_Ico.mp hj
    by_cases hjl : j < jStar + l0
    · rw [hmajE j hjl]
      exact hearly j (Finset.mem_Ico.mpr ⟨hmem.1, hjl⟩)
    · rw [hmajK j hjl]
      exact hrow j (Finset.mem_Ico.mpr ⟨by omega, hmem.2⟩)
  -- the majorant is nonnegative at every target level
  have hmaj0 : ∀ j ∈ Finset.Ico jStar n, (0 : ℝ) ≤ maj j := by
    intro j hj
    have hmem := Finset.mem_Ico.mp hj
    have h4 : (0 : ℝ) ≤ C4 * src j := mul_nonneg hC4 (hsrc j)
    by_cases hjl : j < jStar + l0
    · rw [hmajE j hjl]
      exact h4
    · have hjK : j ∈ Finset.Ico (jStar + l0) n := Finset.mem_Ico.mpr ⟨by omega, hmem.2⟩
      rw [hmajKmem j hjK]
      have h1 : (0 : ℝ) ≤ C1 * frakH Q (relMean P q (j - lam j) t) :=
        mul_nonneg hC1 (hold0 _ (Finset.mem_Ico.mpr (hdepth j hjK)))
      have h2 : (0 : ℝ) ≤ C2 * ∑ r ∈ Finset.Ico jStar (j - lam j),
          (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) * frakH Q (relMean P q r t) := by
        refine mul_nonneg hC2 (Finset.sum_nonneg fun r hr => ?_)
        refine mul_nonneg (Real.rpow_nonneg h3.le _) (hold0 r ?_)
        exact Finset.Ico_subset_Ico le_rfl (le_of_lt (hdepth j hjK).2) hr
      have h3' : (0 : ℝ) ≤ C3 * etaX := mul_nonneg hC3 heta
      linarith only [h1, h2, h3', h4]
  -- the rows, summed against the target weights
  have hreal := nonlinear_rows_le (a := a) (g := g) ha hahi ht hl0 hlam hC1 hC2 hC3
    heta (hold := fun r => frakH Q (relMean P q r t)) (hnew := maj) (src := src) hold0
    (fun j hj => le_of_eq (hmajE j (Finset.mem_Ico.mp hj).2))
    fun j hj => le_of_eq (hmajKmem j hj)
  -- the source total is nonnegative
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico jStar n,
      (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hwn j) (hsrc j)
  -- the old nonlinear history at the old terminal scale
  have hW : ENNReal.ofReal (∑ m ∈ Finset.Ico jStar t,
      (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * frakH Q (relMean P q m t)) =
      nonlinearHistory P Q a q jStar t := by
    rw [nonlinearHistory]
    exact ENNReal.ofReal_sum_of_nonneg fun m hm =>
      mul_nonneg (Real.rpow_nonneg h3.le _) (hold0 m hm)
  have hmaj : nonlinearHistory P Q a q jStar t ≤
      ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) *
        portableProfile P Q a rhoMax q jStar b t := by
    refine le_trans ?_ (PortableHistory.portable_majorization hQ ha hadm hP hq hlj hfin hjb hbt htT)
    rw [portableHistory]
    exact le_add_self
  -- the three admissible coefficients
  have hCA : (2 * C1 + C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) /
      (1 - (3 : ℝ) ^ (-a)) ≤ Ctr := by
    refine le_trans ?_ hCtr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith only [hC3, hC4]) (inv_pos.mpr hdena).le
  have hCB : C3 / (1 - (3 : ℝ) ^ (-a)) ≤ Ctr := by
    refine le_trans ?_ hCtr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith only [hlead, hC4]) (inv_pos.mpr hdena).le
  have hCC : C4 ≤ Ctr := by
    refine le_trans ?_ hCtr
    rw [le_div_iff₀ hdena]
    have hprod : (0 : ℝ) ≤ C4 * (3 : ℝ) ^ (-a) := mul_nonneg hC4 hgeom.le
    linarith only [hprod, hlead, hC3]
  -- the bulk-and-boundary coefficient against the profile
  have hbulkbound : ENNReal.ofReal ((2 * C1 +
        C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
        (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
        ∑ m ∈ Finset.Ico jStar t,
          (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * frakH Q (relMean P q m t)) ≤
      ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
        portableProfile P Q a rhoMax q jStar b t := by
    have hlead0 : (0 : ℝ) ≤ (2 * C1 +
        C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
        (3 : ℝ) ^ (2 * a * (l0 : ℝ)) := mul_nonneg hlead hbuf
    have hcoef : (2 * C1 +
        C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
        (3 : ℝ) ^ (2 * a * (l0 : ℝ)) * (1 / (1 - (3 : ℝ) ^ (-a))) ≤
        Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hCA hbuf
      have heq : (2 * C1 +
          C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
          (3 : ℝ) ^ (2 * a * (l0 : ℝ)) * (1 / (1 - (3 : ℝ) ^ (-a))) =
          (2 * C1 + C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) /
            (1 - (3 : ℝ) ^ (-a)) * (3 : ℝ) ^ (2 * a * (l0 : ℝ)) := by ring
      linarith only [h, heq]
    have hkey : ENNReal.ofReal ((2 * C1 +
          C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
          (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
          (ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) *
            portableProfile P Q a rhoMax q jStar b t) =
        ENNReal.ofReal ((2 * C1 +
            C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
            (3 : ℝ) ^ (2 * a * (l0 : ℝ)) * (1 / (1 - (3 : ℝ) ^ (-a)))) *
          portableProfile P Q a rhoMax q jStar b t := by
      rw [ENNReal.ofReal_mul hlead0]
      ring
    calc ENNReal.ofReal ((2 * C1 +
            C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
            (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
            ∑ m ∈ Finset.Ico jStar t,
              (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * frakH Q (relMean P q m t))
        = ENNReal.ofReal ((2 * C1 +
            C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
            (3 : ℝ) ^ (2 * a * (l0 : ℝ))) * nonlinearHistory P Q a q jStar t := by
          rw [ENNReal.ofReal_mul hlead0, hW]
      _ ≤ ENNReal.ofReal ((2 * C1 +
            C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
            (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
            (ENNReal.ofReal (1 / (1 - (3 : ℝ) ^ (-a))) *
              portableProfile P Q a rhoMax q jStar b t) := by gcongr
      _ = ENNReal.ofReal ((2 * C1 +
            C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
            (3 : ℝ) ^ (2 * a * (l0 : ℝ)) * (1 / (1 - (3 : ℝ) ^ (-a)))) *
            portableProfile P Q a rhoMax q jStar b t := hkey
      _ ≤ ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
            portableProfile P Q a rhoMax q jStar b t := by
          gcongr
  -- the assembly
  calc nonlinearHistory P Q a q' jStar n
      ≤ ∑ j ∈ Finset.Ico jStar n, ENNReal.ofReal
          ((3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * maj j) := by
        rw [nonlinearHistory]
        exact Finset.sum_le_sum fun j hj =>
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hrowmaj j hj) (hwn j))
    _ = ENNReal.ofReal (∑ j ∈ Finset.Ico jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * maj j) :=
        (ENNReal.ofReal_sum_of_nonneg fun j hj => mul_nonneg (hwn j) (hmaj0 j hj)).symm
    _ ≤ ENNReal.ofReal ((2 * C1 +
            C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
            (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
            (∑ m ∈ Finset.Ico jStar t,
              (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * frakH Q (relMean P q m t)) +
          C3 / (1 - (3 : ℝ) ^ (-a)) * etaX +
          C4 * ∑ j ∈ Finset.Ico jStar n,
            (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal ((2 * C1 +
            C2 * ((3 : ℝ) ^ (-(1 - g - a)) / (1 - (3 : ℝ) ^ (-(1 - g - a))))) *
            (3 : ℝ) ^ (2 * a * (l0 : ℝ)) *
            (∑ m ∈ Finset.Ico jStar t,
              (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (m : ℝ))) * frakH Q (relMean P q m t))) +
          ENNReal.ofReal (C3 / (1 - (3 : ℝ) ^ (-a)) * etaX) +
          ENNReal.ofReal (C4 * ∑ j ∈ Finset.Ico jStar n,
            (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j) :=
        le_trans ENNReal.ofReal_add_le (add_le_add ENNReal.ofReal_add_le le_rfl)
    _ ≤ ENNReal.ofReal (Ctr * (3 : ℝ) ^ (2 * a * (l0 : ℝ))) *
          portableProfile P Q a rhoMax q jStar b t +
        ENNReal.ofReal (Ctr * etaX) +
        ENNReal.ofReal (Ctr * ∑ j ∈ Finset.Ico jStar n,
          (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * src j) := by
        refine add_le_add (add_le_add hbulkbound (ENNReal.ofReal_le_ofReal ?_))
          (ENNReal.ofReal_le_ofReal ?_)
        · exact mul_le_mul_of_nonneg_right hCB heta
        · exact mul_le_mul_of_nonneg_right hCC hS0

end Window

end

end Transport
end HighContrast
end Homogenization
