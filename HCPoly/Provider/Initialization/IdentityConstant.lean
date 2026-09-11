/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Initialization.IdentityMoment
import HCPoly.Geometry.ReferenceAspectRatio

/-!
# A common identity-grid initialization constant

The moment coefficient and the logarithmic conversion coefficient admit one
positive maximum.  The logarithmic estimate is separated from the external
reference comparison that supplies the upper bound on the identity constant.
-/

namespace Homogenization
namespace HighContrast
namespace Initialization

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit moment and logarithmic coefficients are simultaneously
bounded by one positive constant. -/
theorem exists_initialization_constant (d : ℕ) (hd : 2 ≤ d) (g : ℝ) :
    ∃ CdQ : ℝ, 0 < CdQ ∧
      2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
          (1 + 2 * (d : ℝ)) ≤ CdQ ∧
      2 * (d : ℝ) * (1 + Real.log 24 / Real.log 3) ≤ CdQ := by
  let A : ℝ := 2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
    (1 + 2 * (d : ℝ))
  let B : ℝ := 2 * (d : ℝ) * (1 + Real.log 24 / Real.log 3)
  have hd0 : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hA : 0 < A := by
    change 0 < 2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
      (1 + 2 * (d : ℝ))
    positivity
  refine ⟨max A B + 1, ?_, ?_, ?_⟩
  · have hmax : A ≤ max A B := le_max_left A B
    linarith only [hA, hmax]
  · change A ≤ max A B + 1
    have hmax : A ≤ max A B := le_max_left A B
    linarith only [hmax]
  · change B ≤ max A B + 1
    have hmax : B ≤ max A B := le_max_right A B
    linarith only [hmax]

/-- If the identity constant is at most `24 Π`, its determinant budget is
absorbed by the common logarithmic initialization coefficient. -/
theorem identity_log_bound {E : BlockMat d} {CdQ : ℝ}
    (hPi : 1 ≤ aspectRatio E) (hI1 : 1 ≤ initIdentityConst E)
    (hIup : initIdentityConst E ≤ 24 * aspectRatio E)
    (hCd : 2 * (d : ℝ) * (1 + Real.log 24 / Real.log 3) ≤ CdQ) :
    2 * (d : ℝ) * Real.log (initIdentityConst E) ≤
      CdQ * Real.log (2 + aspectRatio E) := by
  have hPi0 : 0 < aspectRatio E := lt_of_lt_of_le zero_lt_one hPi
  have hI0 : 0 < initIdentityConst E := lt_of_lt_of_le zero_lt_one hI1
  have h24Pi0 : 0 < 24 * aspectRatio E := by positivity
  have hlogI : Real.log (initIdentityConst E) ≤
      Real.log (24 * aspectRatio E) :=
    Real.log_le_log hI0 hIup
  have hlogMul : Real.log (24 * aspectRatio E) =
      Real.log 24 + Real.log (aspectRatio E) :=
    Real.log_mul (by norm_num) hPi0.ne'
  have h3le : (3 : ℝ) ≤ 2 + aspectRatio E := by
    linarith only [hPi]
  have hPile : aspectRatio E ≤ 2 + aspectRatio E := by norm_num
  have hlogPi : Real.log (aspectRatio E) ≤
      Real.log (2 + aspectRatio E) :=
    Real.log_le_log hPi0 hPile
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog24nonneg : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
  have hlog3 : Real.log 3 ≤ Real.log (2 + aspectRatio E) :=
    Real.log_le_log (by norm_num) h3le
  have hlog24 : Real.log 24 ≤
      (Real.log 24 / Real.log 3) * Real.log (2 + aspectRatio E) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog3pos]
    exact mul_le_mul_of_nonneg_left hlog3 hlog24nonneg
  have hlogMain : Real.log (initIdentityConst E) ≤
      (1 + Real.log 24 / Real.log 3) * Real.log (2 + aspectRatio E) := by
    calc
      Real.log (initIdentityConst E) ≤
          Real.log 24 + Real.log (aspectRatio E) := by
        rw [← hlogMul]
        exact hlogI
      _ ≤ (Real.log 24 / Real.log 3) * Real.log (2 + aspectRatio E) +
          Real.log (2 + aspectRatio E) := add_le_add hlog24 hlogPi
      _ = (1 + Real.log 24 / Real.log 3) *
          Real.log (2 + aspectRatio E) := by ring
  have hdim0 : 0 ≤ 2 * (d : ℝ) := by positivity
  have hlogBase0 : 0 ≤ Real.log (2 + aspectRatio E) :=
    Real.log_nonneg (by linarith only [hPi])
  calc
    2 * (d : ℝ) * Real.log (initIdentityConst E) ≤
        2 * (d : ℝ) *
          ((1 + Real.log 24 / Real.log 3) *
            Real.log (2 + aspectRatio E)) :=
      mul_le_mul_of_nonneg_left hlogMain hdim0
    _ = (2 * (d : ℝ) * (1 + Real.log 24 / Real.log 3)) *
        Real.log (2 + aspectRatio E) := by ring
    _ ≤ CdQ * Real.log (2 + aspectRatio E) :=
      mul_le_mul_of_nonneg_right hCd hlogBase0

/-- Any constant above the explicit moment coefficient gives the centered
identity-grid moment clause with that common constant. -/
theorem identity_centeredMoment_le_of_constant [NeZero d] [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    {Ψ : ℝ → ℝ} {K Cd CdQ : ℝ} {jStar M r : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    (hjr : jStar ≤ r) (hrM : r ≤ M)
    (hCdQ : 2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
        (1 + 2 * (d : ℝ)) ≤ CdQ) :
    centeredMoment P ((initExpQ d g : ℕ) : ℝ)
        (roundedGrid jStar (1 : Mat d)) r ≤
      ENNReal.ofReal (CdQ * initIdentityConst E) := by
  have hmoment := identity_centeredMoment_le
    hg hE hEpd hsharp hw hY hjr hrM
  refine hmoment.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right hCdQ
    (le_trans zero_le_one (one_le_initIdentityConst hE hEpd hsharp))

/-- The same common constant absorbs both general-grid initialization moments. -/
theorem adapted_moment_bounds_of_constant [NeZero d] [Nonempty (Fin d)]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hsharp : BlockMatLoewnerLE (blockSharp E) E)
    {Ψ : ℝ → ℝ} {K Cd CdQ : ℝ} (hCd : 1 ≤ Cd) {jStar M : ℤ}
    (hw : IsCoupledWindow d ((initExpQ d g : ℕ) : ℝ) K jStar M)
    {Y : CoeffSpace d → ℝ}
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {mu : Mat d} (hmu : mu.PosDef) {r : ℤ} {w : Fin d → ℤ}
    (hindex : IsAdmissibleIndex (roundedGrid jStar mu) jStar M r w)
    (hCdQ : 2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
        (1 + 2 * (d : ℝ)) ≤ CdQ) :
    lqSchattenSize P ((initExpQ d g : ℕ) : ℝ)
        (adaptedResponse (roundedGrid jStar mu) r w)
        (adaptedMean P (roundedGrid jStar mu) r) ≤
      ENNReal.ofReal (CdQ * initGridConst Cd g E mu) ∧
      centeredMoment P ((initExpQ d g : ℕ) : ℝ)
          (roundedGrid jStar mu) r ≤
        ENNReal.ofReal (CdQ * initGridConst Cd g E mu) := by
  have hmoment := adapted_moment_bounds
    hg hE hEpd hsharp hCd hw hY hmu hindex
  have hkap : 1 ≤ kappaRef E := one_le_kappaRef hE hEpd hsharp
  have hB : 1 ≤ boundaryConst Cd g mu := one_le_boundaryConst hCd hg hmu
  have hBsq : 1 ≤ boundaryConst Cd g mu ^ 2 := by
    nlinarith only [hB]
  have hC : 0 ≤ initGridConst Cd g E mu := by
    rw [initGridConst]
    exact le_trans zero_le_one <| one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hkap hBsq) (by norm_num)
  have hscale : ENNReal.ofReal
      ((2 * (2 * d : ℝ) ^ (((initExpQ d g : ℕ) : ℝ))⁻¹ *
          (1 + 2 * (d : ℝ))) * initGridConst Cd g E mu) ≤
      ENNReal.ofReal (CdQ * initGridConst Cd g E mu) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCdQ hC)
  exact ⟨hmoment.1.trans hscale, hmoment.2.trans hscale⟩

end

end Initialization
end HighContrast
end Homogenization
