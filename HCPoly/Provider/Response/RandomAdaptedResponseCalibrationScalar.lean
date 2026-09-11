/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.LoadCalibration

/-!
# Scalar consequences of response-load calibration

The determinant comparison converts the terminal response ratio, energies,
defects, and load products into powers of the earlier canonical imbalance.
-/

namespace Homogenization.HighContrast.Response

open scoped ENNReal

noncomputable section

/-- The terminal response-ratio bound and determinant comparison give the
calibrated square-root response scale. -/
theorem sqrt_theta_le_chi {d : ℕ}
    {theta kappaT kappaS R chi : ℝ}
    (hR : 0 ≤ R)
    (htheta : theta ≤ (3 * kappaT - 1) / 2)
    (hcompare : kappaT ≤ R ^ (d : ℝ) * kappaS)
    (hchi : chi = Real.sqrt (3 / 2) * R ^ ((d : ℝ) / 2)) :
    Real.sqrt theta ≤ chi * Real.sqrt kappaS := by
  have htheta' : theta ≤ (3 / 2 : ℝ) * kappaT := by
    linarith only [htheta]
  have hthree : 0 ≤ (3 / 2 : ℝ) := by norm_num
  calc
    Real.sqrt theta ≤ Real.sqrt ((3 / 2 : ℝ) * kappaT) :=
      Real.sqrt_le_sqrt htheta'
    _ ≤ Real.sqrt ((3 / 2 : ℝ) * (R ^ (d : ℝ) * kappaS)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcompare hthree)
    _ = chi * Real.sqrt kappaS := by
      have hrootR : Real.sqrt (R ^ (d : ℝ)) = R ^ ((d : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR]
        congr 1
        ring
      rw [hchi, Real.sqrt_mul hthree,
        Real.sqrt_mul (Real.rpow_nonneg hR (d : ℝ)), hrootR]
      ring

/-- The annealed energy chain is bounded by the calibrated energy constant. -/
theorem energy_le_a_star {EJ theta chi AStar kappa : ℝ}
    (hroot : Real.sqrt theta ≤ chi * Real.sqrt kappa)
    (henergy : EJ ≤ 2 * Real.sqrt theta)
    (hAStar : AStar = 2 * chi) :
    EJ ≤ AStar * Real.sqrt kappa := by
  calc
    EJ ≤ 2 * Real.sqrt theta := henergy
    _ ≤ 2 * (chi * Real.sqrt kappa) :=
      mul_le_mul_of_nonneg_left hroot (by norm_num)
    _ = AStar * Real.sqrt kappa := by rw [hAStar]; ring

/-- The terminal defect chain is bounded by the calibrated defect constant. -/
theorem defect_le_t_star
    {tau rhoPow Rpow theta chi TStar kappa : ℝ}
    (hrho : rhoPow ≤ Rpow) (hRpow : 1 ≤ Rpow)
    (hroot : Real.sqrt theta ≤ chi * Real.sqrt kappa)
    (htau : tau ≤ 2 * (rhoPow - 1) * Real.sqrt theta)
    (hTStar : TStar = 2 * (Rpow - 1) * chi) :
    tau ≤ TStar * Real.sqrt kappa := by
  have hrhoSub : rhoPow - 1 ≤ Rpow - 1 := sub_le_sub_right hrho 1
  have hRminus : 0 ≤ Rpow - 1 := sub_nonneg.mpr hRpow
  calc
    tau ≤ 2 * (rhoPow - 1) * Real.sqrt theta := htau
    _ ≤ 2 * (Rpow - 1) * Real.sqrt theta := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrhoSub (by norm_num))
        (Real.sqrt_nonneg _)
    _ ≤ 2 * (Rpow - 1) * (chi * Real.sqrt kappa) :=
      mul_le_mul_of_nonneg_left hroot
        (mul_nonneg (by norm_num) hRminus)
    _ = TStar * Real.sqrt kappa := by rw [hTStar]; ring

/-- A determinant-power comparison passes through the square root with the
exact half-dimensional exponent. -/
theorem sqrt_comparison_le {d : ℕ} {x y R : ℝ}
    (hR : 0 ≤ R) (hxy : x ≤ R ^ (d : ℝ) * y) :
    Real.sqrt x ≤ R ^ ((d : ℝ) / 2) * Real.sqrt y := by
  have hrootR : Real.sqrt (R ^ (d : ℝ)) = R ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR]
    congr 1
    ring
  calc
    Real.sqrt x ≤ Real.sqrt (R ^ (d : ℝ) * y) :=
      Real.sqrt_le_sqrt hxy
    _ = R ^ ((d : ℝ) / 2) * Real.sqrt y := by
      rw [Real.sqrt_mul (Real.rpow_nonneg hR _), hrootR]

/-- The same determinant-power comparison at exponent one quarter. -/
theorem quarter_power_comparison_le {d : ℕ} {x y R : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hR : 0 ≤ R)
    (hxy : x ≤ R ^ (d : ℝ) * y) :
    x ^ (1 / 4 : ℝ) ≤
      R ^ ((d : ℝ) / 4) * y ^ (1 / 4 : ℝ) := by
  calc
    x ^ (1 / 4 : ℝ) ≤ (R ^ (d : ℝ) * y) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hx hxy (by norm_num)
    _ = R ^ ((d : ℝ) / 4) * y ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hR _) hy,
        ← Real.rpow_mul hR]
      congr 2
      ring

/-- A double square root is the nonnegative one-quarter power. -/
theorem sqrt_sqrt_eq_quarter_power {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Calibrated quarter-power load bounds give the two products in the weak
profile estimate. -/
theorem load_product_bounds
    {K Len Lam KStar LenStar LambdaStar kappa : ℝ}
    (hKStar : 0 ≤ KStar) (hkappa : 0 ≤ kappa)
    (hK : K ≤ KStar * kappa ^ (1 / 4 : ℝ))
    (hLen : Len ≤ LenStar * kappa ^ (1 / 4 : ℝ))
    (hLam : Lam ≤ LambdaStar * kappa ^ (1 / 4 : ℝ))
    (hLen0 : 0 ≤ Len) (hLam0 : 0 ≤ Lam) :
    K * Len ≤ KStar * LenStar * Real.sqrt kappa ∧
      K * Lam ≤ KStar * LambdaStar * Real.sqrt kappa := by
  have hquarter : 0 ≤ kappa ^ (1 / 4 : ℝ) := Real.rpow_nonneg hkappa _
  have hsquare : kappa ^ (1 / 4 : ℝ) * kappa ^ (1 / 4 : ℝ) =
      Real.sqrt kappa := by
    rw [← Real.rpow_add_of_nonneg hkappa (by norm_num) (by norm_num),
      Real.sqrt_eq_rpow]
    norm_num
  constructor
  · calc
      K * Len ≤ (KStar * kappa ^ (1 / 4 : ℝ)) *
          (LenStar * kappa ^ (1 / 4 : ℝ)) :=
        mul_le_mul hK hLen hLen0 (mul_nonneg hKStar hquarter)
      _ = KStar * LenStar * Real.sqrt kappa := by rw [← hsquare]; ring
  · calc
      K * Lam ≤ (KStar * kappa ^ (1 / 4 : ℝ)) *
          (LambdaStar * kappa ^ (1 / 4 : ℝ)) :=
        mul_le_mul hK hLam hLam0 (mul_nonneg hKStar hquarter)
      _ = KStar * LambdaStar * Real.sqrt kappa := by rw [← hsquare]; ring

/-- A calibrated hatted-row estimate has the response-window
`kappa^(3/2)` scale. -/
theorem row_le_l_star
    {row : ℝ≥0∞}
    {Gamma ceps beta kappaT kappaS Rhalf chi
      GammaStar cepsStar betaStar LStar : ℝ}
    (hGamma0 : 0 ≤ Gamma) (hceps0 : 0 ≤ ceps) (hbeta0 : 0 ≤ beta)
    (hRhalf : 1 ≤ Rhalf) (hkappa : 1 ≤ kappaS)
    (hGamma : Gamma ≤ GammaStar) (hceps : ceps ≤ cepsStar)
    (hbeta : beta ≤ betaStar)
    (hkappaRoot : Real.sqrt kappaT ≤ Rhalf * Real.sqrt kappaS)
    {theta : ℝ} (htheta : Real.sqrt theta ≤ chi * Real.sqrt kappaS)
    (hrow : row ≤ ENNReal.ofReal
      (16 * Gamma * ceps * beta * Real.sqrt kappaS *
        (Real.sqrt kappaT + 1) * Real.sqrt theta))
    (hLStar : LStar =
      32 * GammaStar * cepsStar * betaStar * Rhalf * chi) :
    row ≤ ENNReal.ofReal (LStar * kappaS ^ (3 / 2 : ℝ)) := by
  have hkappa0 : 0 ≤ kappaS := zero_le_one.trans hkappa
  have hGammaStar0 : 0 ≤ GammaStar := hGamma0.trans hGamma
  have hcepsStar0 : 0 ≤ cepsStar := hceps0.trans hceps
  have hbetaStar0 : 0 ≤ betaStar := hbeta0.trans hbeta
  have hsqrtOne : 1 ≤ Real.sqrt kappaS := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hkappa
  have hsum : Real.sqrt kappaT + 1 ≤
      2 * Rhalf * Real.sqrt kappaS := by
    calc
      Real.sqrt kappaT + 1 ≤
          Rhalf * Real.sqrt kappaS + Real.sqrt kappaS :=
        add_le_add hkappaRoot hsqrtOne
      _ ≤ Rhalf * Real.sqrt kappaS + Rhalf * Real.sqrt kappaS := by
        have hsqrtScale : Real.sqrt kappaS ≤
            Rhalf * Real.sqrt kappaS := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hRhalf (Real.sqrt_nonneg kappaS)
        exact add_le_add le_rfl hsqrtScale
      _ = 2 * Rhalf * Real.sqrt kappaS := by ring
  have hreal :
      16 * Gamma * ceps * beta * Real.sqrt kappaS *
          (Real.sqrt kappaT + 1) * Real.sqrt theta ≤
        LStar * kappaS ^ (3 / 2 : ℝ) := by
    calc
      16 * Gamma * ceps * beta * Real.sqrt kappaS *
          (Real.sqrt kappaT + 1) * Real.sqrt theta ≤
        16 * GammaStar * cepsStar * betaStar * Real.sqrt kappaS *
          (2 * Rhalf * Real.sqrt kappaS) *
            (chi * Real.sqrt kappaS) := by
          gcongr
      _ = LStar * kappaS ^ (3 / 2 : ℝ) := by
        have hsqrtCube : Real.sqrt kappaS * Real.sqrt kappaS *
            Real.sqrt kappaS = kappaS ^ (3 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add
            (zero_lt_one.trans_le hkappa), ← Real.rpow_add
            (zero_lt_one.trans_le hkappa)]
          norm_num
        rw [hLStar]
        calc
          16 * GammaStar * cepsStar * betaStar * Real.sqrt kappaS *
              (2 * Rhalf * Real.sqrt kappaS) *
                (chi * Real.sqrt kappaS) =
              32 * GammaStar * cepsStar * betaStar * Rhalf * chi *
                (Real.sqrt kappaS * Real.sqrt kappaS *
                  Real.sqrt kappaS) := by ring
          _ = _ := by rw [hsqrtCube]
  exact hrow.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The bad and good profile energies combine at the literal response-window
energy constant. -/
theorem energy_sum_le
    {bad good : ℝ≥0∞} {sqrtTwo Lam BStar expo : ℝ}
    (hSqrtTwo : 0 ≤ sqrtTwo) (hLam : 0 ≤ Lam)
    (hBStar : 0 ≤ BStar) (hexpo : 0 ≤ expo)
    (hbad : bad ≤ ENNReal.ofReal (sqrtTwo * Lam * BStar))
    (hgood : good ≤ ENNReal.ofReal (sqrtTwo * expo * Lam)) :
    bad + good ≤
      ENNReal.ofReal (sqrtTwo * Lam * (BStar + expo)) := by
  calc
    bad + good ≤ ENNReal.ofReal (sqrtTwo * Lam * BStar) +
        ENNReal.ofReal (sqrtTwo * expo * Lam) := add_le_add hbad hgood
    _ = ENNReal.ofReal
        (sqrtTwo * Lam * BStar + sqrtTwo * expo * Lam) := by
      rw [ENNReal.ofReal_add
        (mul_nonneg (mul_nonneg hSqrtTwo hLam) hBStar)
        (mul_nonneg (mul_nonneg hSqrtTwo hexpo) hLam)]
    _ = ENNReal.ofReal (sqrtTwo * Lam * (BStar + expo)) := by
      congr 1
      ring

end

end Homogenization.HighContrast.Response
