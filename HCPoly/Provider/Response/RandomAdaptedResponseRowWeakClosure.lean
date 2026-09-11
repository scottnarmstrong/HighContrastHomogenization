/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.LoadCalibrationClosure
import HCPoly.Provider.Response.ProfileResponseAssembly
import HCPoly.Provider.Response.RandomAdaptedResponseCalibrationScalar
import HCPoly.Provider.Response.RandomAdaptedResponseCarrierBridge
import HCPoly.Provider.Response.RandomAdaptedResponseProfileScalar
import HCPoly.Provider.Response.RandomAdaptedResponseScalarClosure

/-!
# Row and weak scalar closure

The profile row estimate is composed with its calibrated quadratic load, and
the weak-root estimate is squared without leaving the extended-nonnegative
carrier.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal Matrix MatrixOrder

noncomputable section

/-- Flattening a block-vector pair is the corresponding sum-eliminator. -/
theorem to_full_block_vec_pair_row_weak
    {d : ℕ} (P Q : Vec d) :
    toFullBlockVec ((P, Q) : BlockVec d) = Sum.elim P Q := by
  funext i
  cases i <;> rfl

/-- Flattening an arbitrary block vector is elimination by its components. -/
theorem to_full_block_vec_eq_sum_elim_row_weak
    {d : ℕ} (X : BlockVec d) :
    toFullBlockVec X = Sum.elim X.1 X.2 := by
  cases X with
  | mk P Q => exact to_full_block_vec_pair_row_weak P Q

/-- The paper adjoint sign negates only the first center component. -/
theorem paper_adjoint_sign_apply_row_weak
    {d : ℕ} (X : BlockVec d) :
    blockMatVecMul (blockDiag (-1) 1) X = (-X.1, X.2) := by
  apply Prod.ext
  · change matVecMul (-1) X.1 + matVecMul 0 X.2 = -X.1
    rw [zero_matVecMul, add_zero, neg_matVecMul, matVecMul_one]
  · change matVecMul 0 X.1 + matVecMul 1 X.2 = X.2
    rw [zero_matVecMul, zero_add, matVecMul_one]

/-- Negating the first component does not change its quadratic energy in the
canonical block-diagonal metric. -/
theorem metric_center_fst_neg_eq
    {d : ℕ} {m0 : Mat d} {M0 : FullBlockMat d}
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹) (P Q : Vec d) :
    Sum.elim (-P) Q ⬝ᵥ M0 *ᵥ Sum.elim (-P) Q =
      Sum.elim P Q ⬝ᵥ M0 *ᵥ Sum.elim P Q := by
  rw [hM0, quadratic_fromBlocks_diag, quadratic_fromBlocks_diag]
  simp only [dotProduct_neg, Matrix.mulVec_neg, neg_dotProduct, neg_neg]

/-- The independently annealed primal center satisfies the calibrated metric
bound at the canonical gauge. -/
theorem primal_center_metric_le_of_calibration
    {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {q : Mat d} (hq : q.PosDef) {t : ℤ}
    (hint : HasFiniteAdaptedMean P q t) {h0 : Mat d} (hh0 : IsSkewMat h0)
    (p r : Vec d) {m0 : Mat d} {M0 Ehat : FullBlockMat d}
    {beta kappa theta : ℝ} (hm0 : m0.PosDef)
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹)
    (hEhat : Ehat = toFullBlockMat (skewBlockCongr h0 (adaptedMean P q t)))
    (hEhatPd : Ehat.PosDef) (hbeta : 0 < beta) (hkappa : 0 < kappa)
    (hlow : beta⁻¹ • M0 ≤ Ehat)
    (hup : Ehat ≤ (beta * Real.sqrt kappa) • M0)
    (hx : Sum.elim (-p) r ⬝ᵥ Ehat *ᵥ Sum.elim (-p) r ≤
      4 * Real.sqrt theta) :
    let center := profilePrimalCenter P hq t
      (fun a ↦ a.subSkew h0 hh0) p r
    Sum.elim center.1 center.2 ⬝ᵥ M0 *ᵥ Sum.elim center.1 center.2 ≤
      8 * beta * (Real.sqrt kappa + 1) * Real.sqrt theta := by
  dsimp only
  apply metric_center_le hm0 hM0 hEhatPd hbeta hkappa hlow hup
    (x := Sum.elim (-p) r)
  · rw [← to_full_block_vec_eq_sum_elim_row_weak
      (profilePrimalCenter P hq t (fun a ↦ a.subSkew h0 hh0) p r)]
    simpa only [hEhat, to_full_block_vec_pair_row_weak] using
      (toFullBlockVec_profilePrimalCenter_subSkew_eq hq t hint h0 hh0 p r)
  · exact hx

/-- The independently annealed adjoint center satisfies the same calibrated
metric bound; the paper sign is removed only in the block-diagonal metric. -/
theorem adjoint_center_metric_le_of_calibration
    {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {q : Mat d} (hq : q.PosDef) {t : ℤ}
    (hint : HasFiniteAdaptedMean P q t) {h0 : Mat d} (hh0 : IsSkewMat h0)
    (p r : Vec d) {m0 : Mat d} {M0 Ehat : FullBlockMat d}
    {beta kappa theta : ℝ} (hm0 : m0.PosDef)
    (hM0 : M0 = Matrix.fromBlocks m0 0 0 m0⁻¹)
    (hEhat : Ehat = toFullBlockMat (skewBlockCongr h0 (adaptedMean P q t)))
    (hEhatPd : Ehat.PosDef) (hbeta : 0 < beta) (hkappa : 0 < kappa)
    (hlow : beta⁻¹ • M0 ≤ Ehat)
    (hup : Ehat ≤ (beta * Real.sqrt kappa) • M0)
    (hx : Sum.elim p r ⬝ᵥ Ehat *ᵥ Sum.elim p r ≤
      4 * Real.sqrt theta) :
    let center := profileAdjointCenter P hq t
      (fun a ↦ a.subSkew h0 hh0) p r
    Sum.elim center.1 center.2 ⬝ᵥ M0 *ᵥ Sum.elim center.1 center.2 ≤
      8 * beta * (Real.sqrt kappa + 1) * Real.sqrt theta := by
  dsimp only
  have hsigned := metric_center_le_sub hm0 hM0 hEhatPd hbeta hkappa hlow hup
    (x := Sum.elim p r)
    (Y := toFullBlockVec (blockMatVecMul (blockDiag (-1) 1)
      (profileAdjointCenter P hq t (fun a ↦ a.subSkew h0 hh0) p r)))
    (by simpa only [hEhat, to_full_block_vec_pair_row_weak] using
      (toFullBlockVec_profileAdjointCenter_subSkew_eq hq t hint h0 hh0 p r))
    hx
  rw [paper_adjoint_sign_apply_row_weak,
    to_full_block_vec_pair_row_weak] at hsigned
  rw [← metric_center_fst_neg_eq hM0]
  exact hsigned

/-- A profile row bound and its calibrated quadratic load give the literal
response-window row scale. -/
theorem hatted_row_le_l_star_of_profile
    {row : ℝ≥0∞}
    {Gamma Q ceps beta kappaT kappaS theta Rhalf chi
      GammaStar cepsStar betaStar LStar : ℝ}
    (hGamma0 : 0 ≤ Gamma) (hceps0 : 0 ≤ ceps) (hbeta0 : 0 ≤ beta)
    (hRhalf : 1 ≤ Rhalf) (hkappa : 1 ≤ kappaS)
    (hGamma : Gamma ≤ GammaStar) (hceps : ceps ≤ cepsStar)
    (hbeta : beta ≤ betaStar)
    (hkappaRoot : Real.sqrt kappaT ≤ Rhalf * Real.sqrt kappaS)
    (htheta : Real.sqrt theta ≤ chi * Real.sqrt kappaS)
    (hprofile : row ≤ ENNReal.ofReal (2 * Gamma * Q))
    (hQ : Q ≤ 8 * ceps * beta * Real.sqrt kappaS *
      (Real.sqrt kappaT + 1) * Real.sqrt theta)
    (hLStar : LStar =
      32 * GammaStar * cepsStar * betaStar * Rhalf * chi) :
    row ≤ ENNReal.ofReal (LStar * kappaS ^ (3 / 2 : ℝ)) := by
  have hrow : row ≤ ENNReal.ofReal
      (16 * Gamma * ceps * beta * Real.sqrt kappaS *
        (Real.sqrt kappaT + 1) * Real.sqrt theta) := by
    exact hprofile.trans (ENNReal.ofReal_le_ofReal
      (row_from_profile hGamma0 le_rfl hQ))
  exact row_le_l_star hGamma0 hceps0 hbeta0 hRhalf hkappa hGamma hceps
    hbeta hkappaRoot htheta hrow hLStar

/-- Raw terminal metric, load, and energy-load bounds imply the two products
used by the weak profile at the earlier imbalance scale. -/
theorem calibrated_load_products_of_raw
    {d : ℕ} {K Len Lam beta betaStar kappaT kappaS R chi
      KStar LenStar LambdaStar : ℝ}
    (hchi0 : 0 ≤ chi) (hkappaT0 : 0 ≤ kappaT)
    (hkappaS : 1 ≤ kappaS) (hR0 : 0 ≤ R)
    (hbeta : beta ≤ betaStar)
    (hkappa : kappaT ≤ R ^ (d : ℝ) * kappaS)
    {theta : ℝ} (htheta : Real.sqrt theta ≤ chi * Real.sqrt kappaS)
    (hKraw : K ≤ Real.sqrt beta * Real.sqrt (Real.sqrt kappaT))
    (hLenRaw : Len ≤ 2 * Real.sqrt (Real.sqrt theta))
    (hLamRaw : Lam ≤ Real.sqrt 5 * Real.sqrt (Real.sqrt theta))
    (hKStar : KStar = Real.sqrt betaStar * R ^ ((d : ℝ) / 4))
    (hLenStar : LenStar = 2 * Real.sqrt chi)
    (hLambdaStar : LambdaStar = Real.sqrt 5 * Real.sqrt chi)
    (hLen0 : 0 ≤ Len) (hLam0 : 0 ≤ Lam) :
    K * Len ≤ KStar * LenStar * Real.sqrt kappaS ∧
      K * Lam ≤ KStar * LambdaStar * Real.sqrt kappaS := by
  have hkappaS0 : 0 ≤ kappaS := zero_le_one.trans hkappaS
  have hsqrtBeta : Real.sqrt beta ≤ Real.sqrt betaStar :=
    Real.sqrt_le_sqrt hbeta
  have hkappaQuarter : kappaT ^ (1 / 4 : ℝ) ≤
      R ^ ((d : ℝ) / 4) * kappaS ^ (1 / 4 : ℝ) :=
    quarter_power_comparison_le hkappaT0 hkappaS0 hR0 hkappa
  have hK : K ≤ KStar * kappaS ^ (1 / 4 : ℝ) := by
    calc
      K ≤ Real.sqrt beta * Real.sqrt (Real.sqrt kappaT) := hKraw
      _ = Real.sqrt beta * kappaT ^ (1 / 4 : ℝ) := by
        rw [sqrt_sqrt_eq_quarter_power hkappaT0]
      _ ≤ Real.sqrt betaStar *
          (R ^ ((d : ℝ) / 4) * kappaS ^ (1 / 4 : ℝ)) := by gcongr
      _ = KStar * kappaS ^ (1 / 4 : ℝ) := by rw [hKStar]; ring
  have hthetaQuarter : Real.sqrt (Real.sqrt theta) ≤
      Real.sqrt chi * kappaS ^ (1 / 4 : ℝ) := by
    calc
      Real.sqrt (Real.sqrt theta) ≤
          Real.sqrt (chi * Real.sqrt kappaS) := Real.sqrt_le_sqrt htheta
      _ = Real.sqrt chi * Real.sqrt (Real.sqrt kappaS) := by
        rw [Real.sqrt_mul hchi0]
      _ = Real.sqrt chi * kappaS ^ (1 / 4 : ℝ) := by
        rw [sqrt_sqrt_eq_quarter_power hkappaS0]
  have hLen : Len ≤ LenStar * kappaS ^ (1 / 4 : ℝ) := by
    calc
      Len ≤ 2 * Real.sqrt (Real.sqrt theta) := hLenRaw
      _ ≤ 2 * (Real.sqrt chi * kappaS ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hthetaQuarter (by norm_num)
      _ = LenStar * kappaS ^ (1 / 4 : ℝ) := by rw [hLenStar]; ring
  have hLam : Lam ≤ LambdaStar * kappaS ^ (1 / 4 : ℝ) := by
    calc
      Lam ≤ Real.sqrt 5 * Real.sqrt (Real.sqrt theta) := hLamRaw
      _ ≤ Real.sqrt 5 *
          (Real.sqrt chi * kappaS ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hthetaQuarter (Real.sqrt_nonneg 5)
      _ = LambdaStar * kappaS ^ (1 / 4 : ℝ) := by
        rw [hLambdaStar]
        ring
  exact load_product_bounds (by rw [hKStar]; positivity) hkappaS0 hK hLen
    hLam hLen0 hLam0

/-- A weak-root response-window bound closes the squared weak quantity while
retaining the `ENNReal` carrier. -/
theorem weak_quantity_le_rstar_sq
    {W N : ℝ≥0∞} {RStar kappa : ℝ}
    (hW : W = N ^ (2 : ℕ)) (hRStar : 0 ≤ RStar)
    (hkappa : 0 ≤ kappa)
    (hroot : N ≤ ENNReal.ofReal (RStar * Real.sqrt kappa)) :
    W ≤ ENNReal.ofReal (RStar ^ 2 * kappa) :=
  weak_quantity_le_of_root_bound hW hRStar hkappa hroot

/-- The complete retained profile chain gives the response-window weak-root
bound.  All history and weak quantities remain extended nonnegative. -/
theorem weak_root_le_rstar_of_profile
    {N cell average bad good center centeredRoot nonlinearRoot
      nonlinearHalf : ℝ≥0∞}
    {Cprof Cresp K Len Lam KStar LenStar LambdaStar sqrtTwo alpha cconst
      Scen Scell Sav etaRoot etaHalf BStar expo UStar RStar kappa : ℝ}
    (hCprofResp : Cprof ≤ Cresp)
    (hCresp : 0 ≤ Cresp) (hK : 0 ≤ K) (hLen : 0 ≤ Len)
    (hLam : 0 ≤ Lam) (hKStar : 0 ≤ KStar)
    (hLenStar : 0 ≤ LenStar) (hLambdaStar : 0 ≤ LambdaStar)
    (hSqrtTwo : 0 ≤ sqrtTwo) (halpha : 0 < alpha)
    (hcconst : 0 ≤ cconst) (hScen : 0 ≤ Scen)
    (hScell : 0 ≤ Scell) (hSav : 0 ≤ Sav)
    (hetaRoot : 0 ≤ etaRoot) (hetaHalf : 0 ≤ etaHalf)
    (hBStar : 0 ≤ BStar) (hexpo : 0 ≤ expo)
    (hKL : K * Len ≤ KStar * LenStar * Real.sqrt kappa)
    (hKLam : K * Lam ≤ KStar * LambdaStar * Real.sqrt kappa)
    (hcell : cell ≤ ENNReal.ofReal Scen * centeredRoot +
      ENNReal.ofReal Scell * nonlinearRoot)
    (haverage : average ≤ ENNReal.ofReal Sav * nonlinearHalf)
    (hcenteredRoot : centeredRoot ≤ ENNReal.ofReal etaRoot)
    (hnonlinearRoot : nonlinearRoot ≤ ENNReal.ofReal etaRoot)
    (hnonlinearHalf : nonlinearHalf ≤ ENNReal.ofReal etaHalf)
    (hbad : bad ≤ ENNReal.ofReal (sqrtTwo * Lam * BStar))
    (hgood : good ≤ ENNReal.ofReal (sqrtTwo * expo * Lam))
    (hcenter : center ≤ ENNReal.ofReal (K * Len) * centeredRoot)
    (hN : N ≤ ENNReal.ofReal (Cprof * K * Len) * (cell + average) +
      ENNReal.ofReal (Cprof * K / (2 * alpha)) * (bad + good) +
      ENNReal.ofReal cconst * center)
    (hUStar : UStar = (Scen + Scell) * etaRoot + Sav * etaHalf)
    (hRStar : RStar = Cresp * KStar * LenStar * UStar +
      Cresp * KStar * sqrtTwo * LambdaStar / (2 * alpha) *
        (BStar + expo) + cconst * KStar * LenStar * etaRoot) :
    N ≤ ENNReal.ofReal (RStar * Real.sqrt kappa) := by
  have hU : cell + average ≤ ENNReal.ofReal UStar :=
    recent_profile_le_ustar hScen hScell hSav hetaRoot hetaHalf hcell
      haverage hcenteredRoot hnonlinearRoot hnonlinearHalf hUStar
  have henergy : bad + good ≤
      ENNReal.ofReal (sqrtTwo * Lam * (BStar + expo)) :=
    energy_sum_le hSqrtTwo hLam hBStar hexpo hbad hgood
  have hcenter' : center ≤ ENNReal.ofReal (K * Len * etaRoot) := by
    calc
      center ≤ ENNReal.ofReal (K * Len) * centeredRoot := hcenter
      _ ≤ ENNReal.ofReal (K * Len) * ENNReal.ofReal etaRoot := by gcongr
      _ = ENNReal.ofReal (K * Len * etaRoot) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hK hLen)]
  have hN' : N ≤ ENNReal.ofReal (Cresp * K * Len) * (cell + average) +
      ENNReal.ofReal (Cresp * K / (2 * alpha)) * (bad + good) +
      ENNReal.ofReal cconst * center :=
    hN.trans (profile_weak_rhs_mono hCprofResp hK hLen halpha
      (cell + average) (bad + good) (ENNReal.ofReal cconst * center))
  have hUStar0 : 0 ≤ UStar := by
    rw [hUStar]
    exact add_nonneg
      (mul_nonneg (add_nonneg hScen hScell) hetaRoot)
      (mul_nonneg hSav hetaHalf)
  exact weak_root_le_rstar hCresp hK hLen hKStar hLenStar hLambdaStar
    hSqrtTwo halpha hcconst hUStar0 hBStar hexpo hetaRoot hKL hKLam
    hU henergy hcenter' hN' hRStar

/-- The complete profile chain closes the literal squared weak quantity. -/
theorem weak_quantity_le_rstar_sq_of_profile
    {W N cell average bad good center centeredRoot nonlinearRoot
      nonlinearHalf : ℝ≥0∞}
    {Cprof Cresp K Len Lam KStar LenStar LambdaStar sqrtTwo alpha cconst
      Scen Scell Sav etaRoot etaHalf BStar expo UStar RStar kappa : ℝ}
    (hW : W = N ^ (2 : ℕ)) (hRStar0 : 0 ≤ RStar) (hkappa0 : 0 ≤ kappa)
    (hCprofResp : Cprof ≤ Cresp)
    (hCresp : 0 ≤ Cresp) (hK : 0 ≤ K) (hLen : 0 ≤ Len)
    (hLam : 0 ≤ Lam) (hKStar : 0 ≤ KStar)
    (hLenStar : 0 ≤ LenStar) (hLambdaStar : 0 ≤ LambdaStar)
    (hSqrtTwo : 0 ≤ sqrtTwo) (halpha : 0 < alpha)
    (hcconst : 0 ≤ cconst) (hScen : 0 ≤ Scen)
    (hScell : 0 ≤ Scell) (hSav : 0 ≤ Sav)
    (hetaRoot : 0 ≤ etaRoot) (hetaHalf : 0 ≤ etaHalf)
    (hBStar : 0 ≤ BStar) (hexpo : 0 ≤ expo)
    (hKL : K * Len ≤ KStar * LenStar * Real.sqrt kappa)
    (hKLam : K * Lam ≤ KStar * LambdaStar * Real.sqrt kappa)
    (hcell : cell ≤ ENNReal.ofReal Scen * centeredRoot +
      ENNReal.ofReal Scell * nonlinearRoot)
    (haverage : average ≤ ENNReal.ofReal Sav * nonlinearHalf)
    (hcenteredRoot : centeredRoot ≤ ENNReal.ofReal etaRoot)
    (hnonlinearRoot : nonlinearRoot ≤ ENNReal.ofReal etaRoot)
    (hnonlinearHalf : nonlinearHalf ≤ ENNReal.ofReal etaHalf)
    (hbad : bad ≤ ENNReal.ofReal (sqrtTwo * Lam * BStar))
    (hgood : good ≤ ENNReal.ofReal (sqrtTwo * expo * Lam))
    (hcenter : center ≤ ENNReal.ofReal (K * Len) * centeredRoot)
    (hN : N ≤ ENNReal.ofReal (Cprof * K * Len) * (cell + average) +
      ENNReal.ofReal (Cprof * K / (2 * alpha)) * (bad + good) +
      ENNReal.ofReal cconst * center)
    (hUStar : UStar = (Scen + Scell) * etaRoot + Sav * etaHalf)
    (hRStar : RStar = Cresp * KStar * LenStar * UStar +
      Cresp * KStar * sqrtTwo * LambdaStar / (2 * alpha) *
        (BStar + expo) + cconst * KStar * LenStar * etaRoot) :
    W ≤ ENNReal.ofReal (RStar ^ 2 * kappa) := by
  apply weak_quantity_le_rstar_sq hW hRStar0 hkappa0
  exact weak_root_le_rstar_of_profile hCprofResp hCresp hK hLen hLam hKStar
    hLenStar hLambdaStar hSqrtTwo halpha hcconst hScen hScell hSav
    hetaRoot hetaHalf hBStar hexpo hKL hKLam hcell haverage hcenteredRoot
    hnonlinearRoot hnonlinearHalf hbad hgood hcenter hN hUStar hRStar

end

end Homogenization.HighContrast.Response
