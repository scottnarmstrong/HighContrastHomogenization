/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseShiftedCarrier
import HCPoly.Provider.Response.LoadCalibration

/-!
# Annealed energies at the shifted response loads

The canonical skew recentering changes the second load before the terminal
Schur coordinates are read.  The resulting primal and adjoint expectations
are exactly the two signed quadratic energies used by response-load
calibration, with the unit load pairing subtracted.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped Matrix

noncomputable section

/-- The primal and adjoint annealed energies at the oppositely shifted loads
are the two calibrated signed quadratic forms minus one, and are nonnegative. -/
theorem shifted_annealed_response_energies_eq_and_nonneg
    {d : ℕ} [NeZero d] {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] {qGrid : Mat d} (hq : qGrid.PosDef) {t : ℤ}
    (hint : HasFiniteAdaptedMean P qGrid t)
    {S SStar K g0 : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hg0 : IsSkewMat g0)
    (hEt : toFullBlockMat (adaptedMean P qGrid t) =
      schurBlock S SStar K) {Ehat : FullBlockMat d}
    (hEhat : Ehat = (fullBlockShear g0)ᴴ *
      toFullBlockMat (adaptedMean P qGrid t) * fullBlockShear g0)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    let p := centeredResponseLoadP S SStar K e
    let q := centeredResponseLoadQ S SStar K e
    let h := responseSkew K
    let qMinus := q + (g0 - h) *ᵥ p
    let qPlus := q + (h - g0) *ᵥ p
    let EJMinus := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew g0 hg0).coeffOn (adaptedDomain hq t)) p qMinus ∂P
    let EJPlus := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew g0 hg0).transpose.coeffOn (adaptedDomain hq t))
        p qPlus ∂P
    (EJMinus = (1 / 2 : ℝ) *
          (Sum.elim (-p) qMinus ⬝ᵥ Ehat *ᵥ Sum.elim (-p) qMinus) - 1 ∧
        0 ≤ EJMinus) ∧
      (EJPlus = (1 / 2 : ℝ) *
          (Sum.elim p qPlus ⬝ᵥ Ehat *ᵥ Sum.elim p qPlus) - 1 ∧
        0 ≤ EJPlus) := by
  dsimp only
  let r : Mat d := responseSymmetric K
  let h : Mat d := responseSkew K
  let m : Mat d := centeredResponseMetric S SStar K
  let p : Vec d := centeredResponseLoadP S SStar K e
  let q : Vec d := centeredResponseLoadQ S SStar K e
  let qMinus : Vec d := q + (g0 - h) *ᵥ p
  let qPlus : Vec d := q + (h - g0) *ᵥ p
  have hBpd : (centeredResponseBlock S SStar K).PosDef :=
    posDef_responseBlock hS hStar rfl
  have hm : m.PosDef := by
    dsimp only [m, centeredResponseMetric]
    exact posDef_matGeomMean hBpd hStar
  have hEtU : toFullBlockMat
      (annealedBlock P (adaptedDomain hq t : Set (Vec d))) =
        schurBlock S SStar K := by
    simpa only [adaptedMean, adaptedDomain_carrier] using hEt
  have hh : hᴴ = -h := by
    dsimp only [h, responseSkew]
    exact skew_half_sub K
  have hsum : h *ᵥ p + r *ᵥ p = K *ᵥ p := by
    dsimp only [h, r, responseSkew, responseSymmetric]
    rw [← Matrix.add_mulVec]
    congr 1
    module
  have hp : p = matSqrt m⁻¹ *ᵥ e := rfl
  have hqload : q = matSqrt m *ᵥ e := rfl
  have hpairMinus : p ⬝ᵥ (q - h *ᵥ p) = 1 := by
    have hneg : (-h)ᴴ = -(-h) := by rw [Matrix.conjTranspose_neg, hh]
    have hpair := dotProduct_signed_load hm hneg hp hqload he
    simpa only [Matrix.neg_mulVec, sub_eq_add_neg] using hpair
  have hpairPlus : p ⬝ᵥ (q + h *ᵥ p) = 1 :=
    dotProduct_signed_load hm hh hp hqload he
  have hpairMinusVec : vecDot p (q - h *ᵥ p) = 1 := hpairMinus
  have hpairPlusVec : vecDot p (q + h *ᵥ p) = 1 := hpairPlus
  have hminusShift : qMinus - g0 *ᵥ p = q - h *ᵥ p := by
    dsimp only [qMinus]
    rw [Matrix.sub_mulVec]
    module
  have hplusShift : qPlus + g0 *ᵥ p = q + h *ᵥ p := by
    dsimp only [qPlus]
    rw [Matrix.sub_mulVec]
    module
  have hminusSlot : q - h *ᵥ p + K *ᵥ p = q + r *ᵥ p := by
    rw [← hsum]
    abel
  have hplusSlot : q + h *ᵥ p - K *ᵥ p = q - r *ᵥ p := by
    rw [← hsum]
    abel
  have hEJMinus :
      (∫ a, responseJ (adaptedDomain hq t)
          ((a.subSkew g0 hg0).coeffOn (adaptedDomain hq t))
          p qMinus ∂P) =
        (1 / 2 : ℝ) *
            (Sum.elim (-p) qMinus ⬝ᵥ Ehat *ᵥ Sum.elim (-p) qMinus) - 1 := by
    calc
      (∫ a, responseJ (adaptedDomain hq t)
          ((a.subSkew g0 hg0).coeffOn (adaptedDomain hq t))
          p qMinus ∂P) =
          ∫ a, responseJ (adaptedDomain hq t)
            (a.coeffOn (adaptedDomain hq t)) p (q - h *ᵥ p) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with a
        rw [responseJ_subSkew]
        exact congrArg
          (responseJ (adaptedDomain hq t) (a.coeffOn (adaptedDomain hq t)) p)
          hminusShift
      _ = (1 / 2 : ℝ) * (p ⬝ᵥ S *ᵥ p) +
          (1 / 2 : ℝ) *
            ((q - h *ᵥ p + K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ
              (q - h *ᵥ p + K *ᵥ p)) -
          vecDot p (q - h *ᵥ p) :=
        annealed_responseJ_schur (adaptedDomain hq t) hint hEtU
          p (q - h *ᵥ p)
      _ = (1 / 2 : ℝ) *
            (Sum.elim (-p) qMinus ⬝ᵥ Ehat *ᵥ Sum.elim (-p) qMinus) - 1 := by
        rw [hminusSlot, hpairMinusVec]
        dsimp only [qMinus, h, r, responseSkew, responseSymmetric]
        rw [load_sq_neg hEt rfl hEhat rfl rfl]
        ring
  have hEJPlus :
      (∫ a, responseJ (adaptedDomain hq t)
          ((a.subSkew g0 hg0).transpose.coeffOn (adaptedDomain hq t))
          p qPlus ∂P) =
        (1 / 2 : ℝ) *
            (Sum.elim p qPlus ⬝ᵥ Ehat *ᵥ Sum.elim p qPlus) - 1 := by
    calc
      (∫ a, responseJ (adaptedDomain hq t)
          ((a.subSkew g0 hg0).transpose.coeffOn (adaptedDomain hq t))
          p qPlus ∂P) =
          ∫ a, responseJ (adaptedDomain hq t)
            (a.transpose.coeffOn (adaptedDomain hq t))
              p (q + h *ᵥ p) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with a
        rw [CoeffSpace.transpose_subSkew]
        rw [responseJ_subSkew (adaptedDomain hq t) a.transpose
          (-g0) (isSkewMat_neg hg0)]
        apply congrArg
          (responseJ (adaptedDomain hq t)
            (a.transpose.coeffOn (adaptedDomain hq t)) p)
        simpa only [neg_matVecMul, sub_neg_eq_add] using hplusShift
      _ = (1 / 2 : ℝ) * (p ⬝ᵥ S *ᵥ p) +
          (1 / 2 : ℝ) *
            ((q + h *ᵥ p - K *ᵥ p) ⬝ᵥ SStar⁻¹ *ᵥ
              (q + h *ᵥ p - K *ᵥ p)) -
          vecDot p (q + h *ᵥ p) :=
        annealed_adjoint_responseJ_schur (adaptedDomain hq t) hint hEtU
          p (q + h *ᵥ p)
      _ = (1 / 2 : ℝ) *
            (Sum.elim p qPlus ⬝ᵥ Ehat *ᵥ Sum.elim p qPlus) - 1 := by
        rw [hplusSlot, hpairPlusVec]
        dsimp only [qPlus, h, r, responseSkew, responseSymmetric]
        rw [load_sq_pos hEt rfl hEhat rfl rfl]
        ring
  refine ⟨⟨hEJMinus, ?_⟩, ⟨hEJPlus, ?_⟩⟩
  · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun a ↦
      Book.Ch02.responseJ_nonneg (adaptedDomain hq t)
        ((a.subSkew g0 hg0).coeffOn (adaptedDomain hq t)) p qMinus)
  · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun a ↦
      Book.Ch02.responseJ_nonneg (adaptedDomain hq t)
        ((a.subSkew g0 hg0).transpose.coeffOn (adaptedDomain hq t)) p qPlus)

end

end Homogenization.HighContrast.Response
