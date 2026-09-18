/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseCompactInsertion
import HCPoly.Provider.Transport.WindowBelowStart
import HCPoly.Provider.Transport.WindowCenteredBound
import HCPoly.Provider.Response.ProfileEnergyLp
import HCPoly.Provider.Response.ConstantSkewProfiles
import HCPoly.Provider.Response.ProfileSkewMeasurability
import HCPoly.Provider.Response.ProfileDefectHistory
import HCPoly.Provider.Response.ProfileRowSkewCarriers
import HCPoly.Provider.Response.ProfileMismatch
import HCPoly.Provider.Response.LoadCalibrationProfile
import HCPoly.Provider.Response.ProfileCenterIdentities
import HCPoly.Provider.Response.ProfileRowCarriers

/-!
# True response-load carrier bridges

Constant-skew covariance identifies the two terminal centered calls, while
flattening the two block coordinates exposes the row load used by calibration.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal Matrix MatrixOrder

noncomputable section

/-- At the true Schur load, the recentered primal integral is the centered
response used by the terminal supremum. -/
theorem true_load_centered_response_eq
    {d : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) {S SStar K : Mat d} (e : Vec d) :
    let h0 := responseSkew K
    let p := centeredResponseLoadP S SStar K e
    let r := centeredResponseLoadQ S SStar K e
    (∫ a, responseJ (adaptedDomain hq t)
          ((a.subSkew h0 (is_skew_mat_response_skew K)).coeffOn
            (adaptedDomain hq t)) p r ∂P) -
        (1 / 2 : ℝ) *
          vecDot
            (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
              ((a.subSkew h0 (is_skew_mat_response_skew K)).coeffOn
                (adaptedDomain hq t))
              (centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew h0 (is_skew_mat_response_skew K)) p r) i ∂P)
            (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
              ((a.subSkew h0 (is_skew_mat_response_skew K)).coeffOn
                (adaptedDomain hq t))
              (centeredResponseOptimizer (adaptedDomain hq t)
                (a.subSkew h0 (is_skew_mat_response_skew K)) p r) i ∂P) =
      centeredResponse P (adaptedDomain hq t) p
        (r - responseSkew K *ᵥ p) := by
  dsimp only
  exact centeredResponse_subSkew (adaptedDomain hq t)
    (by simpa only [adaptedDomain_carrier] using! hint)
    (responseSkew K) (is_skew_mat_response_skew K)
    (centeredResponseLoadP S SStar K e)
    (centeredResponseLoadQ S SStar K e)

/-- At the same true load, the independently recentered adjoint integral is
the centered adjoint response with the opposite load correction. -/
theorem true_load_centered_adjoint_response_eq
    {d : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (hint : HasFiniteAdaptedMean P q t) {S SStar K : Mat d} (e : Vec d) :
    let h0 := responseSkew K
    let p := centeredResponseLoadP S SStar K e
    let r := centeredResponseLoadQ S SStar K e
    (∫ a, responseJ (adaptedDomain hq t)
          ((a.subSkew h0 (is_skew_mat_response_skew K)).transpose.coeffOn
            (adaptedDomain hq t)) p r ∂P) -
        (1 / 2 : ℝ) *
          vecDot
            (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
              ((a.subSkew h0
                (is_skew_mat_response_skew K)).transpose.coeffOn
                  (adaptedDomain hq t))
              (centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew h0 (is_skew_mat_response_skew K)) p r) i ∂P)
            (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
              ((a.subSkew h0
                (is_skew_mat_response_skew K)).transpose.coeffOn
                  (adaptedDomain hq t))
              (centeredAdjointOptimizer (adaptedDomain hq t)
                (a.subSkew h0 (is_skew_mat_response_skew K)) p r) i ∂P) =
      centeredAdjointResponse P (adaptedDomain hq t) p
        (r + responseSkew K *ᵥ p) := by
  dsimp only
  exact centeredAdjointResponse_subSkew (adaptedDomain hq t)
    (by simpa only [adaptedDomain_carrier] using! hint)
    (responseSkew K) (is_skew_mat_response_skew K)
    (centeredResponseLoadP S SStar K e)
    (centeredResponseLoadQ S SStar K e)

/-- The carried primal compact estimate at one Schur load rewrites to the
literal endgame premise without changing any row or weak carrier. -/
theorem true_carrier_compact_minus
    {d : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) {s t : ℤ}
    (hint : HasFiniteAdaptedMean P q t) {S SStar K : Mat d}
    (e : Vec d) {C expo : ℝ}
    (hE6 :
      let h0 := responseSkew K
      let hh0 := is_skew_mat_response_skew K
      let p := centeredResponseLoadP S SStar K e
      let r := centeredResponseLoadQ S SStar K e
      let center := profilePrimalCenter P hq t
        (fun a ↦ a.subSkew h0 hh0) p r
      let tau := profilePrimalResponseDefect P hq h0 hh0 s t p r
      let EJ := ∫ a, responseJ (adaptedDomain hq t)
        ((a.subSkew h0 hh0).coeffOn (adaptedDomain hq t)) p r ∂P
      let row := profilePrimalHattedEarlierRow P q h0 s center.1 center.2
      let weak := profilePrimalWeakQuantity P m0 hq t
        (fun a ↦ a.subSkew h0 hh0) p r
      let Jtilde := EJ - (1 / 2 : ℝ) *
        vecDot
          (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
            ((a.subSkew h0 hh0).coeffOn (adaptedDomain hq t))
            (centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew h0 hh0) p r) i ∂P)
          (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
            ((a.subSkew h0 hh0).coeffOn (adaptedDomain hq t))
            (centeredResponseOptimizer (adaptedDomain hq t)
              (a.subSkew h0 hh0) p r) i ∂P)
      ENNReal.ofReal |Jtilde| ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt tau) *
          (ENNReal.ofReal (Real.sqrt tau) +
            ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * ENNReal.ofReal expo *
          ENNReal.ofReal (Real.sqrt EJ) *
            (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * weak) :
    let h0 := responseSkew K
    let hh0 := is_skew_mat_response_skew K
    let p := centeredResponseLoadP S SStar K e
    let r := centeredResponseLoadQ S SStar K e
    let center := profilePrimalCenter P hq t
      (fun a ↦ a.subSkew h0 hh0) p r
    let tau := profilePrimalResponseDefect P hq h0 hh0 s t p r
    let EJ := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew h0 hh0).coeffOn (adaptedDomain hq t)) p r ∂P
    let row := profilePrimalHattedEarlierRow P q h0 s center.1 center.2
    let weak := profilePrimalWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew h0 hh0) p r
    ENNReal.ofReal
        |centeredResponse P (adaptedDomain hq t) p (r - h0 *ᵥ p)| ≤
      ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt tau) *
        (ENNReal.ofReal (Real.sqrt tau) +
          ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * ENNReal.ofReal expo *
        ENNReal.ofReal (Real.sqrt EJ) *
          (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * weak := by
  dsimp only
  rw [← true_load_centered_response_eq hq t hint
    (S := S) (SStar := SStar) (K := K) e]
  exact hE6

/-- The carried adjoint compact estimate rewrites with the adjoint defect,
center-component row, and weak quantity unchanged. -/
theorem true_carrier_compact_plus
    {d : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q m0 : Mat d} (hq : q.PosDef) {s t : ℤ}
    (hint : HasFiniteAdaptedMean P q t) {S SStar K : Mat d}
    (e : Vec d) {C expo : ℝ}
    (hE6 :
      let h0 := responseSkew K
      let hh0 := is_skew_mat_response_skew K
      let p := centeredResponseLoadP S SStar K e
      let r := centeredResponseLoadQ S SStar K e
      let center := profileAdjointCenter P hq t
        (fun a ↦ a.subSkew h0 hh0) p r
      let tau := profileAdjointResponseDefect P hq h0 hh0 s t p r
      let EJ := ∫ a, responseJ (adaptedDomain hq t)
        ((a.subSkew h0 hh0).transpose.coeffOn
          (adaptedDomain hq t)) p r ∂P
      let row := profileAdjointHattedEarlierRow P q h0 s center.1 center.2
      let weak := profileAdjointWeakQuantity P m0 hq t
        (fun a ↦ a.subSkew h0 hh0) p r
      let Jtilde := EJ - (1 / 2 : ℝ) *
        vecDot
          (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
            ((a.subSkew h0 hh0).transpose.coeffOn
              (adaptedDomain hq t))
            (centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew h0 hh0) p r) i ∂P)
          (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
            ((a.subSkew h0 hh0).transpose.coeffOn
              (adaptedDomain hq t))
            (centeredAdjointOptimizer (adaptedDomain hq t)
              (a.subSkew h0 hh0) p r) i ∂P)
      ENNReal.ofReal |Jtilde| ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt tau) *
          (ENNReal.ofReal (Real.sqrt tau) +
            ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * ENNReal.ofReal expo *
          ENNReal.ofReal (Real.sqrt EJ) *
            (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
        ENNReal.ofReal C * weak) :
    let h0 := responseSkew K
    let hh0 := is_skew_mat_response_skew K
    let p := centeredResponseLoadP S SStar K e
    let r := centeredResponseLoadQ S SStar K e
    let center := profileAdjointCenter P hq t
      (fun a ↦ a.subSkew h0 hh0) p r
    let tau := profileAdjointResponseDefect P hq h0 hh0 s t p r
    let EJ := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew h0 hh0).transpose.coeffOn
        (adaptedDomain hq t)) p r ∂P
    let row := profileAdjointHattedEarlierRow P q h0 s center.1 center.2
    let weak := profileAdjointWeakQuantity P m0 hq t
      (fun a ↦ a.subSkew h0 hh0) p r
    ENNReal.ofReal
        |centeredAdjointResponse P (adaptedDomain hq t) p
          (r + h0 *ᵥ p)| ≤
      ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt tau) *
        (ENNReal.ofReal (Real.sqrt tau) +
          ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * ENNReal.ofReal expo *
        ENNReal.ofReal (Real.sqrt EJ) *
          (ENNReal.ofReal (Real.sqrt EJ) + row ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal C * weak := by
  dsimp only
  rw [← true_load_centered_adjoint_response_eq hq t hint
    (S := S) (SStar := SStar) (K := K) e]
  exact hE6

/-- Coefficient transposition preserves the quadratic row load before the
adjoint center components are inserted. -/
theorem hatted_adjoint_quadratic_load_eq
    {d : ℕ} (h : Mat d) (E : BlockMat d) (Pcen Qcen : Vec d) :
    profileQuadraticLoad (profileHattedAdjointBlock h E) Pcen Qcen =
      profileQuadraticLoad (profileHattedBlock h E) Pcen Qcen := by
  rw [profileHattedAdjointBlock, profileQuadraticLoad_adjointBlock]

end

end Homogenization.HighContrast.Response
