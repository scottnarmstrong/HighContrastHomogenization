/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.RandomAdaptedResponseCarrierBridge

/-!
# Shifted true-load response carriers

Constant-skew covariance is read at the canonical recentering shear while
the terminal response is expressed in the independent Schur skew coordinate.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal Matrix

noncomputable section

/-- The primal raw recentered carrier at the shifted load is the terminal
centered response at the Schur-skew load. -/
theorem shifted_primal_carrier_le
    {d : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {t : ℤ}
    (hint : HasFiniteAdaptedMean P q t) {g h : Mat d}
    (hg : IsSkewMat g) (p r : Vec d) {bound : ℝ≥0∞}
    (hraw :
      ENNReal.ofReal
          |(∫ a, responseJ (adaptedDomain hq t)
              ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p
                (r + (g - h) *ᵥ p) ∂P) -
            (1 / 2 : ℝ) * vecDot
              (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
                ((a.subSkew g hg).coeffOn (adaptedDomain hq t))
                (centeredResponseOptimizer (adaptedDomain hq t)
                  (a.subSkew g hg) p (r + (g - h) *ᵥ p)) i ∂P)
              (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
                ((a.subSkew g hg).coeffOn (adaptedDomain hq t))
                (centeredResponseOptimizer (adaptedDomain hq t)
                  (a.subSkew g hg) p (r + (g - h) *ᵥ p)) i ∂P)| ≤ bound) :
    ENNReal.ofReal
        |centeredResponse P (adaptedDomain hq t) p (r - h *ᵥ p)| ≤ bound := by
  have hcov := centeredResponse_subSkew (P := P) (adaptedDomain hq t)
    (by simpa only [adaptedDomain_carrier] using hint) g hg p
    (r + (g - h) *ᵥ p)
  have hload : r + (g - h) *ᵥ p - matVecMul g p = r - h *ᵥ p := by
    change r + (g - h) *ᵥ p - g *ᵥ p = r - h *ᵥ p
    rw [Matrix.sub_mulVec]
    module
  rw [hload] at hcov
  rw [← hcov]
  exact hraw

/-- The adjoint raw recentered carrier at the opposite shifted load is the
terminal centered adjoint response at the Schur-skew load. -/
theorem shifted_adjoint_carrier_le
    {d : ℕ} {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {q : Mat d} (hq : q.PosDef) {t : ℤ}
    (hint : HasFiniteAdaptedMean P q t) {g h : Mat d}
    (hg : IsSkewMat g) (p r : Vec d) {bound : ℝ≥0∞}
    (hraw :
      ENNReal.ofReal
          |(∫ a, responseJ (adaptedDomain hq t)
              ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p
                (r + (h - g) *ᵥ p) ∂P) -
            (1 / 2 : ℝ) * vecDot
              (fun i ↦ ∫ a, averageGradient (adaptedDomain hq t)
                ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t))
                (centeredAdjointOptimizer (adaptedDomain hq t)
                  (a.subSkew g hg) p (r + (h - g) *ᵥ p)) i ∂P)
              (fun i ↦ ∫ a, averageFlux (adaptedDomain hq t)
                ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t))
                (centeredAdjointOptimizer (adaptedDomain hq t)
                  (a.subSkew g hg) p (r + (h - g) *ᵥ p)) i ∂P)| ≤ bound) :
    ENNReal.ofReal
        |centeredAdjointResponse P (adaptedDomain hq t) p
          (r + h *ᵥ p)| ≤ bound := by
  have hcov := centeredAdjointResponse_subSkew (P := P) (adaptedDomain hq t)
    (by simpa only [adaptedDomain_carrier] using hint) g hg p
    (r + (h - g) *ᵥ p)
  have hload : r + (h - g) *ᵥ p + matVecMul g p = r + h *ᵥ p := by
    change r + (h - g) *ᵥ p + g *ᵥ p = r + h *ᵥ p
    rw [Matrix.sub_mulVec]
    module
  rw [hload] at hcov
  rw [← hcov]
  exact hraw

end

end Homogenization.HighContrast.Response
