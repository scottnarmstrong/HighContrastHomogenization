/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Response.ProfileEnergyCarriers
import HCPoly.Provider.Response.DiagonalWeakNormState

/-!
# Annealed centers and weak profile quantities

The primal and adjoint centers are formed independently by averaging the two
slots of their terminal optimizer states.  The weak quantities use the
concrete scale-average seminorm, and the centering variances use the diagonal
metric quadratic form.  A coefficient transformation is kept explicit so the
same carriers apply to a fixed skew recentering without changing the ambient
probability space.
-/

namespace Homogenization.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The separately annealed primal optimizer center. -/
def profilePrimalCenter (P : Measure (CoeffSpace d)) {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (sample : CoeffSpace d → CoeffSpace d)
    (p r : Vec d) : BlockVec d :=
  ((fun i ↦ ∫ a, (blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (sample a) p r)).1 i ∂P),
    fun i ↦ ∫ a, (blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (sample a) p r)).2 i ∂P)

/-- The separately annealed coefficient-transpose optimizer center. -/
def profileAdjointCenter (P : Measure (CoeffSpace d)) {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (sample : CoeffSpace d → CoeffSpace d)
    (p r : Vec d) : BlockVec d :=
  ((fun i ↦ ∫ a, (blockCellAverage (adaptedCell q t)
      (diagonalWeakAdjointState hq t (sample a) p r)).1 i ∂P),
    fun i ↦ ∫ a, (blockCellAverage (adaptedCell q t)
      (diagonalWeakAdjointState hq t (sample a) p r)).2 i ∂P)

/-- The normalized primal weak seminorm of one coefficient sample. -/
def profilePrimalWeakRoot (m0 : Mat d) {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (center : BlockVec d) (a : CoeffSpace d) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
    adaptedWeakSeminorm q t (1 / 2) (fun x ↦
      blockMatVecMul (blockDiag (matSqrt m0) (matSqrt m0)⁻¹)
        (diagonalWeakState hq t (sample a) p r x - center))

/-- The normalized adjoint weak seminorm of one coefficient sample. -/
def profileAdjointWeakRoot (m0 : Mat d) {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (center : BlockVec d) (a : CoeffSpace d) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (t : ℝ))) *
    adaptedWeakSeminorm q t (1 / 2) (fun x ↦
      blockMatVecMul (blockDiag (matSqrt m0) (matSqrt m0)⁻¹)
        (diagonalWeakAdjointState hq t (sample a) p r x - center))

/-- The primal weak quantity is the square of the normalized `L²` seminorm. -/
def profilePrimalWeakQuantity (P : Measure (CoeffSpace d)) (m0 : Mat d)
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) : ℝ≥0∞ :=
  eLpNorm (profilePrimalWeakRoot m0 hq t sample p r
    (profilePrimalCenter P hq t sample p r)) 2 P ^ (2 : ℕ)

/-- The defining equation of the primal weak quantity. -/
theorem profilePrimalWeakQuantity_eq (P : Measure (CoeffSpace d))
    (m0 : Mat d) {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) :
    profilePrimalWeakQuantity P m0 hq t sample p r =
      eLpNorm (profilePrimalWeakRoot m0 hq t sample p r
        (profilePrimalCenter P hq t sample p r)) 2 P ^ (2 : ℕ) := rfl

/-- The adjoint weak quantity is the square of its normalized `L²` seminorm. -/
def profileAdjointWeakQuantity (P : Measure (CoeffSpace d)) (m0 : Mat d)
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) : ℝ≥0∞ :=
  eLpNorm (profileAdjointWeakRoot m0 hq t sample p r
    (profileAdjointCenter P hq t sample p r)) 2 P ^ (2 : ℕ)

/-- The defining equation of the adjoint weak quantity. -/
theorem profileAdjointWeakQuantity_eq (P : Measure (CoeffSpace d))
    (m0 : Mat d) {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) :
    profileAdjointWeakQuantity P m0 hq t sample p r =
      eLpNorm (profileAdjointWeakRoot m0 hq t sample p r
        (profileAdjointCenter P hq t sample p r)) 2 P ^ (2 : ℕ) := rfl

/-- The primal centering variance in the canonical diagonal metric. -/
def profilePrimalCenterVariance (P : Measure (CoeffSpace d)) (m0 : Mat d)
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) : ℝ≥0∞ :=
  eLpNorm (fun a ↦ ENNReal.ofReal (Real.sqrt (metricBlockNormSq m0
    (blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (sample a) p r) -
        profilePrimalCenter P hq t sample p r)))) 2 P

/-- The adjoint centering variance in the canonical diagonal metric. -/
def profileAdjointCenterVariance (P : Measure (CoeffSpace d)) (m0 : Mat d)
    {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d) : ℝ≥0∞ :=
  eLpNorm (fun a ↦ ENNReal.ofReal (Real.sqrt (metricBlockNormSq m0
    (blockCellAverage (adaptedCell q t)
      (diagonalWeakAdjointState hq t (sample a) p r) -
        profileAdjointCenter P hq t sample p r)))) 2 P

end

end Homogenization.HighContrast.Response
