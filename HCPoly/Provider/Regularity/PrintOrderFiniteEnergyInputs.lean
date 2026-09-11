/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.MixedOrderFiniteRecurrenceCore
import HCPoly.Provider.Regularity.MultiscaleEllipticityExponentGap
import HCPoly.Provider.Regularity.OrderDecouplingBoundary

/-!
# Printed-order energy inputs for the mixed finite recurrence

The Caccioppoli, terminal-slope, and affine-error rows are assembled at the
printed order.  The remaining one-step field stays explicit in the completion
constructor, so no response-order identification is hidden in this interface.
-/

namespace Homogenization
namespace HighContrast
open MeasureTheory Book.Ch03
open scoped BigOperators ENNReal

noncomputable section

open FiniteLipschitzCoreInternal

/-- The three energy-side analytic inputs at the printed certificate order. -/
structure PrintOrderPrivateFiniteRecurrenceEnergyInputs
    (d : ℕ) [NeZero d] (g : ℝ) (a : CoeffSpace d) (abar : Mat d)
    (sourceAmplitude target kappa : ℝ) (X : CoeffSpace d → ℝ)
    (join : OrderDecoupledRoundedResponseJoin
      d g a abar sourceAmplitude target kappa X) where
  caccioppoliConstant : ℝ
  caccioppoliConstant_pos : 0 < caccioppoliConstant
  caccioppoli :
    ∀ (k : ℤ) (u : Book.Ch03.CubeSolution
        (originCube d k) join.application.aRounded) (c : ℝ) (e : Vec d),
      Transport.baseRoundedSpatialWeakError a abar join.application.hS
          (printCertificateOrder g) k ≤ 1 →
        Book.Ch03.h1EnergyNormOnCube (originCube d (k - 2))
            join.application.aRounded
            (finiteCubeSolutionRestriction join.application.aRounded
              (by omega : k - 2 ≤ k) u).toH1 ≤
          caccioppoliConstant *
            (normalizedAffineCandidateError
              (originCube d k) u.toH1.toFun c e + euclideanNorm e)
  terminalConstant : ℝ
  terminalConstant_pos : 0 < terminalConstant
  terminalSlope :
    ∀ (m : ℤ) (u : Book.Ch03.CubeSolution
        (originCube d m) join.application.aRounded),
      Transport.baseRoundedSpatialWeakError a abar join.application.hS
          (printCertificateOrder g) m ≤ 1 →
        euclideanNorm
            (finiteLipschitzBestSlope join.application.aRounded m u m) ≤
          terminalConstant *
            finiteLipschitzEnergyRow join.application.aRounded m u m
  affineErrorConstant : ℝ
  affineErrorConstant_pos : 0 < affineErrorConstant
  affineErrorEnergy :
    ∀ (m : ℤ) (u : Book.Ch03.CubeSolution
        (originCube d m) join.application.aRounded)
      (k : ℤ) (_hkm : k ≤ m),
      Transport.baseRoundedSpatialWeakError a abar join.application.hS
          (printCertificateOrder g) k ≤ 1 →
        finiteLipschitzAffineErrorRow
            join.application.aRounded m u k ≤
          affineErrorConstant *
            finiteLipschitzEnergyRow join.application.aRounded m u k

end

end HighContrast
end Homogenization
