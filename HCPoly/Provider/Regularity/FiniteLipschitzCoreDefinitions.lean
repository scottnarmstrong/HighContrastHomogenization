/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.FiniteLipschitzCoreBase

/-!
# Public finite centered-cube energy and best-fit objects

This module exposes the finite centered-cube energy and canonical affine
best-fit quantities used by both regularity branches.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory Book.Ch03
open scoped BigOperators ENNReal

noncomputable section

open FiniteLipschitzCoreInternal

/-- The normalized energy of the solution restricted to a centered cube. -/
noncomputable def finiteCenteredCubeSolutionEnergy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a) (k : ℤ) : ℝ :=
  Book.Ch03.h1EnergyNormOnCube (originCube d (min k m)) a
    (finiteCubeSolutionRestriction a (min_le_right k m) u).toH1

/-- On an inner scale, the centered energy is the energy of the exact cube
restriction. -/
theorem finiteCenteredCubeSolutionEnergy_eq_of_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) (hkm : k ≤ m) :
    finiteCenteredCubeSolutionEnergy a m u k =
      Book.Ch03.h1EnergyNormOnCube (originCube d k) a
        (finiteCubeSolutionRestriction a hkm u).toH1 := by
  simpa only [finiteCenteredCubeSolutionEnergy, finiteLipschitzEnergyRow,
    finiteLipschitzRestriction] using
    finiteLipschitzEnergyRow_eq_h1EnergyNormOnCube_of_le a m u k hkm

/-- The canonical normalized best-affine error of a finite cube solution on
an inner centered cube. -/
noncomputable def finiteCenteredCubeBestFitErrorAt
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) (_hkm : k ≤ m) : ℝ :=
  finiteLipschitzAffineErrorRow a m u k

/-- The centered-cube best-fit row is no larger than any affine candidate. -/
theorem finiteCenteredCubeBestFitErrorAt_le
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) (hkm : k ≤ m) (c : ℝ) (e : Vec d) :
    finiteCenteredCubeBestFitErrorAt a m u k hkm ≤
      normalizedAffineCandidateError (originCube d k) u.toH1.toFun c e := by
  exact finiteLipschitzAffineErrorRow_best_le a m u hkm c e

/-- The centered-cube best-fit row is attained by affine coefficients. -/
theorem finiteCenteredCubeBestFitErrorAt_exists_eq
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) (hkm : k ≤ m) :
    ∃ c : ℝ, ∃ e : Vec d,
      finiteCenteredCubeBestFitErrorAt a m u k hkm =
        normalizedAffineCandidateError (originCube d k) u.toH1.toFun c e := by
  refine ⟨finiteLipschitzBestIntercept a m u k,
    finiteLipschitzBestSlope a m u k, ?_⟩
  simp only [finiteCenteredCubeBestFitErrorAt, finiteLipschitzAffineErrorRow,
    finiteLipschitzRestriction_toFun, min_eq_left hkm]

/-- The canonical intercept of the affine best fit on an inner centered
cube. -/
noncomputable def finiteCenteredCubeBestFitInterceptAt
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) : ℝ :=
  finiteLipschitzBestIntercept a m u k

/-- The canonical slope of the affine best fit on an inner centered cube. -/
noncomputable def finiteCenteredCubeBestFitSlopeAt
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) : Vec d :=
  finiteLipschitzBestSlope a m u k

/-- The canonical coefficients attain the centered-cube best-fit error. -/
theorem finiteCenteredCubeBestFitErrorAt_eq_candidate
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (u : Book.Ch03.CubeSolution (originCube d m) a)
    (k : ℤ) (hkm : k ≤ m) :
    finiteCenteredCubeBestFitErrorAt a m u k hkm =
      normalizedAffineCandidateError (originCube d k) u.toH1.toFun
        (finiteCenteredCubeBestFitInterceptAt a m u k)
        (finiteCenteredCubeBestFitSlopeAt a m u k) := by
  simp only [finiteCenteredCubeBestFitErrorAt, finiteLipschitzAffineErrorRow,
    finiteCenteredCubeBestFitInterceptAt, finiteCenteredCubeBestFitSlopeAt,
    finiteLipschitzRestriction_toFun, min_eq_left hkm]

end

end HighContrast
end Homogenization
