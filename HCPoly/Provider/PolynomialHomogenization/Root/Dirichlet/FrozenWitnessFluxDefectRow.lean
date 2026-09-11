/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessClassBRows
import HCPoly.Provider.PolynomialHomogenization.ScheduledLocalizationRowSupply
import HCPoly.Provider.PolynomialHomogenization.ScheduledLocalizationGaugeReduction

/-!
# The composed row `hFdefect`

`memVectorL2_physical_flux_difference` needs an `AEUniformlyEllipticField`
representative of the gauge coefficient, which `exists_gaugeReducedSource`
supplies for exactly the `aHat` premise.  The shape difference — `(aHat − 1) ∇u`
against `aHat ∇u − ∇h` — is closed by `sub_matVecMul` and `matVecMul_one` at
`h := u`, as predicted.
-/

namespace Homogenization
namespace HighContrast
namespace RowSupply

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **Row `hFdefect`.**  The gauge flux defect of the frozen witness is
square-integrable on the gauge domain. -/
theorem frozenWitness_fluxDefect_memVectorL2 [NeZero d] {abar : Mat d}
    (hS : (symmPart abar).PosDef) {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    {epsilon : ℝ} {a : CoeffSpace d} (hepsilon : 0 < epsilon)
    (hU : U = (fun x : Vec d => z + matVecMul (matSqrt (symmPart abar)) x) ''
      openCubeSet (originCube d j))
    {aHat : CoeffField d}
    (haHat : aHat = affineCoefficient (matSqrt (symmPart abar))
      (isUnit_det_matSqrt hS)
      (fun x => scaledCoeff epsilon a x - skewPart abar))
    (uHat : H1Function (matImage (matSqrt (symmPart abar))⁻¹ U)) :
    MemVectorL2 (matImage (matSqrt (symmPart abar))⁻¹ U)
      (fun y ↦ matVecMul (aHat y - 1) (uHat.grad y)) := by
  obtain ⟨aSource, haSource, haeSource⟩ :=
    exists_gaugeReducedSource hS hepsilon a
  have haeq : (⇑aSource : CoeffField d) =ᵐ[volume] aHat := by
    rw [haHat]
    exact haeSource
  have hmem := memVectorL2_physical_flux_difference
    (frozenWitness_gaugeDomain_isOpenBoundedConvexDomain hS hU) aSource haSource
    aHat haeq uHat uHat
  have hfun : (fun y ↦ matVecMul (aHat y - 1) (uHat.grad y)) =
      fun y ↦ matVecMul (aHat y) (uHat.grad y) - uHat.grad y := by
    funext y
    rw [sub_matVecMul, matVecMul_one]
  rw [hfun]
  exact hmem

end

end RowSupply
end HighContrast
end Homogenization
