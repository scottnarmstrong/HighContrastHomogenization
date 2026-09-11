/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Regularity.PrintOrderRoundedGenerationHarmonicComparison
import HCPoly.Provider.Regularity.FiniteCorrector
import Homogenization.PDE.DirichletRHS

namespace Homogenization
namespace HighContrast

open MeasureTheory

noncomputable section

theorem isWeakSolutionOn_finiteAffineSolution
    {d : ℕ} [NeZero d] (a : Book.Ch03.CoeffFamily d)
    (m : ℤ) (e : Vec d) :
    IsWeakSolutionOn (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
      (finiteAffineSolution a m e).toH1.grad := by
  let Q := originCube d m
  let U : Set (Vec d) := Book.Ch02.cubeDomain Q
  let b := a.coeffOn Q
  have hflux : MemVectorL2 U
      (fun x ↦ matVecMul (b.toCoeffField x)
        ((finiteAffineSolution a m e).toH1.grad x)) := by
    have hEll : IsAEEllipticFieldOn b.lam b.Lam U b.toCoeffField :=
      ⟨(Book.Ch02.cubeDomain Q).measurableSet,
        b.aeStronglyMeasurable, b.aeElliptic⟩
    exact hEll.memVectorL2_matVecMul
      (finiteAffineSolution a m e).toH1.grad_memVectorL2
  intro phi hphi
  let psi : H10Function U := H10Function.ofContDiff
    (Book.Ch02.cubeDomain Q).isOpen hphi.contDiff hphi.hasCompactSupport
      hphi.tsupport_subset
  have hpsiGrad : psi.toH1Function.grad = smoothGrad phi := rfl
  have htest : MemVectorL2 U (smoothGrad phi) := by
    simpa only [← hpsiGrad] using psi.toH1Function.grad_memVectorL2
  refine ⟨integrableOn_vecDot_of_memVectorL2 htest hflux, ?_⟩
  have hzero := (finiteAffineCubeSolution a m e).isHarmonic.2 psi
  simpa only [Q, U, b, hpsiGrad, vecDot_comm] using hzero

end

end HighContrast
end Homogenization
