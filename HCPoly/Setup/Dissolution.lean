/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup.CoefficientSpace
import Homogenization.CoarseGraining.MuAdmissibility

/-!
# Finiteness of the competitor energies: the coarse response is an honest infimum

The variational coarse block response `𝐀(U; a)` is defined through a Bochner
average of the block energy density over the cell `U`,
and that average carries a junk value on non-integrable integrands.  This file
removes the junk branch from the definition: on every bounded measurable cell,
*every* admissible competitor of the coarse variational problem has finite
energy, for *every* field of the coefficient space.

The mechanism is the local uniform ellipticity built into the coefficient space.
A sample field has a measurable representative that is uniformly elliptic at
every point of the cell, with the constants the cell's boundedness supplies; the
deterministic theory turns admissibility into the energy-integrability package
for that representative, and the energy density only sees the almost everywhere
class of the field.  Consequently the junk value of the Bochner average is never
attained and `𝐀(U; a)` is the honest infimum of the energy over the admissible
class.
-/

namespace Homogenization
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- On a field with a pointwise uniformly elliptic representative, every
admissible competitor of the coarse variational problem has finite energy, so
the junk branch of the Bochner average is unreachable and the coarse response is
the honest infimum. -/
theorem integrableOn_blockEnergyDensity_of_representative
    {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffSpace d} {f : CoeffField d} {lam Lam : ℝ}
    (hf : (⇑a.1 : Vec d → Mat d) =ᵐ[volume] f)
    (hEll : IsEllipticFieldOn lam Lam U f)
    {Q : BlockVec d} {X : BlockState d} (hX : IsBlockMuAdmissible U Q X) :
    IntegrableOn (blockEnergyDensity (⇑a.1) X) U volume := by
  have hInt := (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn
    (a := f) hEll).energyIntegrable
  refine hInt.congr ?_
  filter_upwards [ae_restrict_of_ae hf] with x hx
  simp only [blockEnergyDensity, blockCoeffField, hx]

/-- **The dissolution of the junk branch**, unconditionally on the coefficient
space: on every bounded measurable cell, every admissible competitor of the
coarse variational problem has finite energy.  The junk value of the Bochner
average is therefore never attained, and the coarse response `𝐀(U; a)` of the
variational definition is the honest infimum. -/
theorem integrableOn_blockEnergyDensity_coeffSpace
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUb : Bornology.IsBounded U)
    [IsFiniteMeasure (volumeMeasureOn U)]
    (a : CoeffSpace d) {Q : BlockVec d} {X : BlockState d}
    (hX : IsBlockMuAdmissible U Q X) :
    IntegrableOn (blockEnergyDensity (⇑a.1) X) U volume := by
  obtain ⟨lam, Lam, f, hlam, hle, hfm, hfp, hfa⟩ :=
    exists_pointwise_elliptic_representative a.2 hUb
  refine integrableOn_blockEnergyDensity_of_representative (lam := lam)
    (Lam := Lam) hfa ⟨?_, hfp⟩ hX
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact Measurable.ite hU
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hfm)))
    measurable_const

end

end HighContrast
end Homogenization
