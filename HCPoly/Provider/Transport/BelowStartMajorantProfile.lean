/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CenteredMajorantSource

/-!
# Below-start target maximum against the transported source remainder

The common below-start multiplier is first estimated without target
multiplicity and then charged to the displayed transported source remainder.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The shared below-start maximum is bounded by one transported-source
remainder, with a coefficient independent of the target family. -/
theorem below_start_majorant_max_le_source_remainder [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K Cd : ℝ} {jStar M : ℤ}
    {Y : CoeffSpace d → ℝ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hw : IsCoupledWindow d Q K jStar M)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y)
    {F : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hF : IsSymmetricBlockMat F) (hFpd : Book.Ch02.BlockPosDef F)
    {rhoMax A D Lam a : ℝ} (hrho : rhoMax < 1)
    (hA : 0 ≤ A) (hD0 : 0 ≤ D) (hAD : A * blockSize E F ≤ D)
    {iota : Type*} [DecidableEq iota] (s : Finset iota) (hs : s.Nonempty)
    (lev : iota → ℤ) {n : ℤ} (hlev : ∀ i ∈ s, jStar ≤ lev i)
    (hLam : 1 ≤ Lam) (mu mu' : Mat d) (hCd : 0 ≤ Cd) (hg : g < 1)
    (hD : D ≤ Lam * transportSrcCoeff Cd g E jStar mu mu')
    (hjn : jStar ≤ n) (haQrho : a ≤ (Q : ℝ) * rhoMax) :
    ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i =>
        (3 : ℝ) ^ (rhoMax * ((lev i : ℝ) - (n : ℝ))) *
          schattenSize (Q : ℝ)
            (blockScale
              (A * (3 : ℝ) ^ (jStar - lev i) *
                (Y x - ∫ y, Y y ∂P)) E) F) ^ (Q : ℝ) ∂P ≤
      ENNReal.ofReal
        (((4 * (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹) ^ (Q : ℝ) *
            Lam ^ (Q : ℝ)) *
          transportSrcRemainder Cd g (Q : ℝ) a E jStar mu mu' n) := by
  have hraw := finite_below_start_max_moment_le hQ hw hY hE hF hFpd
    hrho hA hD0 hAD s hs lev (n := n) hlev
  have hQR0 : (0 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 0 ≤ Q)
  have hbase0 : 0 ≤ 4 * (2 * (d : ℝ)) ^ ((Q : ℝ))⁻¹ * D *
      (3 : ℝ) ^ (-rhoMax * ((n : ℝ) - (jStar : ℝ))) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hbase0 hQR0] at hraw
  have habs := below_start_coefficient_absorbed
    (Q := (Q : ℝ)) (d := d) (a := a) (rhoMax := rhoMax)
    (by exact_mod_cast (by omega : 1 ≤ Q)) hLam hD0 E mu mu' hCd hg hD hjn haQrho
  exact hraw.trans (ENNReal.ofReal_le_ofReal (by
    simpa only [mul_assoc] using habs))

end

end Transport
end HighContrast
end Homogenization
