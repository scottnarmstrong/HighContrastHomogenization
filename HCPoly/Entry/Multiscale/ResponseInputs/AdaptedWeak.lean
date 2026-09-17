import HCPoly.Entry.Multiscale.ResponseInputs.AdaptedWeakRoute

/-!
# R1 decomposition, part 4: the weak-norm estimate

The weak-norm estimate of the decomposition of R1 `adapted_response_core` is
`e.response.weak.estimate`.

The concrete scale-average seminorm used here is the one of the cell-average lemma of the
high-contrast reference, on the selected grid, not the compact-test dual norm of the theorem
statements.  The estimate splits as `3^{-αH}` from the scales older than the response window
plus `C_H η^{1/(2Q)}` from the recent cell fluctuations, the mean differences, and the
correction from random to annealed centering.  This is where the histories retained through
the iteration enter the response argument: small fluctuations at the terminal scale alone
would not control the cell averages in this seminorm.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## The weak-norm estimate -/

/-- **The weak-norm estimate** `e.response.weak.estimate`:
`(W^±)^{1/2} ≤ C (3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2}`, with `α = (1-γ)/4`.

`K_0 = |M_0^{-1/2} Ê_t^± M_0^{-1/2}|^{1/2} ≤ C κ_s^{1/4}`, and the variational bound on the
mean of a gradient–solenoidal field holds on every Lipschitz cell, so the cell-average
argument applies on the selected grid with exponent `1/2`, decay exponent `ρ`, cutoff `1` and
window `H`.  The recent-cell differences contribute `C_H K_0 L^± η^{1/(2Q)}` through the mean
penalty; the energy split at the cutoff `1` contributes `C K_0 L^± (η^{1/2} + 3^{-αH})` using
`E[M^Q] ≤ C η`; the random-to-annealed recentering costs the same order.  Finally
`K_0 L^± ≤ C κ_s^{1/2}` by the calibrated-block and load bounds. -/
theorem response_weak_estimate (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) (Cc Ce Cl Cm Cs : ℝ) (hCc : 0 < Cc)
    (hCe : 0 < Ce) (hCl : 0 < Cl) (hCm : 0 < Cm) (hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ (C : ℝ) (CH : ℕ → ℝ), 0 < C ∧ (∀ n : ℕ, 0 < CH n) ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespCalibrated Cc P jStar F s t →
            ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
              Cprof * σ ^ ((1 - γ) / 8) ≤ η →
              RespSourceSmall d γ Cs η E F jStar s t →
              ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
              ∀ e : Vec d, vecDot e e = 1 →
                RespEnergyDefect Ce P jStar F s t e →
                RespLoadMean Cl P jStar F s t e →
                RespWeakBound C CH d γ P jStar F H η s t e :=
  response_weak_estimate_of_route d hd γ hγ S hS Cc Ce Cl Cm Cs hCc hCe hCl hCm hCs

end Homogenization.HighContrast.Multiscale
