import HCPoly.Entry.Setup.CoarseEllipticityDagger
import HCPoly.Entry.Setup.Stationarity
import HCPoly.Entry.Setup.UnitRange
import HCPoly.Entry.Setup.Response
import HCPoly.Setup.BlockAlgebra
import HCPoly.Entry.PolynomialEntry

/-!
# Theorem `t.polynomial.entry` — polynomial entry into small contrast

The paper's Theorem A, stated directly in `σ`.

`C` is bound before `P`, `E`, `Ψ`, `K` and `S`. That binder order is the content of the
sentence following the theorem — "the constant `C` above is independent of `E`, the coefficient
law, `Π`, and `K_{Ψ_S}`" — and it is what lets one `C` serve two arbitrary laws at once.

The conclusion is the printed one: `Θ_m ≤ 1 + σ` for every scale `m ≥ m_ent`, where
`m_ent := ⌈C log₃(2 + Π K_{Ψ_S})⌉`. Nothing asserts that `m_ent` is the first scale at which
the contrast is small, and `γ` is bound before `C`, so no uniformity is claimed as `γ ↑ 1`.

`Θ_m` is `annealedContrast` (`e.Theta.m`); `Π K_{Ψ_S}` is `aspectRatio E * K`.

The proof is one application of `Homogenization.HighContrast.Provider.polynomial_entry` (`HCPoly/Entry/PolynomialEntry.lean`) to the binders of the statement.
-/

open Homogenization.HighContrast (CoeffSpace annealedContrast aspectRatio)
namespace Homogenization.HighContrast

open MeasureTheory

/-- **Theorem `t.polynomial.entry`.** For every `d ≥ 2`, `γ ∈ [0,1)` and `σ ∈ (0,1]` there is
`C(σ,d,γ) > 0` such that, under the standing assumptions, `Θ_m ≤ 1 + σ` for every scale
`m ≥ ⌈C log₃(2 + Π K)⌉`. -/
theorem polynomial_entry
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ m : ℤ, ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ≤ m →
          annealedContrast P m ≤ 1 + σ := by exact Homogenization.HighContrast.Provider.polynomial_entry d hd γ hγ σ hσ

end Homogenization.HighContrast
