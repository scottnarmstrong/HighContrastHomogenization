import HCPoly.Frozen.CoarseEllipticityDagger
import HCPoly.Setup.BlockAlgebra
import Homogenization.CoarseGraining.BlockMatrixProperties
import Homogenization.CoarseGraining.CoarseBounds
import HCPoly.Setup.Response
import HCPoly.Entry.Geometry.StandardCell
import Homogenization.Probability.IndependentSums.PsiCalculus
import HCPoly.Setup.CoefficientSpace
import HCPoly.Entry.Setup.Profile
import HCPoly.Frozen.Stationarity
import HCPoly.Setup.LocalSigmaFields
import HCPoly.Frozen.UnitRange
import HCPoly.Entry.Geometry.RoundedGridBasic
import HCPoly.Entry.OneGridPropagation

/-!
# Proposition `p.fixed.geometry.one.grid.propagation` — propagation on one adapted geometry

The paper's Proposition "Propagation on one adapted geometry", transcribed from the printed
display, with its four conclusions (i)–(iv) as a four-fold conjunction, each conjunct carrying
its own guard as an implication.

Reading of the display:

* `𝒫_q(m;n)` is `profile P γ q jStar n m` (the definition takes the base scale first),
  `ℋ_q(m)` is `history P γ q jStar m`, `D_{q,j_*}(m)` is `determinantDrift`, `Δ^q_{j,k}` is
  `detIncrement` and `Δ̂^q_h(m)` is `synchCharge`. `Q` is `bigQ d γ` of
  `e.scale.selection.Q.choice`.
* `C = C(d,γ) < ∞` depends on the dimension and the coarse-ellipticity exponent only, so its
  quantifier precedes `h`, `L`, `j_*`, the law and the geometry; `0 < C` is written for the
  printed `C < ∞` of a constant used as an upper bound.
* `h ∈ ℕ` with `h ≥ 2Q` and `L ≥ 1` an integer are the printed constraints; `𝔪 ∈ ℝ^{d×d}_{pos}`
  is `Matrix.PosDef`, named `metric` because `m` and `m₀` are scales in this display, and
  `q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift.
  The standing `3^{j_*} ≥ 2d` is `hj` and the standing `d ≥ 2` is `hd`.
* The source lower scale `e.source.lower.scale`, `j_* ≥ ⌈C_src(d,γ) log_3(2K_{Ψ_S})⌉`, is
  standing from the point where the paper fixes `j_*` onward, so every statement whose type
  mentions `j_*` carries it. `C_src` is existential in the outermost constant group, before
  `C`, `h`, `L`, `j_*`, the coefficient law and the geometry, since the paper fixes one such
  constant for the whole argument at `(d,γ)`.
* In conclusion (iv) (`e.fixed.geometry.synchronized.multiplicity`) the printed number of
  steps `K ≥ 1` is named `Ksteps`, because `K` is the growth constant `K_{Ψ_S}` of the standing
  assumptions; `Σ_{k=0}^{K−1}` is a sum over `Finset.range Ksteps`. Its initial scale `m_0`
  is the bound integer `m₀`, and both of its losses are taken on the fixed geometry `𝒬(𝔪)`.
* The display names no hypothesis on the coefficient law; the paper's standing assumptions
  (P1)–(P3) are in force throughout and are carried explicitly.
* Not carried: any integrability or finiteness premise. The histories, the profile and the
  drift are total real formulas whose divergent cases are junk values; the display asserts no
  premise excluding them and none is added here.

The proof is one application of
`Homogenization.HighContrast.Entry.fixed_geometry_one_grid_propagation`
(`HCPoly/Entry/OneGridPropagation.lean`) to the binders of the statement.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast

open MeasureTheory

/-- **Proposition `p.fixed.geometry.one.grid.propagation`.** There are `C_src(d,γ)` and
`C = C(d,γ)` such that, for every `j_*` satisfying `e.source.lower.scale`, for `h ≥ 2Q`,
`L ≥ 1`, `𝔪` positive definite, `q = 𝒬(𝔪)` and `j_* ≤ n ≤ m`: (i) the profile majorizes the
history (`e.fixed.geometry.profile.majorization`); (ii) if `m ≥ n + h`, the profile with the
drift contracts over a synchronized step (`e.fixed.geometry.synchronized.propagation`);
(iii) from a small input, at `m = n` or `m ≥ n + h`, the profile with the drift propagates over
a fixed span (`e.fixed.geometry.fixed.span.propagation`); (iv) the synchronized losses sum to
at most `h` times one loss (`e.fixed.geometry.synchronized.multiplicity`). -/
theorem fixed_geometry_one_grid_propagation
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
          ∀ L : ℤ, 1 ≤ L →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ (metric : Mat d), metric.PosDef →
                ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
                  history P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                      C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h : ℤ)) +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            (m + (h : ℤ)) ≤
                        1 / 8 *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                (h : ℤ) m) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m) +
                          C *
                            (Real.exp ((bigQ d γ : ℝ) *
                                synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                  (h : ℤ) m) - 1)) ∧
                    ((m = n ∨ n + (h : ℤ) ≤ m) →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) +
                            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) m
                                  (m + L)) - 1)) ∧
                    (∀ m₀ : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m₀ →
                      ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                        ∑ k ∈ Finset.range Ksteps,
                            synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ)
                              (m₀ + (k : ℤ) * (h : ℤ)) ≤
                          (h : ℝ) *
                            detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                              (m₀ + 1 - (h : ℤ)) (m₀ + (Ksteps : ℤ) * (h : ℤ))) := by exact Homogenization.HighContrast.Entry.fixed_geometry_one_grid_propagation d hd γ hγ

end Homogenization.HighContrast
