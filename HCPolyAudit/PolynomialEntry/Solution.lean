/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPolyAudit.PolynomialEntry.SolutionBasic
import HCPolyAudit.Support.PolynomialEntryBridge
import HCPoly.MainResults

/-!
# Polynomial entry into small contrast: the proof of the Mathlib-only statement

This file proves the statement of `HCPolyAudit.PolynomialEntry.Challenge`, in the
vocabulary rebuilt over Mathlib alone in
`HCPolyAudit.PolynomialEntry.SolutionBasic`, from the library export
`HCPoly.polynomial_entry` of `HCPoly.MainResults` through the identifications of
`HCPolyAudit.Support.PolynomialEntryBridge`.

The export is applied to the binders of the statement, and its two conclusions
are carried across the bridge.
-/

namespace HCPoly
namespace StatementAudit
namespace PolynomialEntry

open MeasureTheory

noncomputable section

/-- **Polynomial entry into small contrast** (`t.polynomial.entry`).

For every dimension `d ≥ 2`, every coarse-ellipticity exponent `g ∈ [0, 1)`, and
every tolerance `σ ∈ (0, 1]` there is a finite constant `C > 0` such that, under
the assumptions of stationarity, unit range of dependence, and the random-source
coarse ellipticity `e.coarse.ellipticity` with reference block `E`, gauge `Ψ`,
growth witness `K` and source scale `S`, the annealed contrast satisfies

`Θ_m ≤ 1 + σ` at every generation `m ≥ ⌈C log₃ (2 + Π K)⌉`,

and that ceiling, carried as a natural number `m_ent ∈ ℕ`, has length

`3^{m_ent} ≤ 3 (2 + Π K)^C`,

where `Π = aspectRatio E` is the reference aspect ratio
`e.reference.aspect.ratio` and `Θ_m = annealedContrast P m` is the annealed
contrast `e.Theta.m`.  The constant `C` depends only on `σ`, `d` and `g`: it is
chosen before the law, the reference block, the gauge, the growth witness and
the source scale.  No bound uniform as `g ↑ 1` is asserted. -/
theorem polynomial_entry
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
        CoarseEllipticityDagger P g E Ψ K S →
        (∀ m : ℤ, ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ≤ m →
            annealedContrast P m ≤ 1 + σ) ∧
          ∃ mEnt : ℕ,
            (mEnt : ℤ) = ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
            (3 : ℝ) ^ (mEnt : ℕ) ≤ 3 * (2 + aspectRatio E * K) ^ C := by
  obtain ⟨C, hC, hall⟩ := _root_.HCPoly.polynomial_entry d hd g hg σ hσ
  refine ⟨C, hC, ?_⟩
  intro P E Ψ K S hP hstat hrange hdag
  obtain ⟨hcontrast, mEnt, hmEnt, hlength⟩ :=
    hall (Bridge.toRepoLaw P) (Bridge.toRepoBlock E) Ψ K S
      (Bridge.isProbabilityMeasure_castMeasure (Bridge.instMeasurableSpace_eq d) P hP)
      (Bridge.isStationaryLaw_toRepoLaw hstat)
      (Bridge.isUnitRangeLaw_toRepoLaw hrange)
      (Bridge.coarseEllipticityDagger_toRepoLaw hdag)
  rw [Bridge.aspectRatio_toRepoBlock E]
  refine ⟨fun m hm => ?_, mEnt, hmEnt, hlength⟩
  rw [Bridge.annealedContrast_eq]
  exact hcontrast m hm

end

end PolynomialEntry
end StatementAudit
end HCPoly
