/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Audit.PolynomialEntry.SolutionBasic
import Audit.Support.PolynomialEntryBridge

/-!
# Polynomial entry into small contrast: the proof of the Mathlib-only statement

This file proves the statement of `Audit.PolynomialEntry.Challenge`, in the
vocabulary rebuilt over Mathlib alone in
`Audit.PolynomialEntry.SolutionBasic`, from the library theorem
`HCPoly.Frozen.polynomial_entry_random_source` through the identifications of
`Audit.Support.PolynomialEntryBridge`.

The library states `t.polynomial.entry` with a calibration triple
`(c_sc, δ₀, c_end)` subject to `(1 + δ₀)² (1 + c_end) ≤ 1 + c_sc`, and produces a
tolerance `c_* ∈ (0, min c_sc c_end]` at which the annealed contrast satisfies
`Θ_{m_ent} - 1 ≤ c_*`.  Given the single tolerance `σ ∈ (0, 1]` of the printed
statement, the triple `(σ, σ/8, σ/8)` is admissible, since
`(1 + σ/8)³ ≤ 1 + σ` for `0 < σ ≤ 1`; the resulting `c_*` is at most `σ`, which
is the printed display `e.polynomial.entry`.
-/

namespace HCPoly
namespace StatementAudit
namespace PolynomialEntry

open MeasureTheory

noncomputable section

/-- The calibration triple `(σ, σ/8, σ/8)` meets the threshold inequality of the
library statement for every tolerance `σ ∈ (0, 1]`. -/
theorem calibration_cube_le (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    (1 + σ / 8) ^ 2 * (1 + σ / 8) ≤ 1 + σ := by
  have hsq : σ * σ ≤ σ := by nlinarith [hσ0, hσ1]
  have hcube : σ * σ * σ ≤ σ := by nlinarith [hσ0, hσ1, hsq]
  have hexpand : (1 + σ / 8) ^ 2 * (1 + σ / 8) =
      1 + 3 * σ / 8 + 3 * (σ * σ) / 64 + σ * σ * σ / 512 := by ring
  rw [hexpand]
  linarith only [hsq, hcube, hσ0]

/-- **Polynomial entry into small contrast** (`t.polynomial.entry`).

For every dimension `d ≥ 2`, every coarse-ellipticity exponent `g ∈ [0, 1)`, and
every tolerance `σ ∈ (0, 1]` there is a finite constant `C > 0` such that, under
the assumptions of stationarity, unit range of dependence, and the random-source
coarse ellipticity `e.coarse.ellipticity` with reference block `E`, gauge `Ψ`,
growth witness `K` and source scale `S`, there is a deterministic entry
generation `m_ent ∈ ℕ` with

`m_ent ≤ ⌈C log₃ (2 + Π K)⌉`,  `Θ_{m_ent} ≤ 1 + σ`,  and
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
        ∃ mEnt : ℕ,
          (mEnt : ℤ) ≤ ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
          annealedContrast P (mEnt : ℤ) ≤ 1 + σ ∧
          (3 : ℝ) ^ mEnt ≤ 3 * (2 + aspectRatio E * K) ^ C := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  have hδ₀ : σ / 8 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith only [hσ0], by linarith only [hσ1]⟩
  obtain ⟨cStar, hcStar, hmain⟩ :=
    Frozen.polynomial_entry_random_source d hd σ (σ / 8) (σ / 8) hσ0 hδ₀
      (by linarith only [hσ0]) (calibration_cube_le σ hσ0 hσ1)
  obtain ⟨C, hC, hall⟩ := hmain g hg
  have hcStarσ : cStar ≤ σ := le_trans hcStar.2 (min_le_left _ _)
  refine ⟨C, hC, ?_⟩
  intro P E Ψ K S hP hstat hrange hdag
  obtain ⟨mEnt, hceil, hcontrast, hlength⟩ :=
    hall (Bridge.toRepoLaw P) (Bridge.toRepoBlock E) Ψ K S
      (Bridge.isProbabilityMeasure_castMeasure (Bridge.instMeasurableSpace_eq d) P hP)
      (Bridge.isStationaryLaw_toRepoLaw hstat)
      (Bridge.isUnitRangeLaw_toRepoLaw hrange)
      (Bridge.coarseEllipticityDagger_toRepoLaw hdag)
  rw [Bridge.aspectRatio_toRepoBlock E]
  refine ⟨mEnt, hceil, ?_, hlength⟩
  rw [Bridge.annealedContrast_eq]
  linarith only [hcontrast, hcStarσ]

end

end PolynomialEntry
end StatementAudit
end HCPoly
