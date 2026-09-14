/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPolyAudit.AlgebraicConvergence.SolutionBasic
import HCPolyAudit.Support.AlgebraicConvergenceBridge
import HCPoly.MainResults

/-!
# Algebraic convergence at a polynomial scale: the proof of the Mathlib-only statement

This file proves the statement of `HCPolyAudit.AlgebraicConvergence.Challenge`, in
the vocabulary rebuilt over Mathlib alone in
`HCPolyAudit.AlgebraicConvergence.SolutionBasic`, from the library theorem
`HCPoly.algebraic_convergence` through the identifications of
`HCPolyAudit.Support.AlgebraicConvergenceBridge`.

The library theorem is stated in the same shape, so the proof is the transport
of its data: the law and the reference block are read through the block-matrix
conversion and the equality of the two local σ-fields, and the limit block it
produces is converted back, the Loewner order, the symmetry and positive
definiteness predicates, the scalar dilation and the Schur data all commuting
with that conversion.
-/

namespace HCPoly
namespace StatementAudit
namespace AlgebraicConvergence

open MeasureTheory

noncomputable section

/-- **Algebraic convergence at a polynomial scale** (`t.algebraic.convergence`).

For every dimension `d ≥ 2` and every coarse-ellipticity exponent `g ∈ [0, 1)`
there are constants `C > 0` and `κ > 0` such that, under the assumptions of
stationarity, unit range of dependence, and the random-source coarse ellipticity
`e.coarse.ellipticity` with reference block `E`, gauge `Ψ`, growth witness `K`
and source scale `S`, there are a deterministic generation `m₀ ∈ ℕ` and a
deterministic doubled block `𝐀̄` with

`m₀ ≤ ⌈C log₃ (2 + Π K)⌉`  (`e.algebraic.entry`),

`Θ_{m₀+j} - 1 ≤ 3^{-κ j}`  (`e.algebraic.contrast.decay`),

`𝐀̄` symmetric and positive definite with

`𝐀̄ ≤ 𝐀̄(□_{m₀+j}) ≤ (1 + 6 · 3^{-κ j}) 𝐀̄`  (`e.algebraic.block.decay`),

and Schur coefficients in the parametrization `e.annealed.schur` satisfying
`σ̄_* = σ̄`, with `σ̄` positive definite and `κ̄` antisymmetric.  Here
`Π = aspectRatio E` is the reference aspect ratio `e.reference.aspect.ratio`,
`Θ_m = annealedContrast P m` is the annealed contrast `e.Theta.m`, and
`𝐀̄(□_m) = annealedBlock P (centeredCube d m)` is the annealed block of the
centred cube.  The constants `C` and `κ` depend only on `d` and `g`: they are
chosen before the law, the reference block, the gauge, the growth witness and
the source scale.  No bound uniform as `g ↑ 1` is asserted. -/
theorem algebraic_convergence
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
        CoarseEllipticityDagger P g E Ψ K S →
        ∃ (m₀ : ℕ) (Abar : BlockMat d),
          (m₀ : ℤ) ≤ ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
          (∀ j : ℕ,
            annealedContrast P ((m₀ + j : ℕ) : ℤ) - 1 ≤
              (3 : ℝ) ^ (-κ * (j : ℝ))) ∧
          IsSymmetricBlockMat Abar ∧
          BlockPosDef Abar ∧
          (∀ j : ℕ,
            BlockMatLoewnerLE Abar
              (annealedBlock P (centeredCube d ((m₀ + j : ℕ) : ℤ))) ∧
            BlockMatLoewnerLE
              (annealedBlock P (centeredCube d ((m₀ + j : ℕ) : ℤ)))
              (blockScale (1 + 6 * (3 : ℝ) ^ (-κ * (j : ℝ))) Abar)) ∧
          schurSigmaStar Abar = schurSigma Abar ∧
          (schurSigma Abar).PosDef ∧
          IsSkewMat (schurSkew Abar) := by
  obtain ⟨C, κ, hC, hκ, hall⟩ := _root_.HCPoly.algebraic_convergence d hd g hg
  refine ⟨C, κ, hC, hκ, ?_⟩
  intro P E Ψ K S hP hstat hrange hdag
  obtain ⟨m₀, Abar, hentry, hcontrast, hsymm, hpos, hblock, hdual, hsigma, hskew⟩ :=
    hall (Bridge.toRepoLaw P) (Bridge.toRepoBlock E) Ψ K S
      (Bridge.isProbabilityMeasure_castMeasure (Bridge.instMeasurableSpace_eq d) P hP)
      (Bridge.isStationaryLaw_toRepoLaw hstat)
      (Bridge.isUnitRangeLaw_toRepoLaw hrange)
      (Bridge.coarseEllipticityDagger_toRepoLaw hdag)
  refine ⟨m₀, Bridge.ofRepoBlock Abar, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Bridge.aspectRatio_toRepoBlock E]
    exact hentry
  · intro j
    rw [Bridge.annealedContrast_eq]
    exact hcontrast j
  · exact Bridge.isSymmetricBlockMat_ofRepoBlock hsymm
  · exact Bridge.blockPosDef_ofRepoBlock hpos
  · intro j
    refine ⟨?_, ?_⟩
    · rw [Bridge.annealedBlock_centeredCube_eq]
      exact Bridge.blockMatLoewnerLE_ofRepoBlock (hblock j).1
    · rw [Bridge.annealedBlock_centeredCube_eq, ← Bridge.ofRepoBlock_blockScale]
      exact Bridge.blockMatLoewnerLE_ofRepoBlock (hblock j).2
  · rw [Bridge.schurSigmaStar_ofRepoBlock, Bridge.schurSigma_ofRepoBlock]
    exact hdual
  · rw [Bridge.schurSigma_ofRepoBlock]
    exact hsigma
  · rw [Bridge.schurSkew_ofRepoBlock]
    exact Bridge.isSkewMat_of_repo hskew

end

end AlgebraicConvergence
end StatementAudit
end HCPoly
