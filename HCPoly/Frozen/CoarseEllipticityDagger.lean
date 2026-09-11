/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Setup

/-!
# The coarse ellipticity assumption `e.coarse.ellipticity`

The random-source coarse ellipticity assumption `e.coarse.ellipticity` at unit macroscopic
normalization: with exponent `g`, deterministic positive reference block `E`,
increasing gauge `Ψ` on `ℝ_+` with values in `[1, ∞)`, growth witness `K > 1`,
and nonnegative source scale `S`, the coarse block response of every standard
aligned cube whose center lies in `□_m` is dominated by the reference block with
the discount factor `3^{g(m-k)}`, almost surely on the event that the source has
burned at scale `m`.

The coefficient fields are uniformly elliptic almost everywhere, with ellipticity
constants belonging to the field and entering no estimate;
`e.qualitative.ellipticity` follows from this, and every quantitative object
of the development — `Π`, the gauge and its growth witness, `Θ_m`, and every
dimensional constant — is independent of them.
-/

/-- **The coarse ellipticity assumption `e.coarse.ellipticity`**, with exponent `g`,
deterministic positive reference block `E`, increasing gauge `Ψ` on `ℝ_+` with
values in `[1, ∞)`, growth witness `K > 1`, and nonnegative source scale `S`. -/
structure HCPoly.Frozen.CoarseEllipticityDagger {d : ℕ}
    (P : MeasureTheory.Measure (Homogenization.HighContrast.CoeffSpace d)) (g : ℝ)
    (E : Homogenization.BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : Homogenization.HighContrast.CoeffSpace d → ℝ) : Prop where
  g_mem : g ∈ Set.Ico (0 : ℝ) 1
  refBlock_isSymm : Homogenization.IsSymmetricBlockMat E
  refBlock_posDef : Homogenization.Book.Ch02.BlockPosDef E
  gauge_admissible : Homogenization.IndependentSums.AdmissiblePsi Ψ
  one_lt_growthWitness : 1 < K
  gauge_growth : Homogenization.IndependentSums.HasPsiGrowth Ψ K
  source_measurable : Measurable S
  source_nonneg : ∀ a, 0 ≤ S a
  source_tail : ∀ t : ℝ, 0 < t →
    P.real (Homogenization.IndependentSums.upperTailEvent S t) ≤ (Ψ t)⁻¹
  coarse_bound : ∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m →
    ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
      Homogenization.HighContrast.standardCellCenter k w ∈
        Homogenization.HighContrast.centeredCube d m →
      Homogenization.BlockMatLoewnerLE
        (Homogenization.HighContrast.coarseBlock
          (Homogenization.HighContrast.standardCell d k w) a)
        (Homogenization.HighContrast.blockScale
          ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E)
