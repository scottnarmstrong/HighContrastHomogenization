import HCPoly.Entry.Setup.Response
import HCPoly.Entry.Geometry.StandardCell
import Homogenization.Probability.IndependentSums.PsiCalculus
import HCPoly.Setup.CoefficientSpace

/-!
# The coarse ellipticity assumption

Near `a.coarse.ellipticity`.  The random-scale coarse ellipticity condition together with the
source tail: with exponent `g`, deterministic positive reference block `E`, increasing gauge
`Ψ` on `ℝ_+` with values in `[1, ∞)`, growth witness `K > 1`, and nonnegative random scale
`S`, the coarse block response of every standard aligned cube whose center lies in `□_m` is
dominated by the reference block with the discount factor `3^{g(m-k)}`, almost surely on the
event `3^m ≥ S`.

The coefficient fields are locally uniformly elliptic in the qualitative sense, with
ellipticity constants belonging to the field and entering no estimate; every quantitative
object of the development — `Π`, the gauge and its growth witness, `Θ_m`, and every
dimensional constant — is independent of them.

The ten fields are the printed assumption, field by field.  `g_mem`, `refBlock_isSymm`,
`refBlock_posDef`, `gauge_admissible`, `one_lt_growthWitness` and `source_nonneg` are the
printed data — "an exponent `γ ∈ [0,1)`", "a symmetric positive definite matrix `𝐄`", "an
increasing function `Ψ_𝖲 : ℝ_+ → [1,∞)` with a constant `K_{Ψ_𝖲} ∈ (1,∞)`" and "a nonnegative
random variable `𝖲`"; `source_tail` and `gauge_growth` are the two halves of
`e.source.tail`; `source_measurable` is what "random variable" means; and `coarse_bound` is
`e.coarse.ellipticity`.  Nothing is added and nothing is dropped.

`coarse_bound` is the printed display, not a restriction of it.  `e.coarse.ellipticity` is
stated at the origin — almost surely, for every `m ∈ ℤ`, `3^m ≥ 𝖲` implies
`𝐀(y+□_k;a) ≤ 3^{γ(m-k)}𝐄` for every `k ≤ m` and every `y ∈ 3^k ℤ^d ∩ □_m` — and the
manuscript derives the same bound at every `z ∈ ℤ^d`, with `𝖲(z)` in place of `𝖲`, from
stationarity.  That derivation therefore belongs to the stationarity assumption, which this
development carries separately, and not to this structure.
-/

open Homogenization.HighContrast (CoeffSpace blockScale coarseBlock)
open Homogenization.HighContrast (centeredCube standardCell standardCellCenter)
namespace Homogenization.HighContrast

open MeasureTheory Geometry

/-- **The coarse ellipticity assumption** (`e.coarse.ellipticity`, `e.source.tail`), with
exponent `g`, deterministic positive reference block `E`, increasing gauge `Ψ` on `ℝ_+` with
values in `[1, ∞)`, growth witness `K > 1`, and nonnegative random scale `S`. -/
structure CoarseEllipticityDagger {d : ℕ} (P : Measure (CoeffSpace d)) (g : ℝ)
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ) : Prop where
  g_mem : g ∈ Set.Ico (0 : ℝ) 1
  refBlock_isSymm : IsSymmetricBlockMat E
  refBlock_posDef : Book.Ch02.BlockPosDef E
  gauge_admissible : IndependentSums.AdmissiblePsi Ψ
  one_lt_growthWitness : 1 < K
  gauge_growth : IndependentSums.HasPsiGrowth Ψ K
  source_measurable : Measurable S
  source_nonneg : ∀ a, 0 ≤ S a
  source_tail : ∀ t : ℝ, 0 < t →
    P.real (IndependentSums.upperTailEvent S t) ≤ (Ψ t)⁻¹
  coarse_bound : ∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m →
    ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
      standardCellCenter k w ∈ centeredCube d m →
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
        (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E)

end Homogenization.HighContrast
