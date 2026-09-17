import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Setup.BlockAlgebra

/-!
# The annealed-block form of the two error scalars of the cutoff rows

The cutoff rows of the response estimate bound the centred response by expressions in
`respEJMinus`, `respTauMinus` and `respLsMinus`.  The first two are Bochner integrals of the
pathwise response; under the entrywise integrability hypotheses the cutoff rows carry, both are
algebraic functions of the annealed recentred blocks.  This file records the two identities that
replace those integrals by the quadratic form of the annealed block.

The second identity is the underlying entrywise statement, `e.annealed.schur`: the quadratic form
of a doubled block commutes with the Bochner integral entrywise.  The first identity is then the
source form of the centred response energy `e.response.cutoff.estimate`: the pathwise response
`J(U_u, p, q'; b a)` is the block energy `x. A x / 2 - p. q'`, so its `P`-expectation is the
same block energy of the annealed block `E[A]`.
-/

open Homogenization.HighContrast (CoeffSpace blockVecDot_blockMatVecMul_eq_sum)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The quadratic form commutes with the annealed expectation.**  For any doubled vector `X`,
the `P`-integral of the pathwise quadratic form `X. (coarseBlockMatrix V (b a)) X` equals the
quadratic form of the entrywise annealed block `annealedBlockOf P V b`, whenever every entry of
the pathwise block is `P`-integrable.  This is the entrywise expectation identity `E[A]` of
`e.annealed.schur`. -/
theorem integral_blockVecDot_blockMatVecMul_coarseBlockMatrix {d : ℕ}
    (P : Measure (CoeffSpace d)) (V : Set (Vec d)) (b : CoeffSpace d → CoeffField d)
    (X : BlockVec d)
    (hint : ∀ α β : BlockCoord d,
      Integrable (fun a => blockMatEntry (coarseBlockMatrix V (b a)) α β) P) :
    (∫ a, blockVecDot X (blockMatVecMul (coarseBlockMatrix V (b a)) X) ∂P)
      = blockVecDot X (blockMatVecMul (annealedBlockOf P V b) X) := by
  have hentry : ∀ α β : BlockCoord d,
      blockMatEntry (annealedBlockOf P V b) α β
        = ∫ a, blockMatEntry (coarseBlockMatrix V (b a)) α β ∂P := by
    intro α β
    cases α <;> cases β <;> rfl
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec X α *
        (blockMatEntry (coarseBlockMatrix V (b a)) α β * toFullBlockVec X β)) P :=
    fun α β =>
      ((hint α β).mul_const (toFullBlockVec X β)).const_mul (toFullBlockVec X α)
  have hrow : ∀ α : BlockCoord d, Integrable (fun a =>
      ∑ β : BlockCoord d, toFullBlockVec X α *
        (blockMatEntry (coarseBlockMatrix V (b a)) α β * toFullBlockVec X β)) P :=
    fun α => integrable_finsetSum _ fun β _ => hterm α β
  simp only [blockVecDot_blockMatVecMul_eq_sum, hentry]
  rw [integral_finsetSum _ fun α _ => hrow α]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_finsetSum _ fun β _ => hterm α β]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [integral_const_mul, integral_mul_const]

/-- **The pathwise response integrates to the annealed block energy.**  If the pathwise response
is the doubled block energy `x. A x / 2 - p. q'` with `x = (-p, q')` and `A` the coarse block
matrix of the adapted cell, and if the entries of `A` are `P`-integrable, then the expectation of
the response is the same block energy evaluated at the annealed block `Aann`:
`∫ J = x. Aann x / 2 - p. q'`.  This is the first step of the cutoff rows of
`e.response.cutoff.estimate`. -/
theorem integral_respJ_eq_blockResponseEnergy {d : ℕ}
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (qq : Mat d) (u : ℤ) (p q' : Vec d) (b : CoeffSpace d → CoeffField d) (Aann : BlockMat d)
    (hpath : ∀ a : CoeffSpace d, respJ qq u p q' (b a)
      = (1 / 2 : ℝ) * blockVecDot (-p, q')
          (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) (-p, q'))
        - vecDot p q')
    (hint : ∀ α β : BlockCoord d, Integrable (fun a =>
      blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) α β) P)
    (hann : annealedBlockOf P (HighContrast.adaptedCell qq u) b = Aann) :
    (∫ a, respJ qq u p q' (b a) ∂P)
      = (1 / 2 : ℝ) * blockVecDot (-p, q') (blockMatVecMul Aann (-p, q')) - vecDot p q' := by
  have hterm : ∀ α β : BlockCoord d, Integrable (fun a =>
      toFullBlockVec (-p, q') α *
        (blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a)) α β *
          toFullBlockVec (-p, q') β)) P :=
    fun α β =>
      ((hint α β).mul_const (toFullBlockVec (-p, q') β)).const_mul
        (toFullBlockVec (-p, q') α)
  have hQint : Integrable (fun a => blockVecDot (-p, q')
      (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell qq u) (b a))
        (-p, q'))) P := by
    simp only [blockVecDot_blockMatVecMul_eq_sum]
    exact integrable_finsetSum _ fun α _ =>
      integrable_finsetSum _ fun β _ => hterm α β
  have hQ := integral_blockVecDot_blockMatVecMul_coarseBlockMatrix P
    (HighContrast.adaptedCell qq u) b (-p, q') hint
  have huniv : P.real Set.univ = 1 := by simp
  simp only [hpath]
  rw [integral_sub (hQint.const_mul _) (integrable_const _), integral_const_mul, hQ, hann,
    integral_const, huniv, one_smul]

end

end Homogenization.HighContrast.Multiscale
