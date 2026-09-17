import HCPoly.Entry.Multiscale.ResponseInputs.HC2b_DiagonalWeakRecentResponseField

/-!
# The cell energy layer

The metric square of the canonical state's average on one cell is controlled by the cell's
response size and the actual state energy there.  That is the statement proved below for an
arbitrary Chapter-2 cell; the aligned-subcell instance is its specialization.

## How the statement is expressed

The conclusion is stated with the `blockSqrt (respM0 F)` congruence
`blockVecDot (R v) (R v)` for the metric square, and with the two Loewner inputs `k` and `e`
for the two sizes `blockSize (adaptedResponse q k w a) E` and `diagonalWeakMetricFactor m E ^ 2`.
So the only genuinely new content at this layer is the STATE side:

1. the doubled optimizer state `X = (∇u, a∇u)` of `AdaptedDefs.lean` is a Chapter-2 doubled
  RESPONSE field;
2. its Chapter-2 energy density is exactly TWICE the optimizer energy density used here; the
  factor `2` is the doubled form `X · 𝐀 X = 2 ∇u · a ∇u`, and the same `2` relates
   `average … (blockVecDot state (𝐀 state))` to
   `diagonalWeakEnergy ^ 2 = variationEnergyValue` (`DiagonalWeakNormState.lean`);
3. `Book.Ch02.averageVec` and `cellAverage` (`AdaptedDefs.lean`) are the same
  function (`rfl`).

**The definitions `adaptedDomainAt`, `alignedIndex`, `coe_alignedIndex` and
`exists_restrict_solution_adaptedCellAtCenter` are NOT needed to state or prove the cell energy
bound**, because it is stated over an ARBITRARY `Book.Ch02.Domain d`.  They reappear only in
the aligned-subcell instance, where the subcell domain and the restriction do the work, and
where the geometric alignment fact `adaptedCellAtCenter q k w ⊆ adaptedCell q t` is taken as a
HYPOTHESIS rather than re-derived.

## No new definition

**This module introduces NO definition.**  The one definition it needs, `adaptedDomainAt` — the
per-`w` Chapter-2 domain of an aligned adapted subcell, the twin of `adaptedDomain`
(`HC1_DomainBridge.lean`) — is supplied by the imported
`HC2b_DiagonalWeakRecentResponseField.lean`, together with its explicit `∃`
satisfiability witness, which therefore sits ABOVE every consumer here in import order.
That definition selects no constant: its two fields are the
INEQUALITY-free structural obligations `IsOpenBoundedConvexDomain` and `Nonempty`, both of which
are already proved for every `adaptedCellAtCenter`.
-/

namespace Homogenization.HighContrast.Multiscale

open Homogenization.Book.Ch02
open MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The doubled energy density of an optimizer state -/

omit [NeZero d] in
/-- `Book.Ch02.blockMatrixField` is the pointwise `blockMatrixOfCoeff` of the
representative — the two definitions (`Book/Ch02/Block.lean` and
`CoarseGraining/BlockFormalism/Structures.lean`) have identical bodies. -/
theorem h6a_blockMatrixField_apply {U : Domain d} (a : CoeffOn U) (x : Vec d) :
    blockMatrixField a x = blockMatrixOfCoeff (a.toCoeffField x) := rfl

omit [NeZero d] in
/-- **The doubled energy density of a primal state.**  On the doubled state `(ξ, Aξ)` the
Chapter-2 block form collapses to TWICE the scalar energy density:
`(ξ, Aξ) · 𝐀 (ξ, Aξ) = 2 ξ · Aξ`.

`blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart`
(`CoarseGraining/BlockFormalism/MatrixIdentities.lean`) gives `𝐀 (ξ, Aξ) = (Aξ, ξ)` on the
nose; the rest is `blockVecDot`'s definition. -/
theorem h6a_blockEnergyDensity_primal {A : Mat d} (hdet : IsUnit (symmPart A).det) (ξ : Vec d) :
    blockVecDot ((ξ, matVecMul A ξ) : BlockVec d)
        (blockMatVecMul (blockMatrixOfCoeff A) ((ξ, matVecMul A ξ) : BlockVec d)) =
      2 * vecDot ξ (matVecMul A ξ) := by
  rw [blockMatVecMul_blockMatrixOfCoeff_primal_of_isUnit_det_symmPart A hdet ξ]
  show vecDot ξ (matVecMul A ξ) + vecDot (matVecMul A ξ) ξ = _
  rw [vecDot_comm (matVecMul A ξ) ξ]
  ring

/-! ## The state side — restriction, and membership in the doubled response space -/

omit [NeZero d] in
/-- **The doubled optimizer state lies in the cell's response space.**  Taking the adjoint
solution to be zero in `𝒮(U;a) = {(∇u + ∇u*, a∇u - aᵗ∇u*)}` gives `X = (∇u, a∇u) ∈ 𝒮(U;a)`. -/
theorem h6a_isDoubledResponseField_optimizerField {U : Domain d} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a) :
    IsDoubledResponseField U a
      { potential := u.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) } := by
  have h := Internal.Ch02.BookCh02.doubledFieldOfSolutions_mem_responseField_of_isEllipticFieldOn
    U a hEll u (zeroSolution U a.transpose)
  have hfield : doubledFieldOfSolutions a u (zeroSolution U a.transpose) =
      { potential := u.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) } := by
    unfold doubledFieldOfSolutions
    have hzero : (zeroSolution U a.transpose).toH1.grad = 0 := rfl
    rw [hzero]
    congr 1
    · funext x
      show u.toH1.grad x + (0 : Vec d → Vec d) x = u.toH1.grad x
      simp
    · funext x
      show matVecMul (a.toCoeffField x) (u.toH1.grad x) -
          matVecMul (a.transpose.toCoeffField x) ((0 : Vec d → Vec d) x) =
        matVecMul (a.toCoeffField x) (u.toH1.grad x)
      rw [show ((0 : Vec d → Vec d) x) = (0 : Vec d) from rfl, matVecMul_zero, sub_zero]
  rwa [hfield] at h

/-! ## The carrier bridges — energy, and the cell average -/

omit [NeZero d] in
/-- **The Chapter-2 energy of an optimizer state is TWICE the scalar one.**  The doubled field
`Y = (∇u, a∇u)` has `⨍_U (Y · 𝐀 Y) = 2 ⨍_U ∇u · a∇u`, and the right-hand average is exactly the
integrand of `weakOptimizerEnergy` (`HC2b_DiagonalWeakRecentSupport.lean`).

The pointwise step is the doubled energy identity above; it holds at every `x ∈ U` because
`hEll` makes `a(x)` elliptic there, and it is lifted to the average by
`Book.Ch02.average_eq_of_ae_eq` (`Book/Ch02/Dilation.lean`) along `ae_restrict_mem`. -/
theorem h6a_average_blockEnergyDensity_optimizerField {U : Domain d} (a : CoeffOn U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a) {Y : DoubledField d} (hpot : Y.potential = u.toH1.grad)
    (hflux : Y.flux = fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x)) :
    Book.Ch02.average U (fun x =>
        blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))) =
      2 * volumeAverage (U : Set (Vec d))
        (fun x => vecDot (optimizerField a.toCoeffField u x).1
          (optimizerField a.toCoeffField u x).2) := by
  have hpt : Book.Ch02.average U (fun x =>
        blockVecDot (Y.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))) =
      Book.Ch02.average U (fun x =>
        2 * vecDot (optimizerField a.toCoeffField u x).1
          (optimizerField a.toCoeffField u x).2) := by
    refine Book.Ch02.average_eq_of_ae_eq ?_
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    have hdet : IsUnit (symmPart (a.toCoeffField x)).det :=
      isUnit_det_symmPart_of_isEllipticMatrix (hEll.2 x hx)
    have hY : Y.eval x =
        ((u.toH1.grad x, matVecMul (a.toCoeffField x) (u.toH1.grad x)) : BlockVec d) := by
      show (Y.potential x, Y.flux x) = _
      rw [hpot, hflux]
    rw [hY, h6a_blockMatrixField_apply a x,
      h6a_blockEnergyDensity_primal hdet (u.toH1.grad x)]
    rfl
  rw [hpt]
  show (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ *
      ∫ x in (U : Set (Vec d)), 2 * vecDot (optimizerField a.toCoeffField u x).1
        (optimizerField a.toCoeffField u x).2 ∂MeasureTheory.volume = _
  rw [MeasureTheory.integral_const_mul]
  show _ = 2 * ((MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ * _)
  ring

omit [NeZero d] in
/-- `weakOptimizerEnergy` squared is the average it is the square root of, as soon as
that average is nonnegative. -/
theorem h6a_weakOptimizerEnergy_sq {V : Set (Vec d)} {b : CoeffField d}
    (u : AHarmonicFunction b V)
    (hnn : 0 ≤ volumeAverage V (fun x => vecDot (optimizerField b u x).1
      (optimizerField b u x).2)) :
    weakOptimizerEnergy V b u ^ 2 =
      volumeAverage V (fun x => vecDot (optimizerField b u x).1 (optimizerField b u x).2) :=
  Real.sq_sqrt hnn

omit [NeZero d] in
/-- **The cell average IS the Chapter-2 pair of vector averages.**  `cellAverage`
(`AdaptedDefs.lean`) and `Book.Ch02.averageVec` (`Book/Ch02/Response.lean`) have identical
bodies once `Book.Ch02.average` is unfolded to `volumeAverage`, so this is `rfl` after the two
field rewrites. -/
theorem h6a_averageVec_pair_eq_cellAverage {U : Domain d} {b : CoeffField d}
    (u : AHarmonicFunction b (U : Set (Vec d))) {Y : DoubledField d}
    (hpot : Y.potential = u.toH1.grad)
    (hflux : Y.flux = fun x => matVecMul (b x) (u.toH1.grad x)) :
    ((Book.Ch02.averageVec U Y.potential, Book.Ch02.averageVec U Y.flux) : BlockVec d) =
      cellAverage (U : Set (Vec d)) (optimizerField b u) := by
  rw [hpot, hflux]
  rfl

/-! ## The cell-energy bound on an arbitrary Chapter-2 cell -/

omit [NeZero d] in
/-- **The cell energy bound.**  *"The metric square of the canonical state's average on one
cell is controlled by the cell's response size and the actual state energy there."*

It is stated over an ARBITRARY Chapter-2 cell `U`, so that both the parent cell
`adaptedDomain q hq t` (`HC1_DomainBridge.lean`) and every aligned subcell are
instances.

The three encodings it replaces:

* `metricBlockNormSq m (…)` becomes the `blockSqrt (respM0 F)` congruence
  `blockVecDot (R v) (R v)` (`HC2b_DiagonalWeakRecentEnergyMap.lean`);
* `diagonalWeakMetricFactor m E ^ 2` becomes the Loewner input `k`
  (`HC2b_DiagonalWeakRecentSharpOrder.lean`);
* `blockSize (adaptedResponse q k w a) E` becomes the Loewner input `e`.

The `2` is the doubled quadratic form: the average identity above shows
`⨍_U (X · 𝐀 X) = 2 ⨍_U ∇u · a∇u`, and `weakOptimizerEnergy ^ 2` is the second average.  The
same `2` relates `average … (blockVecDot state (𝐀 state))` to
`diagonalWeakEnergy ^ 2 = variationEnergyValue` (`DiagonalWeakNormState.lean`). -/
theorem h6a_blockSq_cellAverage_optimizerField_le {U : Domain d} (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (u : Solution U a)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) {k e : ℝ} (hk : 0 < k) (he : 0 < e)
    (hEM : toFullBlockMat E ≤ k • toFullBlockMat (respM0 F))
    (hAE : toFullBlockMat (Book.Ch02.coarseBlockMatrix U a) ≤ e • toFullBlockMat E) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (U : Set (Vec d)) (optimizerField a.toCoeffField u)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (U : Set (Vec d)) (optimizerField a.toCoeffField u))) ≤
      (k * e) * (2 * weakOptimizerEnergy (U : Set (Vec d)) a.toCoeffField u ^ 2) := by
  have hY : IsDoubledResponseField U a
      { potential := u.toH1.grad
        flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) } :=
    h6a_isDoubledResponseField_optimizerField a hEll u
  have hmain := h6a_energy_map_respM0_le_coarseStarred a hEll hY hm hE hk he hEM hAE
  rw [h6a_averageVec_pair_eq_cellAverage (U := U) (b := a.toCoeffField) u
        (Y := { potential := u.toH1.grad
                flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) }) rfl rfl,
    h6a_average_blockEnergyDensity_optimizerField a hEll u
      (Y := { potential := u.toH1.grad
              flux := fun x => matVecMul (a.toCoeffField x) (u.toH1.grad x) }) rfl rfl] at hmain
  have hnn : 0 ≤ volumeAverage (U : Set (Vec d))
      (fun x => vecDot (optimizerField a.toCoeffField u x).1
        (optimizerField a.toCoeffField u x).2) := by
    have hlhs := blockVecDot_nonneg
      (blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (U : Set (Vec d)) (optimizerField a.toCoeffField u)))
    have hke : 0 < k * e := mul_pos hk he
    nlinarith [hlhs, hmain, hke]
  rw [h6a_weakOptimizerEnergy_sq u hnn]
  exact hmain

/-! ## The aligned-subcell instance

The cell energy bound above is stated over an arbitrary Chapter-2 cell, so the only thing an
aligned subcell needs is its Chapter-2 domain, `adaptedDomainAt`.  **That definition is NOT
introduced here.**  It and its satisfiability witness live in
`HC2b_DiagonalWeakRecentResponseField.lean`, which this module imports, so
the witness sits strictly ABOVE every consumer in import order.

The copy of `adaptedDomainAt` that stood here has been deleted as a duplicate.  The two copies
were signature-identical and differed only in how the `Nonempty` field was proved, which is a
`Prop`.  **This module now introduces NO definition of its own.** -/

/-- **The cell energy bound on an aligned adapted subcell, for the PARENT optimizer.**  The
left-hand side is the cell average of the PARENT state
`X_t = (∇u, a∇u)` over the subcell, and the right-hand side is the actual state energy THERE,
carried by the restricted solution `z` (`hz : z.grad = u.grad`).

The `obtain ⟨z, hz⟩ := exists_restrict_solution_adaptedCellAtCenter …` step is exactly `hz` here.
The geometric alignment fact `adaptedCellAtCenter q k w ⊆ adaptedCell q t` is NOT re-derived here:
it is taken as a hypothesis, and this statement does not need it at all, because `hz` already
carries its consequence. -/
theorem h6a_blockSq_cellAverage_optimizerField_adaptedCellAtCenter_le
    {q : Mat d} {hq : IsUnit q} {k : ℤ} {w : Fin d → ℤ}
    (a : CoeffOn (adaptedDomainAt q hq k w))
    (hEll : IsEllipticFieldOn a.lam a.Lam (adaptedCellAtCenter q k w) a.toCoeffField)
    {V : Set (Vec d)} (u : AHarmonicFunction a.toCoeffField V)
    (z : Solution (adaptedDomainAt q hq k w) a) (hz : z.toH1.grad = u.toH1.grad)
    {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef)
    {E : BlockMat d} (hE : (toFullBlockMat E).PosDef) {c e : ℝ} (hc : 0 < c) (he : 0 < e)
    (hEM : toFullBlockMat E ≤ c • toFullBlockMat (respM0 F))
    (hAE : toFullBlockMat
        (Book.Ch02.coarseBlockMatrix (adaptedDomainAt q hq k w) a) ≤ e • toFullBlockMat E) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter q k w) (optimizerField a.toCoeffField u)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter q k w) (optimizerField a.toCoeffField u))) ≤
      (c * e) *
        (2 * weakOptimizerEnergy (adaptedCellAtCenter q k w) a.toCoeffField z ^ 2) := by
  have hfield : optimizerField a.toCoeffField z = optimizerField a.toCoeffField u := by
    funext x
    show (z.toH1.grad x, matVecMul (a.toCoeffField x) (z.toH1.grad x)) = _
    rw [hz]
    rfl
  have h := h6a_blockSq_cellAverage_optimizerField_le a hEll z hm hE hc he hEM hAE
  rwa [hfield] at h

end

end Homogenization.HighContrast.Multiscale
