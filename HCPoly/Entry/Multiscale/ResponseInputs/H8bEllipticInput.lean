import HCPoly.Entry.Multiscale.ResponseInputs.HC1_DomainBridgeAnnealedBlock
import HCPoly.Entry.Multiscale.ResponseInputs.H1LinearPullback

/-!
# The elliptic input for the cutoff bound, and the pulled-back flux it feeds

`IsEllipticFieldOn lam Lam (adaptedCell q t) b` is a hypothesis that the cutoff bound
(`integral_abs_hc3CutoffPairingOnCell_le_respWeak`, `HC3_CutoffKernel.lean`) does not carry and
would have to be given one, in order to reach
`MemLp flux 2 (normalizedCubeMeasure Q)` for the pulled-back flux -- the `hflux` slot of the
generic CG product bridge
`Book.Ch05.Section53.JUpperBoundWeakNorms.abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct`.

**It does not have to be given one.**  For the two coefficients the cutoff bound actually quantifies over,
`respCoeffMinus F a` and `respCoeffPlus F a` with `a : CoeffSpace d`, the datum is DERIVABLE from
`a`'s own qualitative local uniform ellipticity (`HCPoly/Setup/CoefficientSpace.lean`) together
with the invertibility of the grid, which the cutoff bound carries through its premise
`2 * d ≤ 3 ^ jStar`.  The derivation is
`Annealed.exists_elliptic_representative_adapted` (`HCPoly/Entry/Annealed/AdaptedDomainRecovery.lean`)
followed by `isEllipticFieldOn_sub_skew`/`isEllipticFieldOn_transpose_add_skew`; it is exactly the
derivation already performed inside `bddAbove_respWeakEnergySet_respCoeffMinus`
(`HC1_DomainBridge.lean`), lifted here to a reusable statement.

The shape is the a.e.-REPRESENTATIVE one -- ellipticity of some `f` with
`respCoeffMinus F a =ᵐ f` on the cell -- and not ellipticity of `respCoeffMinus F a` on the nose,
because a point of `CoeffSpace d` is an a.e. class and no representative of it is elliptic
pointwise.  This is the same shape as the `bddAbove_respWeakEnergySet` hypothesis
(`HC1_DomainBridge.lean`) and as
`CoeffSpace.exists_pointwise_coeffOn_family_aeeq`, and it is
enough for every `MemLp`/`Integrable` consumer, all of which are a.e. invariant.
-/

open Homogenization.HighContrast (CoeffSpace)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The elliptic representative on an adapted cell, for both response coefficients -/

/-- **The elliptic input for the cutoff bound, minus sign.**  For every sample `a` the coefficient
`a_- = a - g` has, on the adapted cell, an a.e.-equal representative that is uniformly elliptic
there.  Nothing but invertibility of the grid is needed; the constants belong to the sample and
to the cell and enter no estimate, since the ellipticity is qualitative and local. -/
theorem exists_elliptic_representative_respCoeffMinus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        respCoeffMinus F a =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => f x - respg F, hlam, ?_,
    isEllipticFieldOn_sub_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0:ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffMinus, hx]

/-- **The elliptic input for the cutoff bound, plus sign.**  The transposed twin, for `a_+ = a^t + g`. -/
theorem exists_elliptic_representative_respCoeffPlus (q : Mat d) (hq : IsUnit q) (t : ℤ)
    (F : BlockMat d) (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f ∧
        respCoeffPlus F a =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f := by
  obtain ⟨lam, Lam, f, hlam, hle, hEll, hae⟩ :=
    Annealed.exists_elliptic_representative_adapted q hq t 0 a
  rw [adaptedCellTranslate_zero] at hEll
  refine ⟨lam, 2 * Lam + 2 * ‖respg F‖ ^ 2 / lam, fun x => matTranspose (f x) + respg F, hlam, ?_,
    isEllipticFieldOn_transpose_add_skew hEll _ (respg_isSkew F), ?_⟩
  · have hn : (0:ℝ) ≤ 2 * ‖respg F‖ ^ 2 / lam := by positivity
    linarith
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [hae] with x hx
    simp [respCoeffPlus, hx]

/-- The same datum at the cutoff bound's own grid, from its own premises:
`2 * d ≤ 3 ^ jStar` and positive definiteness of the canonical metric. -/
theorem exists_elliptic_representative_respCell_respCoeffMinus {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        respCoeffMinus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f :=
  exists_elliptic_representative_respCoeffMinus (respGrid jStar F)
    (Geometry.isUnit_roundedGrid hjStar hm) t F a

/-- The plus twin of the previous. -/
theorem exists_elliptic_representative_respCell_respCoeffPlus {jStar : ℕ}
    (hjStar : 2 * d ≤ 3 ^ jStar) {F : BlockMat d} (hm : (explicitCanonicalMetric F).PosDef) (t : ℤ)
    (a : CoeffSpace d) :
    ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        respCoeffPlus F a =ᵐ[volumeMeasureOn (respCell jStar F t)] f :=
  exists_elliptic_representative_respCoeffPlus (respGrid jStar F)
    (Geometry.isUnit_roundedGrid hjStar hm) t F a

/-! ## The pulled-back flux is `L²` for the normalized reference-cube measure -/

/-- **The flux slot of the pulled-back centred optimizer field.**  The field
`y ↦ q⁻¹ ((optimizerField b u (q y) − Y).2)` is square integrable for
the normalized measure of the reference cube — the `hflux` slot of the generic CG product bridge
`abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct`
(`Book/Ch05/.../JUpperBoundWeakNorms/Product/Bridge.lean`), whose potential slot is
`respCenteredPullbackH1` (`H1LinearPullback.lean`).

The elliptic datum is taken in the a.e.-representative form produced by
`exists_elliptic_representative_respCoeffMinus`/`…Plus` above, so the cutoff bound needs no ellipticity
hypothesis of its own. -/
theorem memLp_two_normalizedCubeMeasure_pullback_flux {q : Mat d} (hq : IsUnit q) (t : ℤ)
    {lam Lam : ℝ} {b f : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q t) f)
    (hbf : b =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)] f)
    (u : AHarmonicFunction b (HighContrast.adaptedCell q t)) (Y : BlockVec d) :
    MemLp (fun y => matVecMul q⁻¹ ((optimizerField b u (matVecMul q y) - Y).2)) 2
      (normalizedCubeMeasure (originCube d t)) := by
  classical
  have hconv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) :=
    adaptedCell_isOpenBoundedConvexDomain q hq t
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  -- The flux of the ELLIPTIC REPRESENTATIVE is `L²` on the cell (CG, `CoefficientField.lean`).
  have hfluxf : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => matVecMul (f x) (u.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1.grad_memVectorL2
  -- a.e. equality on the cell transfers it to the coefficient itself, and the constant `Y.2` is
  -- `L²` because the cell has finite measure.
  have hae : (fun x => matVecMul (f x) (u.toH1.grad x))
      =ᵐ[volumeMeasureOn (HighContrast.adaptedCell q t)]
        fun x => matVecMul (b x) (u.toH1.grad x) := by
    filter_upwards [hbf] with x hx
    rw [hx]
  have hfluxb : MemVectorL2 (HighContrast.adaptedCell q t)
      (fun x => (optimizerField b u x - Y).2) :=
    ((memLp_congr_ae hae).mp hfluxf).sub (memLp_const Y.2)
  -- coordinatewise, then pull back along `x = q y` with the post-composition `q⁻¹`
  have hG : GradMemL2On (HighContrast.adaptedCell q t) (fun x => (optimizerField b u x - Y).2) :=
    fun i => (memLp_pi_iff.mp hfluxb) i
  have hpull : GradMemL2On (openCubeSet (originCube d t))
      (fun y => matVecMul q⁻¹ ((optimizerField b u (matVecMul q y) - Y).2)) :=
    gradMemL2On_matVecMul_comp_matVecMul hq q⁻¹
      (image_openCubeSet_originCube_eq_adaptedCell q t).subset hG
  exact MemLp.of_eval fun i => memL2On_openCubeSet_normalizedCubeMeasure (hpull i)

end

end Homogenization.HighContrast.Multiscale
