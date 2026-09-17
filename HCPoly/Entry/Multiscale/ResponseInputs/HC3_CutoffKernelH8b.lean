import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffKernelH8a

/-!
# HC3_CutoffKernel, part 2 of 3

Continuation of `HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffKernel`, split at declaration boundaries so that
no module exceeds the 800-line isolation cap of
`scripts/check_isolation.py`.  Declaration statements, bodies and names
are unchanged; `private` is dropped only where a declaration is used from
a later part of the chain, since module privacy does not survive an import.
-/

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory
open Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! **GAP 1 of the integrability premise: PROVED, and the generic form REFUTED.**

The bound needed here is the squared scale-average seminorm bound for the doubled optimizer
state.  It holds, for the two recentred response coefficients, by chaining the linearity of the
cell average, the Jensen/partition bound and the square integrability of the
doubled state on the cell.

It is NOT available for an arbitrary coefficient family `c : CoeffSpace d → CoeffField d`, and
the generic statement is false: if the flux slot `c a ⋅ ∇v` fails to be square integrable on the
cell, the right-hand side is the Bochner junk value `0`
(`cellMeanSq_eq_zero_of_not_integrable`) while the left-hand side, whose gradient slot is an
honest average of an `L²` field, need not vanish; the resulting collapse is
`eq_zero_of_sq_le_cellMeanSq_of_not_integrable`.  The proof below therefore splits on the
hypothesis that the coefficient family is one of the two recentrings. -/

/-! **The `L¹(P)` envelope of the weak quantity: PROVED, and the `cellMeanSq` route ABANDONED.**

The bound needed here -- `P`-integrability of the pathwise `M_0`-energy
`cellMeanSq U_t (M_0^{1/2}(X_t - Y))` of the doubled optimizer state -- is NOT available, and not
for want of a proof: the `M_0`-energy of the state is the `L²(U_t)` norm of the GRADIENT and of the
FLUX separately, and in the high-contrast class those are not controlled by the coarse block.  A
one-dimensional sample with conductivity `δ` on a set of measure `δ` has `⟨a⁻¹⟩ = 2` -- so its
coarse block, and every moment of it, is bounded uniformly in `δ` -- while the gradient energy of
its response maximizer is of order `δ⁻¹`; a law with a heavy tail in `δ⁻¹` therefore satisfies
`e.coarse.ellipticity` with a non-integrable `M_0`-energy.

The scale-average seminorm, however, never sees the pointwise state: it sees only the cell averages
of the state over the triadic subcells, and those ARE controlled, by the Fenchel inequality dual to
AK.HC (2.15) on each subcell together with the all-scale coarse-block bound of
`p.response.transfer`.  That is the route taken below: it dominates the seminorm square
by `C ((1 + ℳ) J + 1)` with `ℳ` the all-scale maximum and `J` the pathwise response, both of which
the standing assumptions make square integrable.  The private helper is therefore gone, and with it
the `cellMeanSq` detour; see `HC3_CutoffWeakFromRaw.lean` and the modules it names. -/

/-! **The measurability of the weak-quantity integrand: PROVED.**

A response maximizer is unique up to a null set in its gradient, so the cell averages entering the
scale-average seminorm are those of the canonical Chapter-2 maximizer, which depends measurably on
the sample; and the seminorm is a sum of measurable terms.  This is
`aestronglyMeasurable_besovSeminorm_sq_of_maximizer` (`HC3_CutoffSupportMeasFamily.lean`), which
consumes the maximizer hypothesis and the identification of the coefficient family — both of which
the caller below already carries, and neither of which the deleted generic form had.  For an
arbitrary family of `AHarmonicFunction`s, with no maximizer hypothesis, measurability is not
available and the generic statement is false. -/

/-- **The integrability premise of `e.response.weak.estimate`, PROVED.**

`respWeakEnergy` is the supremum of the numbers `3^{-t} E[[M_0^{1/2}(X_t - Y)]^2]`, and Bochner
integration returns `0` on a non-integrable integrand, so the cutoff estimate is only informative
once the squared scale-average seminorm of the doubled optimizer state is `P`-integrable.  That is
what this theorem supplies, from the standing assumptions on the law alone.

The two measurability premises are the all-scale maximum `ℳ` of `p.response.transfer`
in `L^Q(P)`; they are produced once and for all by
`respAllScaleMax_aestronglyMeasurable_integrable` and discharged at the sole call site.  The
dimension premise `2 ≤ d` is the one the coarse-ellipticity source chain carries; it too is
discharged at the call site, which already assumes it.

The proof is the almost sure envelope of `HC3_CutoffWeakDomination.lean` -- the subcell Fenchel
inequality dual to AK.HC (2.15), the all-scale coarse-block bound, exact partition averaging and
the geometric summation of the scale-average seminorm -- integrated against the law by
`HC3_CutoffWeakIntegrable.lean`; the majorant `(1 + ℳ) J + 1` is integrable by Cauchy-Schwarz,
since `ℳ` has all moments up to `Q` and the recentred pathwise response is square integrable. -/
theorem integrable_besovSeminorm_sq_respCell (d : ℕ) [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (c : CoeffSpace d → CoeffField d)
    (_hc : c = respCoeffMinus F ∨ c = respCoeffPlus F) (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (_hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a)) :
    Integrable (fun a => besovSeminorm t (fun n z =>
      blockMatVecMul (blockSqrt (respM0 F))
        (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (c a) (u a)) - Y)) ^ 2) P := by
  have := _raw.prob
  -- The selected grid is invertible (`RawOutput.hj/symm/pos`).
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef _raw.symm _raw.pos
  rcases _hc with rfl | rfl
  · exact integrable_besovSeminorm_sq_of_raw_minus hd γ _raw.ell.g_mem P E Ψ Kg Src _raw.stat
      _raw.ell jStar _raw.hj F hm t p q' Y hMint hMmeas
      (integrable_respJ_sq_respCoeffMinus_of_dagger P γ E Ψ Kg Src _raw.stat _raw.ell jStar
        _raw.hj F hm t p q') u _hu
  · exact integrable_besovSeminorm_sq_of_raw_plus hd γ _raw.ell.g_mem P E Ψ Kg Src _raw.stat
      _raw.ell jStar _raw.hj F hm t p q' Y hMint hMmeas
      (integrable_respJ_sq_respCoeffPlus_of_dagger P γ E Ψ Kg Src _raw.stat _raw.ell jStar
        _raw.hj F hm t p q') u _hu

/-! ### The metric dichotomy that makes the pullback estimates applicable under the hypotheses of `p.response.transfer`.

The pullback estimates all carry `hm : m.PosDef` for `m = explicitCanonicalMetric F`, while the
response-transfer estimate quantifies over a
BARE `F : BlockMat d` (the `PosDef` fact is `Geometry.explicitCanonicalMetric_posDef`, which consumes
`raw.symm`/`raw.pos` of `RawOutput`, available to the CALLER `AdaptedCutoff.lean` but not
inside that estimate).  This is NOT a hypothesis deficiency: the missing case
is empty on the left-hand side.  Indeed `explicitCanonicalMetric F` is `X⁻¹` for
`X = (ofFullBlockMat (matSqrt · * matSqrt · * matSqrt ·)).lowerRight`, and `matSqrt` is
positive semidefinite on EVERY input (on non-`PosSemidef` data it
takes its junk value `1`), so `X` is positive semidefinite and `explicitCanonicalMetric F` is either
positive definite (when `X` is invertible) or singular.  In the singular case
`(explicitCanonicalMetric F)⁻¹ = 0`, so the selected grid `respGrid jStar F = explicitRoundedGrid jStar
(explicitCanonicalMetric F)` -- whose every entry carries the factor `sqrt ‖m⁻¹‖` -- is the ZERO matrix,
its determinant vanishes, the adapted cell is
Lebesgue-null and the left-hand side of the response-transfer estimate is `0`.

Positive semidefiniteness of `explicitCanonicalMetric F` itself, i.e. preservation of `PosSemidef` by
`A * B * A`, by the lower-right principal block and by `Matrix.inv`, is NOT
formalized here. -/

/-! ### The change of variables `x = q y` of `p.response.transfer`.

`hc3CutoffPairingOnCell` lives on the adapted cell `U_t = q ⋄_t`; the reference-cube product-term
bound and the two pullback seminorm bounds live on the reference cube `originCube d t`.  The bridge
is the pullback `x = q y`, which is exact on volume
averages (`cubeAverage_comp_matVecMul`, `HC2_WeakSeminorm.lean`) and which distributes the
grid between the two slots of the pairing through the adjoint identity `⟨qᵀ v, q⁻¹ w⟩ = ⟨v, w⟩`:
the two pulled-back slots are then LITERALLY the fields `fun y => qᵀ (X (q y)).1` and
`fun y => q⁻¹ (X (q y)).2` whose partial Besov seminorms are bounded by the pullback lemmas
(`partialSeminorm_pullback_fst_le` / `partialSeminorm_pullback_snd_le`, with `X` the centred
field `fun x => optimizerField b u x - Y`).  No estimate is used here; this step is an identity. -/

/-! ### The two steps that do NOT depend on the AK.HC (A.4) transport.

The two private lemmas below are the outer shell of the response-transfer estimate
(`p.response.transfer`): the
degenerate branch and the integration in `a`.  Together they reduce the response-transfer estimate
to the SINGLE pathwise
estimate

`|(φ (X_a - Y) · (X_a - Y))_{U_t}| ≤ C₀ * (3 ^ (-t) * ‖M₀^{1/2}((X_a)_· - Y)‖_{B,t} ^ 2)` (P1)

for each sample `a` on a NONSINGULAR grid, which is the remaining analytic content (the change
of variables `x = q y` of `p.response.transfer` composed with the pullback estimates and AK.HC Lemma A.1 (A.4)).
Nothing below assumes (P1); the reduction is unconditional. -/

/-- **The response-transfer estimate** (`p.response.transfer`).  Integration by parts, the cutoff functional
estimate, and the direct full-dual pairing of AK.HC Lemma A.1 (A.4) give
`E[|(φ (∇v_t^± - P^±) · (a_± ∇v_t^± - Q^±))_{U_t}|] ≤ C W^±`,
with a constant `C` that is independent of the eccentricity of the grid: the comparison of the
rounded and unrounded metrics costs only the dimensional factor
`|m^{-1/2}q| |q^{-1}m^{1/2}| ≤ 3` of `p.response.transfer`, and the pullback `x = q y` preserves
normalized cell averages and their Besov sums.

`W^±` is `respWMinus`/`respWPlus` (`AdaptedDefs.lean`); `(P^±, Q^±) = Y^±` is
`respYMinus`/`respYPlus`; the cutoff class is `IsResponseCutoff`.

The cutoff-product estimate consumes
`ContDiff R (top : N-infty) phi`, `HasCompactSupport phi`, `tsupport phi subseteq openCubeSet Q`
and a bound `B` on the derivative of `scalarCutoffGradientField phi` -- i.e. SMOOTHNESS and a
SECOND-derivative scale -- while a cutoff class recording only nonnegativity, the bound `2`, the
support, the mean and a FIRST-order Lipschitz constant, with a piecewise linear witness, does not
suffice.  `IsResponseCutoff` (`AdaptedDefs.lean`) therefore carries exactly the four additional
conjuncts (`ContDiff`, `HasCompactSupport`, `tsupport phi subseteq adaptedCell qq t`, and the
pullback second-derivative bound `1024 * d ^ 4 * Theta ^ 2 * 3 ^ (-2 * t)`), and
`exists_isResponseCutoff` above constructs a genuinely SMOOTH member of that class out of
`QuantitativeCubeCutoff.canonicalFun` and `smoothTransitionProfile` of the pinned CoarseGraining
package.  See the `IsResponseCutoff` docstring: the two coefficients carry the universal profile
factor `Theta >= 1`, which no choice of the recorded numerals avoids, since
`derivBound = secondDerivBound = 1` is satisfied by no smooth profile and bounded by nothing in the
pinned package.

The hypothesis is not deficient, so the reference-cube product-term bound applies; the remaining analytic transport is the change
of variables `x = q y` of `p.response.transfer` carrying `hc3CutoffPairingOnCell` on `U_t` to
`cutoffProductTermOnCube` on the reference cube, composed with the pullback estimates
(`partialSeminorm_pullback_fst_le`, `partialSeminorm_pullback_snd_le`,
`explicitRoundedGrid_metricFrobenius_product_le`, all in `HC2_WeakSeminorm.lean`) and the integration in
`a`.

The statement carries, once per sign, the integrability of the Besov square of the family whose
cutoff pairing it bounds -- the integrand of `respWeakEnergySet` (`HC1_DomainBridge.lean`)
itself, which is the weakest form the proof can use and the form the caller can state.  The
hypothesis is necessary: without it the statement is false, since on a family whose Besov square
is not `P`-integrable Bochner returns `0`, `respWeakEnergySet` is a subsingleton, `W^± = 0`, and
the left-hand side can still be positive.  The caller (`AdaptedCutoff.lean`) discharges both from
`integrable_besovSeminorm_sq_respCell` above.

The statement carries `2 * d ≤ 3 ^ jStar`.  Without it the selected grid `q = respGrid jStar F`
need not be invertible -- the only route to `IsUnit (explicitRoundedGrid jStar m)` in the tree is
`Geometry.isUnit_roundedGrid` (`HCPoly/Entry/Geometry/RoundedGrid.lean`), which consumes exactly this
premise -- so the change of variables `x = q y` of `p.response.transfer`, and with it the pullback of the
potential, are unavailable at ANY constant, whatever one is willing to pay.  The premise is
discharged at the sole caller (`AdaptedCutoff.lean`) by `raw.hj`, the very hypothesis that already
supplies the grid's invertibility there, so nothing downstream pays for it.  It is needed only on
the `PosDef` branch; the `¬PosDef` branch is killed by the vanishing of the grid for a singular
metric.

A separate ellipticity hypothesis `IsEllipticFieldOn lam Lam (adaptedCell q t) b` is NOT needed.
Although the coefficient of the response-transfer estimate is the bare `respCoeffMinus F a` and carries no ellipticity, that
hypothesis is DERIVABLE, for both signs, from the sample's own qualitative local uniform
ellipticity together with the invertibility that the new premise above already provides: see
`exists_elliptic_representative_respCoeffMinus` / `…Plus` and
`memLp_two_normalizedCubeMeasure_pullback_flux` in
`HCPoly/Entry/Multiscale/ResponseInputs/H8bEllipticInput.lean`, which close the `hflux` slot of the generic
CG product bridge outright.  The response-transfer estimate therefore takes no ellipticity binder. -/
theorem integral_abs_hc3CutoffPairingOnCell_le_respWeak (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] (jStar : ℕ) (F : BlockMat d)
        (t : ℤ) (e : Vec d) (φ : Vec d → ℝ),
        -- Without this the selected grid `q = respGrid jStar F` need not be
        -- invertible, so the change of variables `x = q y` of `p.response.transfer` is unavailable at
        -- ANY constant; see the paragraph in the docstring above.
        2 * d ≤ 3 ^ jStar →
        IsResponseCutoff (respGrid jStar F) t φ →
        ∀ uM : (a : CoeffSpace d) →
            AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqMinus P jStar F t e) (respCoeffMinus F a) (uM a)) →
          -- The Besov square of this family must be `P`-integrable, otherwise the
          -- Bochner integral defining `W^-` collapses to `0` while the left-hand side stays
          -- positive; see `integrable_besovSeminorm_sq_respCell` above.
          Integrable (fun a => besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                  (optimizerField (respCoeffMinus F a) (uM a)) -
                respYMinus P jStar F t e)) ^ 2) P →
        ∀ uP : (a : CoeffSpace d) →
            AHarmonicFunction (respCoeffPlus F a) (respCell jStar F t),
          (∀ a, IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
            (respqPlus P jStar F t e) (respCoeffPlus F a) (uP a)) →
          Integrable (fun a => besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                  (optimizerField (respCoeffPlus F a) (uP a)) -
                respYPlus P jStar F t e)) ^ 2) P →
        (∫ a, |hc3CutoffPairingOnCell (respCell jStar F t) φ (respYMinus P jStar F t e)
              (respCoeffMinus F a) (uM a)| ∂P) ≤ C * respWMinus P jStar F t e ∧
          (∫ a, |hc3CutoffPairingOnCell (respCell jStar F t) φ (respYPlus P jStar F t e)
              (respCoeffPlus F a) (uP a)| ∂P) ≤ C * respWPlus P jStar F t e := by
  obtain ⟨C₀, hC₀, hpath⟩ := exists_pathwise_cutoff_pairing_bound d
  exact exists_pos_const_integral_abs_pairing_le_respWeak d C₀ hC₀ hpath

/-! ### Collapse diagnostics for the cutoff estimate.

`respEJMinus/Plus` (`AdaptedDefs.lean`) and both scale integrals inside
`respTauMinus/Plus` are Bochner integrals of `a ↦ respJ … (respCoeffMinus F a)`,
and the fourth summand of the cutoff estimate is a Bochner integral of `a ↦ |hc3CutoffPairingOnCell …|`.
Nothing in the cutoff estimate's premises forces any of them to be `Integrable`: a point of
`CoeffSpace d` is only QUALITATIVELY locally uniformly elliptic (`HCPoly/Setup/CoefficientSpace.lean`
-- the ellipticity constants are quantified INSIDE the predicate, per sample), so on a general `P`
the map `a ↦ respJ …` is unbounded and need not even be a.e.-strongly measurable.  On such a `P`
all of these integrals take the Bochner junk value `0` (`MeasureTheory.integral_undef`), the entire
right-hand side of the cutoff estimate collapses to `0`, and the estimate then FORCES
`Jtilde^-(e) = 0`.  But `respCenteredJMinus` (`AdaptedDefs.lean`) is a purely algebraic
function of `adaptedMean P (respGrid jStar F) t`, i.e. of the four ENTRYWISE integrals of the
coarse block (`HCPoly/Entry/Setup/Response.lean`), which do not collapse together with the response
integrals: a law with uniformly bounded upper ellipticity and degenerating lower ellipticity keeps
`(adaptedMean P q t).upperLeft` finite while `respJ` blows up.  The lemmas below are half of that
argument; the construction of the law itself is not carried out here.
This is the same integrability obstruction as the one for the response-transfer estimate. -/

/-! ### The integrability premises of the cutoff estimate.

Both statements below consume `raw` and are the cutoff-estimate analogues of
`integrable_besovSeminorm_sq_respCell` above (the integrability hypothesis of the response-transfer
estimate).  They record
the premises the cutoff estimate now carries as explicit obligations on the law, rather than
folding them into the estimate itself (which would make it false -- see the collapse diagnostics
above) or leaving them unstated inside `response_cutoff_estimate`.

Why they cannot be discharged here from the available hypotheses.
`Annealed.responseJ_eq_coarseBlock_adapted` (`HCPoly/Entry/Annealed/AdaptedDomainRecovery.lean`) turns
`ResponseJ (adaptedCellTranslate q j y) p r (a.1)` into the fixed quadratic
`(1/2) (-p, r). A(U; a) (-p, r) - p. r` in the coarse block, and the coarse block IS entrywise
`P`-integrable under `raw` (`Annealed.hasIntegrableCoarseBlock_adapted`, from `raw.stat`,
`raw.ell`, `raw.hj`).  That would settle integrability immediately -- but the cutoff estimate's
integrands are `respJ... (respCoeffMinus F a)` and `respJ... (respCoeffPlus F a)`, i.e. the
RECENTRED fields `a - g` and `a^t + g` of `p.response.transfer`, and
`responseJ_eq_coarseBlock_adapted` is available only for members of the coefficient carrier: its
proof goes through `exists_elliptic_representative_adapted`, and a recentred field need not be
elliptic at all.  Supplying the recentred avatar of that identity (equivalently, the ellipticity of
`a_±` that the self-dual recentring of Step 4 is supposed to provide) is the content of these two
statements. -/

/-- **The pathwise-response integrability premise of the cutoff estimate.**
`respEJMinus/Plus` (`AdaptedDefs.lean`) and both scale integrals inside
`respTauMinus/Plus` are Bochner integrals of `a => respJ... (respCoeffMinus F a)`;
without integrability they take the junk value `0`, the entire right-hand side of the cutoff
estimate collapses and the estimate forces `Jtilde^±(e) = 0`.  The cutoff estimate therefore
carries the four instances `u ∈ {s, t}` × `sign ∈ {-, +}` of this statement, and the caller
discharges them from here. -/
theorem integrable_respJ_respCell (d : ℕ) [NeZero d] (γ : ℝ) (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (c : CoeffSpace d → CoeffField d)
    (_hc : c = respCoeffMinus F ∨ c = respCoeffPlus F) (u : ℤ)
    (_hlo : (jStar : ℤ) ≤ u) (_hhi : u ≤ t) (p q' : Vec d) :
    Integrable (fun a => respJ (respGrid jStar F) u p q' (c a)) P := by
  have := _raw.prob
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef _raw.symm _raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid _raw.hj hm
  have hint : HasIntegrableCoarseBlock P (respCell jStar F u) :=
    hasIntegrableCoarseBlock_respCell P γ E Ψ Kg Src _raw.stat _raw.ell jStar _raw.hj F hm u
  rcases _hc with rfl | rfl
  · exact integrable_respJ_respCoeffMinus P jStar F u hq hint p q'
  · exact integrable_respJ_respCoeffPlus P jStar F u hq hint p q'

/-- **The cutoff-pairing integrability premise of the cutoff rows, PROVED.**
The fourth summand of each row of the cutoff estimate is `∫ |hc3CutoffPairingOnCell...| ∂P`, which
is `0` on a non-integrable integrand; that is the `E4 = 0` input of the collapse lemma, and the
weak-quantity bound does not supply it,
being itself true, vacuously, with both sides `0` in the bad case.

The two ingredients are now available.  The pathwise cutoff estimate dominates the absolute pairing
by a fixed multiple of the squared scale-average seminorm, whose integrability is
`integrable_besovSeminorm_sq_respCell` above; and the pairing is almost everywhere strongly
measurable in the sample, because a response maximizer is determined almost everywhere by the
canonical Chapter-2 one, whose cutoff-weighted readouts -- the three linear ones and the quadratic
one -- are measurable through the Galerkin selection.  The two measurability premises on the
all-scale maximum and the dimension premise are those of `integrable_besovSeminorm_sq_respCell`,
and are discharged at the same call site. -/
theorem integrable_abs_hc3CutoffPairingOnCell (d : ℕ) [NeZero d] (hd : 2 ≤ d) (γ : ℝ)
    (S : SelectionData)
    (ε σ Cglob Cprof Csrc Bresp : ℝ) (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (Ψ : ℝ → ℝ) (Kg : ℝ) (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ)
    (_raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (hMmeas : AEStronglyMeasurable (respAllScaleMax P γ jStar F t) P)
    (hMint : Integrable (fun a => respAllScaleMax P γ jStar F t a ^ bigQ d γ) P)
    (c : CoeffSpace d → CoeffField d)
    (_hc : c = respCoeffMinus F ∨ c = respCoeffPlus F) (φ : Vec d → ℝ)
    (_hφ : IsResponseCutoff (respGrid jStar F) t φ) (p q' : Vec d) (Y : BlockVec d)
    (u : (a : CoeffSpace d) → AHarmonicFunction (c a) (respCell jStar F t))
    (_hu : ∀ a, IsResponseMaximizer (respCell jStar F t) p q' (c a) (u a)) :
    Integrable (fun a =>
      |hc3CutoffPairingOnCell (respCell jStar F t) φ Y (c a) (u a)|) P := by
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef _raw.symm _raw.pos
  have hq : IsUnit (respGrid jStar F) := Geometry.isUnit_roundedGrid _raw.hj hm
  have hbesov := integrable_besovSeminorm_sq_respCell d hd γ S ε σ Cglob Cprof Csrc Bresp H P E Ψ
    Kg Src B jStar F s t _raw hMmeas hMint c _hc p q' Y u _hu
  have hmeas := aestronglyMeasurable_abs_pairing_of_maximizer P jStar F t _raw.hj hm c _hc
    p q' Y _hφ u _hu
    ((measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffMinus_full
      (respGrid jStar F) (Geometry.isUnit_roundedGrid _raw.hj hm) t F p q' _hφ).aestronglyMeasurable)
    ((measurable_volumeAverage_cutoff_quadratic_canonicalRespCoeffPlus_full
      (respGrid jStar F) (Geometry.isUnit_roundedGrid _raw.hj hm) t F p q' _hφ).aestronglyMeasurable)
  have hrep : ∀ a : CoeffSpace d, ∃ (lam Lam : ℝ) (f : CoeffField d), 0 < lam ∧ lam ≤ Lam ∧
      IsEllipticFieldOn lam Lam (respCell jStar F t) f ∧
        c a =ᵐ[volumeMeasureOn (respCell jStar F t)] f := by
    rcases _hc with rfl | rfl
    · exact fun a => exists_elliptic_representative_respCell_respCoeffMinus _raw.hj hm t a
    · exact fun a => exists_elliptic_representative_respCell_respCoeffPlus _raw.hj hm t a
  have _ := hq
  simpa only [hc3CutoffPairingOnCell] using
    integrable_abs_pairing_of_measurable_of_integrable_besov P jStar F t φ _raw.hj _hφ hm c hrep
      Y u hmeas hbesov

end

end Homogenization.HighContrast.Multiscale
