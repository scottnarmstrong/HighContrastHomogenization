/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Mathlib

/-!
# Theorem C: quantitative homogenization under uniform ellipticity

Theorem C of *Homogenization at a polynomial scale in high contrast*
(`t.uniform.homogenization`), restated over Mathlib alone.

## The theorem in words

Fix a dimension `d ≥ 2`.  There are an exponent `κ > 0`, a constant `C > 0`, a
shape constant `C₀` of the adapted domain and a constant `C₁` of the regularity
exponent such that every law `P` satisfying the standing assumptions produces a
homogenized matrix `ā` with positive definite symmetric part `s̄`, a
homogenization scale `X ≥ 1` with the tail
`P[X ≥ C (2 + Λ/λ)^C t] ≤ exp(-t^d)` of `e.uniform.scale.tail`, and a corrector
family `(Φ_e, ∇Φ_e)` linear in the slope `e` and stationary under the integer
translations.  On one translation-invariant event of full probability, and with
the same scale and the same family throughout, the following hold:

* the Dirichlet estimate, in the homogeneous negative-Sobolev form on the
  adapted cells of `ā`;
* the corrector equation and the corrector estimate;
* the Liouville classification, as a double inclusion;
* the large-scale energy estimate `e.uniform.energy` and the first-order
  approximation, both on the ellipsoids `e.homogenized.ellipsoids`.

The homogenization length is polynomial in the ellipticity ratio: the tail
exponent is the dimension and the deterministic factor is a power of `2 + Λ/λ`.
The shape constant `C₀` depends on nothing but the dimension, the regularity
exponent and the radii of two concentric balls trapping `s̄^{-1/2}U`, so its
binder stands outside the ellipticity constants and outside the law.

## Standing assumptions

`P` is a probability law on the coefficient space `Ω` of measurable coefficient
fields modulo equality almost everywhere, qualitatively locally uniformly
elliptic.  It is stationary under the integer translations of `ℝ^d`, has unit
range of dependence — the local `σ`-fields of two sets at supremum distance at
least one are independent — and is almost surely `(λ, Λ)`-elliptic in the sense
of `e.uniform.ellipticity`, with `0 < λ ≤ 1 ≤ Λ`.

## Presentation deltas

* **Symbols.**  The paper's `ā`, `s̄`, `𝒳` and `φ_e` are here `abar`,
  `symmPart abar`, `X` and `Phi`, with gradients `gradPhi`; only the spelling
  changes.
* **Where the conclusion comes from.**  The paper obtains most of the clauses
  from `t.random.homogenization`; here the conclusion is that of
  `t.random.homogenization` at exponent zero, with the two-part tail collapsed
  to `exp(-t^d)` and the length a power of `2 + Λ/λ`.
* **The Dirichlet clause.**  The paper states the `L²` estimate
  `e.uniform.dirichlet`; here the homogeneous negative-Sobolev estimate of
  `t.random.homogenization` on the adapted cells, the duality argument from one
  to the other not being formalized.
* **The homogenized matrix.**  The paper identifies `ā` with the matrix of
  `t.algebraic.convergence`; here it is produced existentially, which is weaker
  and leaves nothing in the statement depending on the choice.
* **The flux differences.**  The paper writes them with the full homogenized
  matrix; here for the skew-centred field, `k̄` being subtracted from `a`, a
  recentering that changes neither the solutions nor the coarse-grained blocks.
* **The ellipsoids.**  The paper writes `E_r` with a strict inequality; here it
  is closed, and the two sets differ by a Lebesgue-null boundary.
* **Values in `ℝ≥0∞`.**  The paper writes norms and energies as real numbers;
  here they are valued in `ℝ≥0∞`, infinite exactly where the printed quantity
  is rather than totalized to zero there.
* **The membership classes.**  The printed classes are completions of smooth
  functions in a norm; here each also carries the measurability that such a
  completion presupposes, and the approximants are globally smooth.
* **The two ellipticity conditions.**  The carrier already carries the
  qualitative condition, whose constants are quantified inside the predicate;
  the `λ` and `Λ` of `e.uniform.ellipticity` are a separate hypothesis, and no
  constant of the conclusion sees the qualitative pair.
* **Positive constants.**  The paper asserts that `C`, `C₀` and `C₁` are finite;
  here they are asserted positive as well, which is a normalization.
* **The invariant event.**  The paper does not record the behaviour of the
  full-probability event under translations; here its invariance under the
  integer translations is part of the conclusion.

The only omitted proof is the proof of the theorem.
-/

namespace HCPoly.StatementAudit.UniformHomogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Ambient vectors and matrices

This statement names no coarse-grained block, so only the `d × d` matrices are
needed, together with the Loewner order, read as the inequality of the
associated quadratic forms.
-/

/-- The ambient space `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- The `d × d` real matrices. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The Euclidean inner product on `ℝ^d`. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ := ∑ i, x i * y i

/-- The squared Euclidean norm on `ℝ^d`. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ := vecDot x x

/-- Matrix–vector multiplication. -/
def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d := fun i => ∑ j, A i j * x j

/-- The symmetric part `s = ½(a + aᵗ)` of a matrix. -/
def symmPart {d : ℕ} (A : Mat d) : Mat d := fun i j => (A i j + A j i) / 2

/-- The antisymmetric part `k = ½(a - aᵗ)` of a matrix. -/
def skewPart {d : ℕ} (A : Mat d) : Mat d := fun i j => (A i j - A j i) / 2

/-- The Loewner order `A ≤ B` on matrices, as the inequality of the forms `½ x · A x`. -/
def MatLoewnerLE {d : ℕ} (A B : Mat d) : Prop :=
  ∀ x : Vec d,
    (1 / 2 : ℝ) * vecDot x (matVecMul A x) ≤
      (1 / 2 : ℝ) * vecDot x (matVecMul B x)

/-- The scalar Loewner bound `|M| = inf {t ≥ 0 : M ≤ t I}`, the printed bracket `| · |`. -/
def specBound {d : ℕ} (M : Mat d) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))}

/-- The `i`-th coordinate basis vector of `ℝ^d`. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d := Pi.single i (1 : ℝ)

/-! ## Coefficient fields and the almost-everywhere carrier

The sample space `Ω` of the paper is a set of measurable coefficient fields on
`ℝ^d` subject to `e.qualitative.ellipticity`, carrying the translations
`a ↦ a(· + z)` by `z ∈ ℤ^d` and a law stationary under them.
-/

/-- A measurable representative of a coefficient field `a : ℝ^d → ℝ^{d×d}`. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- Uniform ellipticity of one matrix, the pointwise bounds of `e.uniform.ellipticity`. -/
def IsEllipticMatrix {d : ℕ} (lam Lam : ℝ) (A : Mat d) : Prop :=
  0 < lam ∧
    lam ≤ Lam ∧
    (∀ ξ : Vec d, lam * vecNormSq ξ ≤ vecDot ξ (matVecMul A ξ)) ∧
    (∀ ξ : Vec d, Lam⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul A⁻¹ ξ))

/-- The measurable matrix fields modulo equality almost everywhere, the carrier of `Ω`. -/
abbrev AEField (d : ℕ) := Vec d →ₘ[volume] Mat d

/-- Qualitative local uniform ellipticity of a coefficient field, with constants on every ball. -/
def IsAELocallyUniformlyElliptic {d : ℕ} (b : CoeffField d) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
    ∀ᵐ x ∂volume, x ∈ Metric.ball (0 : Vec d) R → IsEllipticMatrix lam Lam (b x)

/-- Qualitative local uniform ellipticity of a point of the quotient carrier. -/
def AEUniformlyEllipticField {d : ℕ} (a : AEField d) : Prop :=
  IsAELocallyUniformlyElliptic (⇑a : CoeffField d)

/-- The coefficient space `Ω`: qualitatively elliptic fields modulo equality almost everywhere. -/
def CoeffSpace (d : ℕ) : Type := {a : AEField d // AEUniformlyEllipticField a}

/-- The real vector attached to an integer vector. -/
def intTranslation {d : ℕ} (z : Fin d → ℤ) : Vec d := fun i => z i

/-- Integer translation on the quotient carrier, well defined since translation preserves volume. -/
def translateField {d : ℕ} (z : Fin d → ℤ) (a : AEField d) : AEField d :=
  a.compMeasurePreserving (fun x : Vec d => x + intTranslation z)
    (measurePreserving_add_right (volume : Measure (Vec d)) (intTranslation z))

/-- The pointwise description of an integer translation. -/
theorem translateField_ae {d : ℕ} (z : Fin d → ℤ) (a : AEField d) :
    translateField z a =ᵐ[volume] fun x => a (x + intTranslation z) :=
  AEEqFun.coeFn_compMeasurePreserving _ _

/-- Qualitative local uniform ellipticity survives an integer translation. -/
theorem aeUniformlyEllipticField_translateField {d : ℕ} (z : Fin d → ℤ)
    {a : AEField d} (ha : AEUniformlyEllipticField a) :
    AEUniformlyEllipticField (translateField z a) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    ha (R + ‖intTranslation z‖)
      (lt_of_lt_of_le hR (le_add_of_nonneg_right (norm_nonneg _)))
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [translateField_ae z a,
    (measurePreserving_add_right (volume : Measure (Vec d))
        (intTranslation z)).quasiMeasurePreserving.tendsto_ae
      hell] with x hfield hx hxb
  rw [hfield]
  refine hx (mem_ball_zero_iff.2 ?_)
  have hxn : ‖x‖ < R := mem_ball_zero_iff.1 hxb
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith only [hxn])

/-- The translation action `a ↦ a(· + z)` of `ℤ^d` on the coefficient space. -/
def translateCoeff {d : ℕ} (z : Fin d → ℤ) (a : CoeffSpace d) : CoeffSpace d :=
  ⟨translateField z a.1, aeUniformlyEllipticField_translateField z a.2⟩

/-- The rescaled sample coefficient `a^ε(x) = a(x/ε)`. -/
def scaledCoeff {d : ℕ} (ε : ℝ) (a : CoeffSpace d) : CoeffField d := fun x => a.1 (ε⁻¹ • x)

/-! ## The local `σ`-fields and the standing hypotheses on the law

The law is a probability measure on `Ω`, stationary under the integer
translations, with unit range of dependence: the `σ`-fields `F(U)` and `F(V)`
carried by the field inside two sets at distance at least one are independent.
-/

/-- The supremum distance of two points of `ℝ^d`. -/
def supDist {d : ℕ} (x y : Vec d) : ℝ := ‖x - y‖

/-- `dist_∞(U, V) ≥ 1`, in the pointwise form. -/
def UnitSeparated {d : ℕ} (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → 1 ≤ supDist x y

/-- A scalar test function on `U`: the class `C_c^∞(U)`. -/
structure IsLocalTest {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) φ
  hasCompactSupport : HasCompactSupport φ
  tsupport_subset : tsupport φ ⊆ U

/-- The generating linear statistic `a ↦ ∫ e' · a(x) e φ(x) dx` of the local `σ`-field `F(U)`. -/
def coeffPairing {d : ℕ} (e e' : Vec d) (φ : Vec d → ℝ) (a : CoeffSpace d) : ℝ :=
  ∫ x, vecDot e' (matVecMul (a.1 x) e) * φ x ∂volume

/-- The local `σ`-field `F(U)`, generated by the statistics with test function supported in `U`. -/
def coeffSigma (d : ℕ) (U : Set (Vec d)) : MeasurableSpace (CoeffSpace d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (e e' : Vec d) (φ : Vec d → ℝ), IsLocalTest U φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = coeffPairing e e' φ ⁻¹' t}

/-- The global `σ`-field `F = F(ℝ^d)` of the coefficient space. -/
instance instMeasurableSpaceCoeffSpace (d : ℕ) : MeasurableSpace (CoeffSpace d) :=
  coeffSigma d Set.univ

/-- Stationarity of the law: every integer translation preserves `P`. -/
def IsStationaryLaw {d : ℕ} (P : Measure (CoeffSpace d)) : Prop :=
  ∀ z : Fin d → ℤ, Measure.map (translateCoeff z) P = P

/-- Unit range of dependence: the `σ`-fields of two unit-separated sets are independent. -/
def IsUnitRangeLaw {d : ℕ} (P : Measure (CoeffSpace d)) : Prop :=
  ∀ U V : Set (Vec d), MeasurableSet U → MeasurableSet V →
    UnitSeparated U V →
      ProbabilityTheory.Indep (coeffSigma d U) (coeffSigma d V) P

/-! ## Triadic geometry

The cubes of the paper are triadic, `□_m = (-3^m/2, 3^m/2)^d` and its translates
by `3^m ℤ^d`; they enter this statement through the adapted cells of the
homogenized matrix.
-/

/-- A triadic cube, presented by its integer scale and its integer index. -/
structure TriadicCube (d : ℕ) where
  scale : ℤ
  index : Fin d → ℤ

/-- The side length `3^scale` of a triadic cube. -/
def cubeScaleFactor {d : ℕ} (Q : TriadicCube d) : ℝ := (3 : ℝ) ^ Q.scale

/-- The open realization of a triadic cube: side `3^scale`, centre `3^scale` times the index. -/
def openCubeSet {d : ℕ} (Q : TriadicCube d) : Set (Vec d) :=
  { x | ∀ i,
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q < x i) ∧
      (x i < (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) }

/-- The triadic cube of scale `m` centred at the origin. -/
def originCube (d : ℕ) (m : ℤ) : TriadicCube d :=
  { scale := m
    index := 0 }

/-! ## Weak derivatives and the `H¹` classes

`H¹(U)` and `H¹₀(U)` have their usual meaning; a member is carried here as a
function together with a named candidate gradient and the integration-by-parts
identity witnessing that the candidate is the weak gradient.
-/

/-- The weak `i`-th partial derivative on `U`, by integration by parts against test functions. -/
def HasWeakPartialDerivOn {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (u gi : Vec d → ℝ) : Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume =
      -∫ x in U, gi x * φ x ∂volume

/-- The weak gradient on `U`, componentwise. -/
def HasWeakGradientOn {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivOn U i u (fun x => Du x i)

/-- Scalar `L²` membership on `U`. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop := MemLp u 2 (volume.restrict U)

/-- Componentwise `L²` membership of a candidate gradient on `U`. -/
def GradMemL2On {d : ℕ} (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, MemL2On U (fun x => Du x i)

/-- `H¹(U)` through explicit witnesses: a function, its weak gradient, `L²` control on both. -/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  toFun : Vec d → ℝ
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

/-- `H¹₀(U)`: an `H¹(U)` function approximated in that norm from `C_c^∞(U)`. -/
structure H10Function {d : ℕ} (U : Set (Vec d)) extends H1Function U where
  approx : ℕ → Vec d → ℝ
  approx_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (approx n)
  approx_hasCompactSupport : ∀ n, HasCompactSupport (approx n)
  approx_support_subset : ∀ n, tsupport (approx n) ⊆ U
  tendsto_approx :
    Filter.Tendsto
      (fun n => eLpNorm (fun x => approx n x - toH1Function.toFun x) 2
        (volume.restrict U))
      Filter.atTop (nhds 0)
  tendsto_approx_grad :
    ∀ i : Fin d,
      Filter.Tendsto
        (fun n => eLpNorm
          (fun x => (fderiv ℝ (approx n) x) (basisVec i) - toH1Function.grad x i) 2
          (volume.restrict U))
        Filter.atTop (nhds 0)

/-- The volume-normalized integral `⨍_U f`. -/
def volumeAverage {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume

/-! ## Normalized norms, weighted classes, and the Liouville class

The estimates are written in the volume-normalized norms `‖·‖_{L̲²(V)}`,
`‖·‖_{H̲^s(V)}` of `e.physical.fractional.norm`, `‖·‖_{H̲¹(V)}` of
`e.physical.endpoint.norm` and the duals `‖·‖_{H̲^{-s}(V)}` of
`e.physical.negative.norm`, on the coefficient-weighted classes `H¹_s(V)` and
`H¹_a(V)` and on the class of `e.random.liouville.growth`.
-/

/-- The open Euclidean ball of radius `r` centred at `c`. -/
def euclideanBallAt {d : ℕ} (c : Vec d) (r : ℝ) : Set (Vec d) := {x | vecNormSq (x - c) < r ^ 2}

/-- The open Euclidean ball `B_r` centred at the origin. -/
def euclideanBall (d : ℕ) (r : ℝ) : Set (Vec d) := euclideanBallAt (0 : Vec d) r

/-- The coordinate gradient of a smooth scalar function. -/
def smoothGrad {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : Vec d := fun i => fderiv ℝ f x (basisVec i)

/-- A vector test function on `U`, the class `C_c^∞(U; ℝ^d)` of `e.physical.negative.norm`. -/
structure IsLocalVecTest {d : ℕ} (U : Set (Vec d)) (ψ : Vec d → Vec d) : Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) ψ
  hasCompactSupport : HasCompactSupport ψ
  tsupport_subset : tsupport ψ ⊆ U

/-- The volume-normalized integral `⨍_V f` of a nonnegative quantity. -/
def eVolumeAverage {d : ℕ} (V : Set (Vec d)) (f : Vec d → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ x in V, f x ∂volume) / volume V

/-- The normalized norm `‖v‖_{L̲²(V)} = (⨍_V |v|²)^{1/2}`. -/
def normalizedL2Norm {d : ℕ} (V : Set (Vec d)) (v : Vec d → ℝ) : ℝ≥0∞ :=
  (eVolumeAverage V fun x => ENNReal.ofReal (v x ^ 2)) ^ (1 / 2 : ℝ)

/-- The normalized norm `‖s^{1/2} F‖_{L̲²(V)}`, through the quadratic form `F · s F`. -/
def weightedGradNorm {d : ℕ} (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  (eVolumeAverage V fun x =>
    ENNReal.ofReal (vecDot (F x) (matVecMul (symmPart (b x)) (F x)))) ^ (1 / 2 : ℝ)

/-- The Gagliardo term of `e.physical.fractional.norm`, with Euclidean distances. -/
def fracSeminormSq {d : ℕ} (V : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) : ℝ≥0∞ :=
  eVolumeAverage V fun x =>
    ∫⁻ y in V, ENNReal.ofReal
      (vecNormSq (F x - F y) /
        Real.sqrt (vecNormSq (x - y)) ^ ((d : ℝ) + 2 * s)) ∂volume

/-- The normalized norm square `‖F‖²_{H̲^s(V)}` of `e.physical.fractional.norm`. -/
def hsNormSq {d : ℕ} (V : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) : ℝ≥0∞ :=
  volume V ^ (-(2 * s) / (d : ℝ)) *
      eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (F x))) +
    fracSeminormSq V s F

/-- The normalized norm square `‖ψ‖²_{H̲¹(V)}` of `e.physical.endpoint.norm`. -/
def h1NormSq {d : ℕ} (V : Set (Vec d)) (ψ : Vec d → Vec d) : ℝ≥0∞ :=
  volume V ^ (-(2 : ℝ) / (d : ℝ)) *
      eVolumeAverage V (fun x => ENNReal.ofReal (vecNormSq (ψ x))) +
    eVolumeAverage V fun x =>
      ENNReal.ofReal (∑ j, vecNormSq (smoothGrad (fun y => ψ y j) x))

open scoped Classical in
/-- The normalized pairing `⨍_V F · ψ`, infinite where `F · ψ` is not integrable on `V`. -/
def dualPairing {d : ℕ} (V : Set (Vec d)) (F ψ : Vec d → Vec d) : ℝ≥0∞ :=
  if IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume then
    ENNReal.ofReal (volumeAverage V fun x => vecDot (F x) (ψ x))
  else ⊤

/-- The dual norm `‖F‖_{H̲^{-s}(V)}` of `e.physical.negative.norm`. -/
def negSobolevNorm {d : ℕ} (V : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → Vec d // IsLocalVecTest V ψ ∧ hsNormSq V s ψ ≤ 1},
    dualPairing V F ψ.1

/-- The endpoint dual norm `‖F‖_{H̲^{-1}(V)}`, the same supremum at `s = 1`. -/
def negOneNorm {d : ℕ} (V : Set (Vec d)) (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ ψ : {ψ : Vec d → Vec d // IsLocalVecTest V ψ ∧ h1NormSq V ψ ≤ 1},
    dualPairing V F ψ.1

/-- The weighted Dirichlet energy `∫_V F · s F`. -/
def sEnergyOn {d : ℕ} (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal (vecDot (F x) (matVecMul (symmPart (b x)) (F x)))
    ∂volume

/-- The norm square `‖u‖²_{H¹_s(V)} = ‖u‖²_{L¹(V)} + ∫_V ∇u · s ∇u` of the weighted class. -/
def h1sNormSqOn {d : ℕ} (b : CoeffField d) (V : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : ℝ≥0∞ :=
  (∫⁻ x in V, ENNReal.ofReal |u x| ∂volume) ^ 2 + sEnergyOn b V Du

open scoped Classical in
/-- The pairing `∫_V ∇φ · k F` of the skew flux against a test gradient. -/
def skewFluxPairing {d : ℕ} (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d) (φ : Vec d → ℝ) : ℝ≥0∞ :=
  if IntegrableOn
      (fun x => vecDot (smoothGrad φ x) (matVecMul (skewPart (b x)) (F x))) V
      volume then
    ENNReal.ofReal
      (∫ x in V, vecDot (smoothGrad φ x) (matVecMul (skewPart (b x)) (F x))
        ∂volume)
  else ⊤

/-- The norm `‖∇·(k F)‖_{H^{-1}_s(V)}` that the graph norm of `H¹_a(V)` adds to `‖·‖_{H¹_s(V)}`. -/
def skewFluxDualNorm {d : ℕ} (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  ⨆ φ : {φ : Vec d → ℝ //
      IsLocalTest V φ ∧ h1sNormSqOn b V φ (smoothGrad φ) ≤ 1},
    skewFluxPairing b V F φ.1

/-- A function and a candidate gradient field for it, both measurable. -/
def IsMeasurableGradientPair {d : ℕ} (μ : Measure (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  AEStronglyMeasurable u μ ∧ ∀ i, AEStronglyMeasurable (fun x => Du x i) μ

/-- Membership of `(u, ∇u)` in `H¹_a(V)`, the smooth completion for the graph norm. -/
def MemH1a {d : ℕ} (b : CoeffField d) (V : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  IsMeasurableGradientPair (volume.restrict V) u Du ∧
    HasWeakGradientOn V u Du ∧
    ∃ v : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n)) ∧
      Filter.Tendsto
        (fun n => h1sNormSqOn b V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n => skewFluxDualNorm b V (fun x => smoothGrad (v n) x - Du x))
        Filter.atTop (nhds 0)

/-- Membership of `(u, ∇u)` in `H¹_{a,0}(V)`, the same completion from `C_c^∞(V)`. -/
def MemH1a0 {d : ℕ} (b : CoeffField d) (V : Set (Vec d)) (u : Vec d → ℝ)
    (Du : Vec d → Vec d) : Prop :=
  IsMeasurableGradientPair (volume.restrict V) u Du ∧
    HasWeakGradientOn V u Du ∧
    ∃ v : ℕ → Vec d → ℝ,
      (∀ n, IsLocalTest V (v n)) ∧
      Filter.Tendsto
        (fun n => h1sNormSqOn b V (fun x => v n x - u x)
          (fun x => smoothGrad (v n) x - Du x)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n => skewFluxDualNorm b V (fun x => smoothGrad (v n) x - Du x))
        Filter.atTop (nhds 0)

/-- Membership of `(v, ∇v)` in `H¹_{s,loc}(ℝ^d)`, the completion condition on every ball. -/
def MemH1sLoc {d : ℕ} (b : CoeffField d) (v : Vec d → ℝ)
    (Dv : Vec d → Vec d) : Prop :=
  IsMeasurableGradientPair volume v Dv ∧
    ∀ R : ℝ, 0 < R →
      HasWeakGradientOn (euclideanBall d R) v Dv ∧
        ∃ w : ℕ → Vec d → ℝ,
          (∀ n, ContDiff ℝ (⊤ : ℕ∞) (w n)) ∧
          Filter.Tendsto
            (fun n => h1sNormSqOn b (euclideanBall d R) (fun x => w n x - v x)
              (fun x => smoothGrad (w n) x - Dv x)) Filter.atTop (nhds 0)

/-- The weak interior equation `-∇·(b F) = 0` in `V`, against the test gradients. -/
def IsWeakSolutionOn {d : ℕ} (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d) : Prop :=
  ∀ φ : Vec d → ℝ, IsLocalTest V φ →
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (b x) (F x))) V
        volume ∧
      ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (b x) (F x)) ∂volume = 0

/-- The class of `e.random.liouville.growth`: entire solutions of `L̲²(B_r)` growth `o(r^{1+ϑ})`. -/
def MemLiouvilleClass {d : ℕ} (b : CoeffField d) (ϑ : ℝ) (v : Vec d → ℝ)
    (Dv : Vec d → Vec d) : Prop :=
  MemH1sLoc b v Dv ∧
    IsWeakSolutionOn b Set.univ Dv ∧
      Filter.Tendsto
        (fun r : ℝ =>
          ENNReal.ofReal (r ^ (-(1 + ϑ))) * normalizedL2Norm (euclideanBall d r) v)
        Filter.atTop (nhds 0)

/-- Membership of `h` in the affine class `g₀ + H¹₀(U)`. -/
def MemAffineH10 {d : ℕ} (U : Set (Vec d)) (g₀ h : H1Function U) : Prop :=
  ∃ w : H10Function U,
    (w.toH1Function.toFun =ᵐ[volume.restrict U]
      fun x => h.toFun x - g₀.toFun x) ∧
    (w.toH1Function.grad =ᵐ[volume.restrict U]
      fun x => h.grad x - g₀.grad x)

/-! ## The adapted geometry of the homogenized matrix

The geometry of the estimates is the one adapted to `s̄`: the ellipsoids `E_r` of
`e.homogenized.ellipsoids`, and the adapted cells `z + s̄^{1/2} □_j` carrying the
Dirichlet estimate.
-/

open scoped Classical in
/-- The positive semidefinite square root: the `B` with `B * B = M`; junk value `1` otherwise. -/
def matSqrt {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : Matrix n n ℝ :=
  if h : ∃ B : Matrix n n ℝ, B.PosSemidef ∧ B * B = M then h.choose else 1

/-- The image of a set under a linear map. -/
def matImage {d : ℕ} (M : Mat d) (U : Set (Vec d)) : Set (Vec d) := matVecMul M '' U

/-- `U` traps, and is trapped by, concentric Euclidean balls of radii `ρ` and `Rad`. -/
def HasBallSandwich {d : ℕ} (U : Set (Vec d)) (ρ Rad : ℝ) : Prop :=
  0 < ρ ∧ 0 ≤ Rad ∧
    ∃ c : Vec d, euclideanBallAt c ρ ⊆ U ∧ U ⊆ euclideanBallAt c Rad

/-- The ellipsoid `E_r = {x : x · s̄⁻¹ x ≤ λ̄⁻¹ r²}` of `e.homogenized.ellipsoids`. -/
def ellipsoid {d : ℕ} (abar : Mat d) (r : ℝ) : Set (Vec d) :=
  {x | vecDot x (matVecMul (symmPart abar)⁻¹ x) ≤
    specBound (symmPart abar)⁻¹ * r ^ 2}

/-! ## The theorem

Each binder group and each conclusion clause is annotated with the content it
restates and, where there is one, the label of the display of the paper.
-/

/-- **Theorem C, `t.uniform.homogenization`: homogenization under uniform ellipticity.** -/
theorem uniform_homogenization
    -- the dimension
    (d : ℕ) (hd : 2 ≤ d) :
    -- the exponent `κ`, the constants `C` and `C₁`, and the shape constant `C₀`,
    -- all chosen before the ellipticity constants and before the law
    ∃ (κ C : ℝ) (C₀ : ℝ → ℝ → ℝ → ℝ) (C₁ : ℝ → ℝ),
      0 < κ ∧ 0 < C ∧ (∀ s₀ ρ Rad : ℝ, 0 < C₀ s₀ ρ Rad) ∧ (∀ ϑ : ℝ, 0 < C₁ ϑ) ∧
      -- the ellipticity constants `0 < λ ≤ 1 ≤ Λ` of `e.uniform.ellipticity`
      ∀ lam Lam : ℝ, 0 < lam → lam ≤ 1 → 1 ≤ Lam →
        -- the law: a probability measure, stationary, of unit range
        ∀ P : MeasureTheory.Measure (CoeffSpace d),
          MeasureTheory.IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          -- almost sure `(λ, Λ)`-ellipticity, `e.uniform.ellipticity`
          (∀ᵐ a ∂P, ∀ᵐ x ∂MeasureTheory.volume,
            IsEllipticMatrix lam Lam (a.1 x)) →
          -- `ā`, the scale `𝒳` and the corrector family `φ_e`
          ∃ (abar : Mat d) (X : CoeffSpace d → ℝ)
            (Phi : Vec d → CoeffSpace d → Vec d → ℝ)
            (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            -- the scale is a measurable random variable, at least one
            Measurable X ∧
            (∀ a, 1 ≤ X a) ∧
            -- the family is linear in the slope
            (∀ (c : ℝ) (e e' : Vec d) (a : CoeffSpace d),
              gradPhi (c • e + e') a
                =ᵐ[MeasureTheory.volume] fun x =>
                  c • gradPhi e a x + gradPhi e' a x) ∧
            -- and stationary under integer translations
            (∀ (z : Fin d → ℤ) (e : Vec d) (a : CoeffSpace d),
              gradPhi e (translateCoeff z a)
                =ᵐ[MeasureTheory.volume] fun x =>
                  gradPhi e a (x + intTranslation z)) ∧
            -- the tail of the homogenization scale, `e.uniform.scale.tail`
            (∀ t : ℝ, 1 ≤ t →
              P.real {a | C * (2 + Lam / lam) ^ C * t ≤ X a} ≤
                Real.exp (-(t ^ (d : ℝ)))) ∧
            -- the symmetric part of the homogenized matrix is positive definite
            (∀ x : Vec d, x ≠ 0 → 0 < vecDot x (matVecMul (symmPart abar) x)) ∧
            -- one translation-invariant event of full probability
            ∃ Ωend : Set (CoeffSpace d),
              MeasurableSet Ωend ∧
              P.real Ωend = 1 ∧
              (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Ωend = Ωend) ∧
              -- (1) the Dirichlet estimate, in the homogeneous negative-Sobolev
              -- form, on the adapted cells of `ā`; the exponent `s ∈ [1/4, 1/2)`
              (∀ s₀ : ℝ, s₀ ∈ Set.Ico (1 / 4 : ℝ) (1 / 2 : ℝ) →
                  -- the domain `U` and the radii of the balls trapping `s̄^{-1/2}U`
                  ∀ (ρ Rad : ℝ) (U : Set (Vec d)),
                    -- `U` is an adapted cell: a translate of `s̄^{1/2} □_j`
                    (∃ j : ℤ, ∃ z : Vec d,
                      U = (fun x : Vec d =>
                        z + matVecMul (matSqrt (symmPart abar)) x) ''
                          openCubeSet (originCube d j)) →
                    -- its shape, seen by the endpoint constant only here
                    HasBallSandwich
                      (matImage ((matSqrt (symmPart abar))⁻¹) U) ρ Rad →
                    -- and its normalization between two adapted ellipsoids
                    U ⊆ ellipsoid abar 1 →
                    ellipsoid abar (1 / (3 * Real.sqrt (d : ℝ))) ⊆ U →
                      -- a sample point and a microscale `ε ≤ 𝒳⁻¹`
                      ∀ a ∈ Ωend, ∀ ε : ℝ, 0 < ε → X a ≤ ε⁻¹ →
                        -- the boundary datum `g ∈ W^{1,∞}(U) ∩ H^{1+s}(U)`
                        ∀ g₀ : H1Function U,
                          (∃ Lg : ℝ, ∀ᵐ x ∂MeasureTheory.volume.restrict U,
                            |g₀.toFun x| +
                              Real.sqrt (vecNormSq (g₀.grad x)) ≤ Lg) →
                          hsNormSq U s₀ g₀.grad ≠ ⊤ →
                          -- the homogenized solution `ū ∈ g + H¹₀(U)`
                          ∀ h : H1Function U,
                            MemAffineH10 U g₀ h →
                            IsWeakSolutionOn (fun _ => abar) U h.grad →
                            -- the heterogeneous solution `u^ε ∈ g + H¹_{a^ε,0}(U)`
                            ∀ (uFun : Vec d → ℝ) (uGrad : Vec d → Vec d),
                              MemH1a0 (scaledCoeff ε a) U
                                (fun x => uFun x - g₀.toFun x)
                                (fun x => uGrad x - g₀.grad x) →
                              IsWeakSolutionOn (scaledCoeff ε a) U uGrad →
                              -- `‖s̄^{1/2}(∇u^ε - ∇ū)‖_{H̲^{-s}(U)}`
                              -- `+ ‖s̄^{-1/2}((a^ε - k̄)∇u^ε - s̄∇ū)‖_{H̲^{-s}(U)}`
                              -- `≤ C₀ (ε𝒳)^κ ‖s̄^{1/2}∇g‖_{H̲^s(U)}`
                              negSobolevNorm U s₀
                                  (fun x => matVecMul (matSqrt (symmPart abar))
                                    (uGrad x - h.grad x)) +
                                negSobolevNorm U s₀
                                  (fun x => matVecMul
                                    (matSqrt (symmPart abar))⁻¹
                                    (matVecMul
                                        (scaledCoeff ε a x - skewPart abar)
                                        (uGrad x) -
                                      matVecMul (symmPart abar) (h.grad x))) ≤
                                ENNReal.ofReal
                                    (C₀ s₀ ρ Rad * (ε * X a) ^ κ) *
                                  hsNormSq U s₀
                                      (fun x => matVecMul
                                        (matSqrt (symmPart abar)) (g₀.grad x)) ^
                                    (1 / 2 : ℝ)) ∧
              -- (2a) the corrector equation `-∇·a(e + ∇φ_e) = 0` in `ℝ^d`
              (∀ a ∈ Ωend, ∀ e : Vec d,
                HasWeakGradientOn Set.univ (Phi e a) (gradPhi e a) ∧
                  IsWeakSolutionOn (fun x => a.1 x) Set.univ
                    (fun x => e + gradPhi e a x)) ∧
              -- (2b) the corrector estimate
              -- `r⁻¹‖s̄^{1/2}∇φ_e‖_{H̲^{-1}(E_r)}`
              -- `+ r⁻¹‖s̄^{-1/2}((a - k̄)(e + ∇φ_e) - s̄e)‖_{H̲^{-1}(E_r)}`
              -- `≤ C|s̄^{1/2}e|(r/𝒳)^{-κ}`
              (∀ a ∈ Ωend, ∀ e : Vec d, ∀ r : ℝ, X a ≤ r →
                ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun x => matVecMul (matSqrt (symmPart abar))
                        (gradPhi e a x)) +
                  ENNReal.ofReal r⁻¹ *
                    negOneNorm (ellipsoid abar r)
                      (fun x => matVecMul (matSqrt (symmPart abar))⁻¹
                        (matVecMul (a.1 x - skewPart abar)
                            (e + gradPhi e a x) -
                          matVecMul (symmPart abar) e)) ≤
                  ENNReal.ofReal
                    (C * Real.sqrt (vecDot e (matVecMul (symmPart abar) e)) *
                      (r / X a) ^ (-κ))) ∧
              -- (3) the Liouville classification `e.random.liouville.growth`:
              -- the entire solutions are the `e · x + φ_e + c`, as two inclusions
              (∀ a ∈ Ωend, ∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                (∀ (v : Vec d → ℝ) (Dv : Vec d → Vec d),
                  MemLiouvilleClass (fun x => a.1 x) ϑ v Dv →
                  ∃ (e : Vec d) (c : ℝ),
                    v =ᵐ[MeasureTheory.volume] fun x => vecDot e x +
                      Phi e a x + c) ∧
                (∀ (e : Vec d) (c : ℝ),
                  MemLiouvilleClass (fun x => a.1 x) ϑ
                    (fun x => vecDot e x + Phi e a x + c)
                    (fun x => e + gradPhi e a x))) ∧
              -- for every solution on a large ellipsoid `E_R`, `R ≥ 𝒳`:
              -- (4) the large-scale energy estimate `e.uniform.energy`,
              -- `sup_{r ∈ [𝒳, R]} ‖s^{1/2}∇u‖_{L̲²(E_r)} ≤ C‖s^{1/2}∇u‖_{L̲²(E_R)}`, and
              -- (5) the first-order approximation,
              -- `‖s^{1/2}(∇u - e - ∇φ_e)‖_{L̲²(E_r)} ≤ C₁(ϑ)(r/R)^ϑ‖s^{1/2}∇u‖_{L̲²(E_R)}`
              (∀ a ∈ Ωend, ∀ R : ℝ, X a ≤ R →
                ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                  MemH1a (fun x => a.1 x) (ellipsoid abar R) u Du →
                  IsWeakSolutionOn (fun x => a.1 x) (ellipsoid abar R) Du →
                  (∀ r : ℝ, r ∈ Set.Icc (X a) R →
                    weightedGradNorm (fun x => a.1 x) (ellipsoid abar r) Du ≤
                      ENNReal.ofReal C *
                        weightedGradNorm (fun x => a.1 x)
                          (ellipsoid abar R) Du) ∧
                  (∀ ϑ : ℝ, ϑ ∈ Set.Ioo (0 : ℝ) 1 →
                    ∃ e : Vec d, ∀ r : ℝ, r ∈ Set.Icc (X a) R →
                      weightedGradNorm (fun x => a.1 x) (ellipsoid abar r)
                          (fun x => Du x - (e + gradPhi e a x)) ≤
                        ENNReal.ofReal (C₁ ϑ * (r / R) ^ ϑ) *
                          weightedGradNorm (fun x => a.1 x)
                            (ellipsoid abar R) Du)) := by
  sorry

end

end HCPoly.StatementAudit.UniformHomogenization
