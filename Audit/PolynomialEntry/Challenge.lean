/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Mathlib

/-!
# Theorem A: polynomial entry into small contrast

Theorem A of *Homogenization at a polynomial scale in high contrast*
(`t.polynomial.entry`), restated over Mathlib alone.  Every object the statement
names is rebuilt below, in the order in which the paper introduces it, so the
sections that follow read as the setup section of the paper and the last one as
the theorem.

## The theorem in words

Fix a dimension `d ≥ 2`, a coarse ellipticity exponent `g ∈ [0, 1)` and a
tolerance `σ ∈ (0, 1]`.  There is a constant `C > 0` such that every law `P`
satisfying the standing assumptions admits a deterministic entry generation
`m_ent ∈ ℕ` with

* `m_ent ≤ ⌈C log₃ (2 + Π K)⌉`, where `Π` is the aspect ratio
  `e.reference.aspect.ratio` of the reference block and `K` is the growth
  witness of the source gauge;
* `Θ_{m_ent} ≤ 1 + σ`, where `Θ_m` is the annealed contrast `e.Theta.m` of the
  centred cube `□_m`;
* `3^{m_ent} ≤ 3 (2 + Π K)^C`, the same bound read as a length.

The first two displays are `e.polynomial.entry`.  The constant `C` depends on
`σ`, `d` and `g` alone: it is chosen before the law, the reference block, the
gauge, the growth witness and the source scale, so a single power of `2 + Π K`
bounds the entry length over the whole class.  The generation `m_ent` need not
be the first at which the contrast is small, and no bound uniform as `g ↑ 1` is
asserted.

## Standing assumptions

`P` is a probability law on the coefficient space `Ω` of measurable coefficient
fields modulo equality almost everywhere, qualitatively locally uniformly
elliptic.  It is stationary under the integer translations of `ℝ^d`, has unit
range of dependence — the local `σ`-fields of two sets at supremum distance at
least one are independent — and satisfies the random-source coarse ellipticity
`e.coarse.ellipticity` with reference block `E`, gauge `Ψ`, growth witness `K`
and source scale `S`.

## Presentation deltas

* **Symbols.**  The paper writes the exponent `γ`, the gauge `Ψ_S` and its
  growth witness `K_{Ψ_S}`.  Here they are `g`, `Ψ` and `K`, and `m_ent` is
  `mEnt`.  Only the spelling changes, the Lean names carrying no subscripts.
* **The length form of the entry bound.**  The paper bounds the generation and
  remarks that the corresponding length is bounded by a power of `2 + Π K`.
  Here that remark is the third conclusion, `3^{m_ent} ≤ 3 (2 + Π K)^C`, with
  the same `C`.  It is the first conclusion composed with `⌈x⌉ ≤ x + 1`.
* **The reference block.**  The paper writes `𝐄` in the Schur form
  `e.reference.block`.  Here `E` is an arbitrary symmetric positive definite
  doubled block and its Schur coefficients `σ₀`, `κ₀`, `σ_{*,0}` are read off
  from it.  The Schur form parametrizes exactly the symmetric positive definite
  blocks, so the two readings name the same matrices.
* **`Π` and `Θ_m`.**  The paper writes both through a spectral norm, `Π` through
  `|σ_{*,0}^{-1}|` and `Θ_m` through a conjugation by `σ̄_*^{-1/2}`.  Here each
  is the least scalar `t ≥ 0` realizing a Loewner bound.  Conjugating that
  Loewner bound by the positive definite `σ̄_*^{-1/2}` returns the printed
  spectral norm, so the two quantities agree.
* **The coefficient carrier.**  The paper takes the coefficient fields subject
  to `e.qualitative.ellipticity`.  Here the carrier is the almost-everywhere
  quotient of the measurable fields that are qualitatively locally uniformly
  elliptic.  That condition implies the printed one, so the class here is
  contained in the printed class; no constant of the theorem depends on the
  ellipticity constants it produces, and the quotient changes nothing because
  every object named in the statement is insensitive to a null set.

The only omitted proof is the proof of the theorem.
-/

namespace HCPoly.StatementAudit.PolynomialEntry

open MeasureTheory

noncomputable section

/-! ## Ambient vectors, matrices, and the doubled block algebra

The paper works on `ℝ^d` with a measurable coefficient field `a`, writing
`s = ½(a + aᵗ)` for its symmetric part and `k = ½(a - aᵗ)` for its antisymmetric
part.  Coarse graining pairs a slope with a flux, so the matrices it compares —
the coarse block `𝐀(U; a)`, the reference block `𝐄` and the annealed block
`𝐀̄(U)` — are `2d × 2d` and act on the doubled space `ℝ^d × ℝ^d`, and every
inequality between them is in the Loewner order.  A doubled matrix is carried
here by its four `d × d` blocks, and each Loewner order by the inequality of the
associated quadratic forms.
-/

/-- The ambient space `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- The `d × d` real matrices. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- A doubled vector `P = (p, q)`: a slope paired with a flux. -/
abbrev BlockVec (d : ℕ) := Vec d × Vec d

/-- The index type of a doubled vector: the `d` slope coordinates, then the `d` flux coordinates. -/
abbrev BlockCoord (d : ℕ) := Sum (Fin d) (Fin d)

/-- A doubled `2d × 2d` matrix, carried by its four `d × d` blocks. -/
structure BlockMat (d : ℕ) where
  upperLeft : Mat d
  upperRight : Mat d
  lowerLeft : Mat d
  lowerRight : Mat d

/-- The Euclidean inner product on `ℝ^d`. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ := ∑ i, x i * y i

/-- The squared Euclidean norm on `ℝ^d`. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ := vecDot x x

/-- Matrix–vector multiplication. -/
def matVecMul {d : ℕ} (A : Mat d) (x : Vec d) : Vec d := fun i => ∑ j, A i j * x j

/-- Matrix transposition. -/
def matTranspose {d : ℕ} (A : Mat d) : Mat d := Matrix.transpose A

/-- The Euclidean inner product on doubled vectors. -/
def blockVecDot {d : ℕ} (X Y : BlockVec d) : ℝ := vecDot X.1 Y.1 + vecDot X.2 Y.2

/-- Doubled matrix–vector multiplication. -/
def blockMatVecMul {d : ℕ} (A : BlockMat d) (X : BlockVec d) : BlockVec d :=
  ( matVecMul A.upperLeft X.1 + matVecMul A.upperRight X.2
  , matVecMul A.lowerLeft X.1 + matVecMul A.lowerRight X.2 )

/-- The symmetric part `s = ½(a + aᵗ)` of a matrix. -/
def symmPart {d : ℕ} (A : Mat d) : Mat d := fun i j => (A i j + A j i) / 2

/-- The antisymmetric part `k = ½(a - aᵗ)` of a matrix. -/
def skewPart {d : ℕ} (A : Mat d) : Mat d := fun i j => (A i j - A j i) / 2

/-- The entries of a doubled block matrix, indexed by the coordinates of the doubled space. -/
def blockMatEntry {d : ℕ} (A : BlockMat d) : BlockCoord d → BlockCoord d → ℝ
  | Sum.inl i, Sum.inl j => A.upperLeft i j
  | Sum.inl i, Sum.inr j => A.upperRight i j
  | Sum.inr i, Sum.inl j => A.lowerLeft i j
  | Sum.inr i, Sum.inr j => A.lowerRight i j

/-- The standard basis of the doubled space: the slope directions, then the flux directions. -/
def blockBasis {d : ℕ} : BlockCoord d → BlockVec d
  | Sum.inl i => (Pi.single i 1, 0)
  | Sum.inr i => (0, Pi.single i 1)

/-- Symmetry of a doubled block matrix, entry by entry. -/
def IsSymmetricBlockMat {d : ℕ} (A : BlockMat d) : Prop :=
  ∀ α β : BlockCoord d, blockMatEntry A α β = blockMatEntry A β α

/-- The Loewner order `A ≤ B` on matrices, as the inequality of the forms `½ x · A x`. -/
def MatLoewnerLE {d : ℕ} (A B : Mat d) : Prop :=
  ∀ x : Vec d,
    (1 / 2 : ℝ) * vecDot x (matVecMul A x) ≤
      (1 / 2 : ℝ) * vecDot x (matVecMul B x)

/-- The scalar Loewner bound `|M| = inf {t ≥ 0 : M ≤ t I}`, the printed bracket `| · |`. -/
def specBound {d : ℕ} (M : Mat d) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ MatLoewnerLE M (t • (1 : Mat d))}

/-- The Loewner order on doubled block matrices, in which `e.coarse.ellipticity` is read. -/
def BlockMatLoewnerLE {d : ℕ} (A B : BlockMat d) : Prop :=
  ∀ X : BlockVec d,
    (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul A X) ≤
      (1 / 2 : ℝ) * blockVecDot X (blockMatVecMul B X)

/-- Positive definiteness of a doubled block matrix, through its quadratic form. -/
def BlockPosDef {d : ℕ} (A : BlockMat d) : Prop :=
  ∀ X : BlockVec d, X ≠ 0 → 0 < blockVecDot X (blockMatVecMul A X)

/-- The `i`-th coordinate basis vector of `ℝ^d`. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d := Pi.single i (1 : ℝ)

/-! ## Coefficient fields and the almost-everywhere carrier

The sample space of the paper is a set `Ω` of measurable coefficient fields on
`ℝ^d`, carrying the translations `a ↦ a(· + z)` by `z ∈ ℤ^d` and a law
stationary under them.  Two fields agreeing almost everywhere define the same
equation, the same coarse block and the same statistic, so `Ω` is built here
from the Lebesgue quotient of the matrix-valued fields rather than from
functions.  Its points are the fields that are locally uniformly elliptic in the
qualitative sense: on every ball one pair of ellipticity constants serves almost
every value of the field there.  Those constants belong to the field and to the
ball and enter no estimate; what the condition supplies is the local
integrability of the gradients and the fluxes, which is the role of
`e.qualitative.ellipticity` in the paper.
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

/-! ## The local `σ`-fields and the standing hypotheses on the law

The law is a probability measure on `Ω`, stationary under the integer
translations, with unit range of dependence: the `σ`-fields `F(U)` and `F(V)`
carried by the field inside two sets at distance at least one are independent.
`F(U)` is generated here by the linear statistics `a ↦ ∫ e' · a(x) e φ(x) dx`
with `φ` smooth and supported in `U`.  Each of them is a function of the
restriction of `a` to `U`, and together they determine that restriction almost
everywhere, so they generate exactly the information the field carries inside
`U`.
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

Contrast is measured on the centred cubes `□_m = (-3^m/2, 3^m/2)^d`, and the
coarse ellipticity condition `e.coarse.ellipticity` is imposed on the aligned
cubes `y + □_k` with `y ∈ 3^k ℤ^d`.  Both are realizations of a single triadic
cube, indexed by its integer scale and its integer position; the scale ranges
over all the integers, so the cubes descend below the unit scale.
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

/-- The triadic cube translated by an integer index shift. -/
def translateCube {d : ℕ} (shift : Fin d → ℤ) (Q : TriadicCube d) : TriadicCube d :=
  { scale := Q.scale
    index := fun i => Q.index i + shift i }

/-- The centred open cube `□_m = (-3^m/2, 3^m/2)^d`. -/
def centeredCube (d : ℕ) (m : ℤ) : Set (Vec d) := openCubeSet (originCube d m)

/-- The aligned cube `y + □_k`, `y = 3^k w`, over which `e.coarse.ellipticity` quantifies. -/
def standardCell (d : ℕ) (k : ℤ) (w : Fin d → ℤ) : Set (Vec d) :=
  openCubeSet (translateCube w (originCube d k))

/-- The centre `y = 3^k w` of an aligned cube. -/
def standardCellCenter {d : ℕ} (k : ℤ) (w : Fin d → ℤ) : Vec d := fun i => (3 : ℝ) ^ k * (w i : ℝ)

/-! ## Weak derivatives and the `H¹` classes

Sobolev membership without an underline has its usual meaning in the paper:
`H¹(U)` is the space of `L²(U)` functions with an `L²(U)` distributional
gradient, and `H¹₀(U)` is the closure in it of the smooth functions compactly
supported in `U`.  A member of either is carried here as a function together
with a named candidate gradient and the integration-by-parts identity witnessing
that the candidate is the weak gradient, so that an estimate on `∇u` below is an
estimate on a field one can exhibit rather than on a chosen representative of an
equivalence class.
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

/-- The restricted Lebesgue measure on a domain `U ⊆ ℝ^d`. -/
abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) := volume.restrict U

/-- Vector-valued `L²` membership on `U`. -/
abbrev MemVectorL2 {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  MemLp f 2 (volumeMeasureOn U)

/-- A vector field that is the gradient of an `H¹₀(U)` function. -/
def IsPotentialZeroTraceOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  ∃ u : H10Function U, u.toH1Function.grad = f

/-- A vector field divergence free on `U` with vanishing normal trace. -/
def IsSolenoidalZeroNormalTraceOn {d : ℕ} (U : Set (Vec d))
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H1Function U,
    ∫ x in U, vecDot (g x) (φ.grad x) ∂volume = 0

/-- The volume-normalized integral `⨍_U f`. -/
def volumeAverage {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume

/-! ## The block formalism and the coarse block response

The coarse block `𝐀(U; a)` of the paper is the variational coarse-grained matrix
of the high-contrast theory, characterized by
`½ P · 𝐀(U; a) P = inf {⨍_U ½ X · 𝐀(x) X}`, the infimum over the doubled states
`X` whose slope part differs from `p` by a gradient with zero boundary values and
whose flux part differs from `q` by a divergence-free field with zero normal
trace, `𝐀(x)` being the doubled matrix of `a(x)`.  That infimum is the definition
used here, and the entries of `𝐀(U; a)` are recovered from it by polarization, so
the block is a function of the coefficient field alone.
-/

/-- A doubled state `X = (potential, flux)`: a slope field paired with a flux field. -/
structure BlockState (d : ℕ) where
  potential : Vec d → Vec d
  flux : Vec d → Vec d

/-- The doubled vector of a state at a point. -/
def BlockState.eval {d : ℕ} (X : BlockState d) (x : Vec d) : BlockVec d := (X.potential x, X.flux x)

/-- The doubled matrix `𝐀(x)` of a coefficient matrix, the Schur form of `e.reference.block`. -/
def blockMatrixOfCoeff {d : ℕ} (A : Mat d) : BlockMat d :=
  let s := symmPart A
  let k := skewPart A
  let sInv := s⁻¹
  { upperLeft := s + (matTranspose k) * sInv * k
    upperRight := -((matTranspose k) * sInv)
    lowerLeft := -(sInv * k)
    lowerRight := sInv }

/-- The doubled matrix field of a coefficient field. -/
def blockCoeffField {d : ℕ} (a : CoeffField d) : Vec d → BlockMat d :=
  fun x => blockMatrixOfCoeff (a x)

/-- The admissible competitors of the doubled variational problem on `U` with datum `P`. -/
def IsBlockMuAdmissible {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (X : BlockState d) : Prop :=
  MemVectorL2 U (fun x => X.potential x - P.1) ∧
    IsPotentialZeroTraceOn U (fun x => X.potential x - P.1) ∧
      MemVectorL2 U (fun x => X.flux x - P.2) ∧
        IsSolenoidalZeroNormalTraceOn U (fun x => X.flux x - P.2)

/-- The doubled energy density `½ X(x) · 𝐀(x) X(x)` of a state. -/
def blockEnergyDensity {d : ℕ} (a : CoeffField d) (X : BlockState d)
    (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) *
    blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))

/-- The normalized energies of the admissible competitors. -/
def muValueSet {d : ℕ} (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) :
    Set ℝ :=
  { m | ∃ X : BlockState d,
      IsBlockMuAdmissible U P X ∧ m = volumeAverage U (blockEnergyDensity a X) }

/-- The coarse-graining quantity `μ(U, P; a)`, with `½ P · 𝐀(U; a) P = μ(U, P; a)`. -/
def Mu {d : ℕ} (U : Set (Vec d)) (P : BlockVec d) (a : CoeffField d) : ℝ := sInf (muValueSet U P a)

/-- The entries of the coarse block `𝐀(U; a)`, recovered from `μ` by polarization. -/
def coarseBlockEntry {d : ℕ} (U : Set (Vec d)) (a : CoeffField d)
    (α β : BlockCoord d) : ℝ :=
  if _h : α = β then
    2 * Mu U (blockBasis α) a
  else
    Mu U (blockBasis α + blockBasis β) a - Mu U (blockBasis α) a -
      Mu U (blockBasis β) a

/-- The coarse block of a coefficient representative. -/
def coarseBlockMatrix {d : ℕ} (U : Set (Vec d)) (a : CoeffField d) : BlockMat d :=
  { upperLeft := fun i j => coarseBlockEntry U a (Sum.inl i) (Sum.inl j)
    upperRight := fun i j => coarseBlockEntry U a (Sum.inl i) (Sum.inr j)
    lowerLeft := fun i j => coarseBlockEntry U a (Sum.inr i) (Sum.inl j)
    lowerRight := fun i j => coarseBlockEntry U a (Sum.inr i) (Sum.inr j) }

/-- The coarse block `𝐀(U; a)` of a point of the coefficient space. -/
def coarseBlock {d : ℕ} (U : Set (Vec d)) (a : CoeffSpace d) : BlockMat d :=
  coarseBlockMatrix U ⇑a.1

/-! ## Schur data, the annealed block, and the annealed contrast

A positive doubled block is parametrized by its Schur coefficients `σ`, `κ`,
`σ_*` as in `e.reference.block` and `e.annealed.schur`, and they are read off
from the four blocks here.  The annealed block is `𝐀̄(U) = E[𝐀(U; ·)]`, taken
entry by entry.  The two scalars the theorem bounds are built from these
coefficients: the reference aspect ratio `Π` of `e.reference.aspect.ratio` and
the annealed contrast `Θ_m` of `e.Theta.m`, each written as the least scalar
realizing a Loewner bound.
-/

/-- Scalar dilation of a doubled block matrix. -/
def blockScale {d : ℕ} (c : ℝ) (A : BlockMat d) : BlockMat d :=
  { upperLeft := c • A.upperLeft
    upperRight := c • A.upperRight
    lowerLeft := c • A.lowerLeft
    lowerRight := c • A.lowerRight }

/-- A skew-symmetric `d × d` matrix. -/
def IsSkewMat {d : ℕ} (h : Mat d) : Prop := matTranspose h = -h

/-- The Schur coefficient `σ_*` of a doubled block (`e.annealed.schur`). -/
def schurSigmaStar {d : ℕ} (H : BlockMat d) : Mat d := H.lowerRight⁻¹

/-- The Schur coefficient `κ` of a doubled block (`e.annealed.schur`). -/
def schurSkew {d : ℕ} (H : BlockMat d) : Mat d := -(H.lowerRight⁻¹ * H.lowerLeft)

/-- The Schur coefficient `σ` of a doubled block (`e.annealed.schur`). -/
def schurSigma {d : ℕ} (H : BlockMat d) : Mat d :=
  H.upperLeft - matTranspose (schurSkew H) * H.lowerRight * schurSkew H

/-- The contrast `Θ` of a doubled block, the quantity of `e.Theta.m`. -/
def blockContrast {d : ℕ} (H : BlockMat d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
    MatLoewnerLE
      (schurSigma H +
        matTranspose (schurSkew H - h) * H.lowerRight * (schurSkew H - h))
      (t • schurSigmaStar H)}

/-- The lower reference constant `λ₀ = |σ_{*,0}⁻¹|⁻¹` of `e.reference.aspect.ratio`. -/
def lambdaRef {d : ℕ} (E : BlockMat d) : ℝ := (specBound E.lowerRight)⁻¹

/-- The upper reference constant `Λ₀` of `e.reference.aspect.ratio`. -/
def bigLambdaRef {d : ℕ} (E : BlockMat d) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ h : Mat d, IsSkewMat h ∧
    MatLoewnerLE
      (schurSigma E +
        matTranspose (schurSkew E - h) * E.lowerRight * (schurSkew E - h))
      (t • (1 : Mat d))}

/-- The reference aspect ratio `Π = Λ₀ / λ₀` of `e.reference.aspect.ratio`. -/
def aspectRatio {d : ℕ} (E : BlockMat d) : ℝ := bigLambdaRef E / lambdaRef E

/-- The deterministic annealed block `𝐀̄(U) = E[𝐀(U; ·)]`, entry by entry. -/
def annealedBlock {d : ℕ} (P : Measure (CoeffSpace d)) (U : Set (Vec d)) :
    BlockMat d :=
  { upperLeft := Matrix.of fun i j => ∫ a, (coarseBlock U a).upperLeft i j ∂P
    upperRight := Matrix.of fun i j => ∫ a, (coarseBlock U a).upperRight i j ∂P
    lowerLeft := Matrix.of fun i j => ∫ a, (coarseBlock U a).lowerLeft i j ∂P
    lowerRight := Matrix.of fun i j => ∫ a, (coarseBlock U a).lowerRight i j ∂P }

/-- The annealed contrast `Θ_m` of `e.Theta.m`, the contrast of the block of `□_m`. -/
def annealedContrast {d : ℕ} (P : Measure (CoeffSpace d)) (m : ℤ) : ℝ :=
  blockContrast (annealedBlock P (centeredCube d m))

/-! ## The concentration gauge and the coarse ellipticity assumption

The quantitative hypothesis of the paper bounds the coarse blocks above a random
source scale `S`: almost surely, once `3^m ≥ S`, every aligned cube `y + □_k`
with `k ≤ m` and `y ∈ 3^k ℤ^d ∩ □_m` satisfies `𝐀(y + □_k; a) ≤ 3^{g(m - k)} 𝐄`,
which is `e.coarse.ellipticity`.  The law of `S` is controlled by a gauge `Ψ_S`
through `e.source.tail`: `P[S > t] ≤ Ψ_S(t)⁻¹`, with `Ψ_S` nondecreasing, at
least one, and of moderate growth in the sense `t Ψ_S(t) ≤ Ψ_S(K t)` for a
witness `K > 1`.  Those displays and the positivity of the reference block are
bundled below into one hypothesis on the law.
-/

/-- The upper-tail event `{X > t}` of `e.source.tail`. -/
def upperTailEvent {Ω : Type*} (X : Ω → ℝ) (a : ℝ) : Set Ω := {ω | a < X ω}

/-- An admissible gauge `Ψ_S`: nondecreasing on `ℝ₊`, with values in `[1, ∞)`. -/
def AdmissiblePsi (Ψ : ℝ → ℝ) : Prop := MonotoneOn Ψ (Set.Ici 0) ∧ ∀ ⦃t : ℝ⦄, 0 ≤ t → 1 ≤ Ψ t

/-- The moderate-growth hypothesis `t Ψ_S(t) ≤ Ψ_S(K t)`, `t ≥ 1`, of `e.source.tail`. -/
def HasPsiGrowth (Ψ : ℝ → ℝ) (K : ℝ) : Prop := ∀ ⦃t : ℝ⦄, 1 ≤ t → t * Ψ t ≤ Ψ (K * t)

/-- The random-source coarse ellipticity hypothesis `e.coarse.ellipticity`, with `e.source.tail`. -/
structure CoarseEllipticityDagger {d : ℕ} (P : Measure (CoeffSpace d)) (g : ℝ)
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ) : Prop where
  g_mem : g ∈ Set.Ico (0 : ℝ) 1
  refBlock_isSymm : IsSymmetricBlockMat E
  refBlock_posDef : BlockPosDef E
  gauge_admissible : AdmissiblePsi Ψ
  one_lt_growthWitness : 1 < K
  gauge_growth : HasPsiGrowth Ψ K
  source_measurable : Measurable S
  source_nonneg : ∀ a, 0 ≤ S a
  source_tail : ∀ t : ℝ, 0 < t → P.real (upperTailEvent S t) ≤ (Ψ t)⁻¹
  coarse_bound : ∀ᵐ a ∂P, ∀ m : ℤ, S a ≤ (3 : ℝ) ^ m →
    ∀ k : ℤ, k ≤ m → ∀ w : Fin d → ℤ,
      standardCellCenter k w ∈ centeredCube d m →
      BlockMatLoewnerLE (coarseBlock (standardCell d k w) a)
        (blockScale ((3 : ℝ) ^ (g * ((m : ℝ) - (k : ℝ)))) E)

/-! ## The theorem

Each hypothesis and each conclusion is annotated with the content it restates
and, where there is one, the label of the display of the paper, so that the
statement can be checked clause by clause against the printed theorem.
-/

/-- **Theorem A, `t.polynomial.entry`: polynomial entry into small contrast.** -/
theorem polynomial_entry
    -- the dimension, the coarse ellipticity exponent `γ`, and the tolerance `σ`
    (d : ℕ) (hd : 2 ≤ d) (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1)
    (σ : ℝ) (hσ : σ ∈ Set.Ioc (0 : ℝ) 1) :
    -- the constant `C = C(σ, d, γ)`, chosen before the law and all of its data
    ∃ C : ℝ, 0 < C ∧
      -- the law, the reference block `𝐄`, the gauge `Ψ_S`, its growth witness
      -- `K_{Ψ_S}`, and the source scale `S`
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        -- a probability measure, stationary, of unit range of dependence
        IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
        -- coarse ellipticity above the source scale, `e.coarse.ellipticity`
        -- together with the source tail `e.source.tail`
        CoarseEllipticityDagger P g E Ψ K S →
        -- the deterministic entry generation `m_ent`
        ∃ mEnt : ℕ,
          -- `m_ent ≤ ⌈C log₃ (2 + Π K)⌉`, `e.polynomial.entry`
          (mEnt : ℤ) ≤ ⌈C * Real.logb 3 (2 + aspectRatio E * K)⌉ ∧
          -- `Θ_{m_ent} ≤ 1 + σ`, `e.polynomial.entry`
          annealedContrast P (mEnt : ℤ) ≤ 1 + σ ∧
          -- the same bound as a length: `3^{m_ent} ≤ 3 (2 + Π K)^C`
          (3 : ℝ) ^ mEnt ≤ 3 * (2 + aspectRatio E * K) ^ C := by
  sorry

end

end HCPoly.StatementAudit.PolynomialEntry
