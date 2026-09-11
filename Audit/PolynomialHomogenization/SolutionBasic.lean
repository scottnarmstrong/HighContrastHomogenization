/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import Mathlib

/-!
# Polynomial homogenization with a random microscopic source scale: the statement vocabulary

This file carries the vocabulary of `Audit.PolynomialHomogenization.Challenge`, word for
word, and is imported by `Audit.PolynomialHomogenization.Solution`, so that the proved
theorem is stated in exactly the objects the challenge states it in.  It imports
only Mathlib; the statement, the standing assumptions and the presentation deltas
are recorded in the module docstring of the challenge.
-/

namespace HCPoly.StatementAudit.PolynomialHomogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## Ambient vectors, matrices, and the doubled block algebra

Coarse graining pairs a slope with a flux, so the blocks `𝐀(U; a)`, `𝐄` and
`𝐀̄(U)` it compares are `2d × 2d` and every inequality between them is in the
Loewner order.
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

Contrast is measured on the centred cubes `□_m = (-3^m/2, 3^m/2)^d`, and
`e.coarse.ellipticity` is imposed on the aligned cubes `y + □_k` with
`y ∈ 3^k ℤ^d`.
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

The coarse block `𝐀(U; a)` is characterized by
`½ P · 𝐀(U; a) P = inf {⨍_U ½ X · 𝐀(x) X}` over the admissible doubled states
`X`, and its entries are recovered from that infimum by polarization.
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

/-! ## Schur data and the reference aspect ratio

A positive doubled block is parametrized by its Schur coefficients `σ`, `κ`,
`σ_*` as in `e.reference.block`; the only scalar this statement builds from them
is the reference aspect ratio `Π` of `e.reference.aspect.ratio`.
-/

/-- Scalar dilation of a doubled block matrix. -/
def blockScale {d : ℕ} (c : ℝ) (A : BlockMat d) : BlockMat d :=
  { upperLeft := c • A.upperLeft
    upperRight := c • A.upperRight
    lowerLeft := c • A.lowerLeft
    lowerRight := c • A.lowerRight }

/-- A skew-symmetric `d × d` matrix. -/
def IsSkewMat {d : ℕ} (h : Mat d) : Prop := matTranspose h = -h

/-- The Schur coefficient `κ` of a doubled block (`e.annealed.schur`). -/
def schurSkew {d : ℕ} (H : BlockMat d) : Mat d := -(H.lowerRight⁻¹ * H.lowerLeft)

/-- The Schur coefficient `σ` of a doubled block (`e.annealed.schur`). -/
def schurSigma {d : ℕ} (H : BlockMat d) : Mat d :=
  H.upperLeft - matTranspose (schurSkew H) * H.lowerRight * schurSkew H

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

/-! ## The concentration gauge and the coarse ellipticity assumption

`e.coarse.ellipticity` bounds the coarse blocks of the aligned cubes above a
random source scale `S`, whose law is controlled through `e.source.tail` by a
gauge `Ψ_S` of moderate growth.
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

end

end HCPoly.StatementAudit.PolynomialHomogenization
