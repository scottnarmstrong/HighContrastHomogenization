import HCPoly.Entry.Multiscale.ResponseInputs.HC3_CutoffSupportQuadMeas
import Homogenization.CoarseGraining.BlockFormalism.MatrixIdentities
import Homogenization.CoarseGraining.BlockFormalism.EllipticBounds

/-!
# The cutoff-weighted quadratic readout of the canonical optimizer state

The cutoff pairing of the response estimate `e.response.cutoff.estimate` expands, in the notation of
AK.HC Lemma A.1, (A.4), into one quadratic term and three linear terms.  The quadratic term is the
cutoff-weighted volume average of the Euclidean pairing of the two slots of the canonical optimizer
state,

`a ↦ ⨍_{adaptedCell} φ · ⟨Z(a).1, Z(a).2⟩`,

where `Z(a)` is the canonical optimizer state of the recentred coefficient.  This is exactly the
`hquadMinus`/`hquadPlus` input of the family reduction of the cutoff pairing.

The second slot of the canonical optimizer state is the coefficient applied to the first, so this
readout is one half of the cutoff-weighted block self-pairing of `Z(a)`.  The block self-pairing of
`Z(a)` is *not* the block self-pairing of the Chapter-2 doubled minimizer `X(a)`: the a.e. extraction
identity `ae_toFullBlockVec_canonicalOptimizerBlockState` reads

`Z(a).α = X(a).α + (B_a X(a)).α.swap`,

so the two slots of `Z(a)` are the two slots of `X(a)` shifted by the swapped block image of `X(a)`.
This file records the exact algebraic link between the two self-pairings: pointwise,

`⟨Z(a).1, Z(a).2⟩ = ⟨X(a), B_a X(a)⟩ + 2 ⟨X(a).1, X(a).2⟩`.

Consequently the cutoff-weighted quadratic readout is *not* the (manifestly continuous) functional
`z ↦ ⨍ φ ⟨z.1, z.2⟩` of the Hilbert minimizer; the correct functional of the minimizer additionally
carries the weighted energy `⨍ φ ⟨z, B z⟩`, whose coefficients depend on the sample.  The
measurability of the cutoff-weighted quadratic readout therefore does not follow from the
Hilbert-space continuity argument applied to `⨍ φ ⟨z.1, z.2⟩`, and the identity below is the missing
algebraic link in that route.
-/

namespace Homogenization.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- For an elliptic matrix `A`, the two slots of the block image `B A X` satisfy
`⟨(B X).2, (B X).1⟩ = ⟨X.1, X.2⟩`.  Writing `s, k` for the symmetric and skew parts of `A` and
`(B X).1 = s p + k s⁻¹ r`, `(B X).2 = s⁻¹ r` with `r = q - k p`, this is the cancellation of the
skew form on `s⁻¹ r` together with the symmetry of `s`.  It is the exact reason the block
self-pairing of the canonical optimizer state differs from that of the doubled minimizer by a cross
pairing. -/
theorem vecDot_blockMatVecMul_snd_fst {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (X : BlockVec d) :
    vecDot (blockMatVecMul (blockMatrixOfCoeff A) X).2
      (blockMatVecMul (blockMatrixOfCoeff A) X).1 = vecDot X.1 X.2 := by
  let s := symmPart A
  let k := skewPart A
  let r := X.2 - matVecMul k X.1
  have hsnd : (blockMatVecMul (blockMatrixOfCoeff A) X).2 = matVecMul s⁻¹ r := by
    simpa only [s, k, r] using blockMatVecMul_blockMatrixOfCoeff_snd A X.1 X.2
  have hfst : (blockMatVecMul (blockMatrixOfCoeff A) X).1 =
      matVecMul s X.1 + matVecMul k (matVecMul s⁻¹ r) := by
    simpa only [s, k, r] using blockMatVecMul_blockMatrixOfCoeff_fst A X.1 X.2
  have hskew : vecDot (matVecMul s⁻¹ r) (matVecMul k (matVecMul s⁻¹ r)) = 0 := by
    simpa only [k] using vecDot_matVecMul_skewPart_self_eq_zero A (matVecMul s⁻¹ r)
  have hsdet : IsUnit s.det := by
    simpa only [s] using isUnit_det_symmPart_of_isEllipticMatrix hA
  have hsym : vecDot (matVecMul s⁻¹ r) (matVecMul s X.1) = vecDot r X.1 := by
    have h1 : vecDot (matVecMul s⁻¹ r) (matVecMul s X.1) =
        vecDot (matVecMul s (matVecMul s⁻¹ r)) X.1 := by
      have h := vecDot_matVecMul_transpose (matVecMul s⁻¹ r) X.1 s
      rwa [matTranspose_symmPart] at h
    rw [h1, matVecMul_mul, Matrix.mul_nonsing_inv s hsdet, matVecMul_one]
  have hr : vecDot r X.1 = vecDot X.1 X.2 := by
    have hk0 : vecDot (matVecMul k X.1) X.1 = 0 := by
      rw [vecDot_comm]
      exact vecDot_matVecMul_skewPart_self_eq_zero A X.1
    simp only [r, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, hk0, neg_zero, add_zero]
    exact vecDot_comm X.2 X.1
  rw [hsnd, hfst, vecDot_add_right, hsym, hskew, add_zero, hr]

/-- Pointwise link between the self-pairing of the canonical optimizer state and the doubled
minimizer energy.  If `Z = X + swap (B X)` is the state whose slots are the shifted slots of the
doubled minimizer `X`, then

`⟨Z.1, Z.2⟩ = ⟨X, B X⟩ + 2 ⟨X.1, X.2⟩`.

The cross term `2 ⟨X.1, X.2⟩` and the block energy `⟨X, B X⟩` are exactly what is lost by reading
the canonical state pairing as the pairing of the minimizer itself. -/
theorem vecDot_canonical_eq_blockVecDot_add_cross {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (X : BlockVec d) :
    vecDot (X.1 + (blockMatVecMul (blockMatrixOfCoeff A) X).2)
        (X.2 + (blockMatVecMul (blockMatrixOfCoeff A) X).1) =
      blockVecDot X (blockMatVecMul (blockMatrixOfCoeff A) X) + 2 * vecDot X.1 X.2 := by
  have hkey := vecDot_blockMatVecMul_snd_fst hA X
  have hcomm : vecDot (blockMatVecMul (blockMatrixOfCoeff A) X).2 X.2 =
      vecDot X.2 (blockMatVecMul (blockMatrixOfCoeff A) X).2 := vecDot_comm _ _
  simp only [vecDot_add_left, vecDot_add_right, blockVecDot]
  rw [hkey, hcomm]
  ring

/-- The same pointwise link, phrased for the coordinatewise extraction of the canonical optimizer
state of `e.response.cutoff.estimate`: almost everywhere on the domain, the pairing of the two slots
of the canonical optimizer state equals the doubled block energy of the minimizer plus twice the
cross pairing of the minimizer slots.  This is the algebraic content of the gap between the
cutoff-weighted quadratic readout and the pairing of the Hilbert minimizer (AK.HC Lemma A.1,
(A.4)). -/
theorem ae_vecDot_canonicalOptimizerBlockState_eq_blockVecDot {U : Book.Ch02.Domain d}
    {lam Lam : ℝ} {aU : Book.Ch02.CoeffOn U}
    (haU : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)), IsEllipticMatrix lam Lam (aU.toCoeffField x))
    (p q : Vec d) {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U aU (-p, q) X) :
    (fun x => vecDot
        (canonicalOptimizerBlockState U aU p q x).1
        (canonicalOptimizerBlockState U aU p q x).2)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
    fun x => blockVecDot (X.eval x)
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)) +
      2 * vecDot (X.eval x).1 (X.eval x).2 := by
  have hcoordP : ∀ i : Fin d,
      (fun x => (canonicalOptimizerBlockState U aU p q x).1 i)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (X.eval x).1 i +
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)).2 i := by
    intro i
    have h := ae_toFullBlockVec_canonicalOptimizerBlockState (aU := aU) p q (Sum.inl i) hX
    simpa only [toFullBlockVec, Sum.swap_inl] using h
  have hcoordN : ∀ i : Fin d,
      (fun x => (canonicalOptimizerBlockState U aU p q x).2 i)
        =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (X.eval x).2 i +
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)).1 i := by
    intro i
    have h := ae_toFullBlockVec_canonicalOptimizerBlockState (aU := aU) p q (Sum.inr i) hX
    simpa only [toFullBlockVec, Sum.swap_inr] using h
  have h1 : (fun x => (canonicalOptimizerBlockState U aU p q x).1)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (X.eval x).1 +
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)).2 := by
    filter_upwards [ae_all_iff.mpr hcoordP] with x hx
    exact funext fun i => hx i
  have h2 : (fun x => (canonicalOptimizerBlockState U aU p q x).2)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => (X.eval x).2 +
        (blockMatVecMul (blockCoeffField aU.toCoeffField x) (X.eval x)).1 := by
    filter_upwards [ae_all_iff.mpr hcoordN] with x hx
    exact funext fun i => hx i
  filter_upwards [haU, h1, h2] with x hEll h1x h2x
  rw [h1x, h2x]
  exact vecDot_canonical_eq_blockVecDot_add_cross hEll (X.eval x)

end

end Homogenization.HighContrast.Multiscale

