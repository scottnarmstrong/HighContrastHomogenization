/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Persistence.AdaptedPersistence
import HCPoly.Provider.Persistence.TransferGauge
import HCPoly.Provider.Recurrence.PositiveGapClosure
import HCPoly.Geometry.NearIsometry
import HCPoly.Geometry.OperatorOrder

/-!
# The Euclidean transfer of the entry mean

The comparison between adapted and Euclidean cubes compares a Euclidean annealed
block with an adapted mean up to an error measured in units of the reference
block `𝐄`.  This file turns two such comparisons, read on the two distinct strict
generation chains of the forward and of the reverse comparison, into the
two-sided near-isometry `e.response.transfer.block.comparison` and a bound on the
Euclidean imbalance after the transfer.

The mechanism is one congruence and one rearrangement.  The congruence is the
entry ratio `Λ_t = |(E_t^q)^{-1/2}𝐄(E_t^q)^{-1/2}|`, one of the normalization
constants of the transfer: it is exactly the least scalar with `𝐄 ≤ Λ_t E_t^q`,
so an error `c𝐄` whose congruenced size `cΛ_t` is below a tolerance `η` is an
error below `ηE_t^q`.  The forward comparison then reads as the upper Euclidean
comparison.

The reverse comparison is one-sided in the wrong direction: it bounds the
adapted mean at the auxiliary scale by the Euclidean block.  The persistence
clause at that scale turns it into a lower bound for the Euclidean block in terms
of the entry mean, at the cost of the factor `(1+δ_ad)^d`, which is the lower
Euclidean comparison.  The tolerance conditions `e.response.transfer.tolerances`
were chosen exactly so that the two one-sided bounds close up into the symmetric
sandwich.

The last step is `e.global.selection.metric.comparison` at the sandwich: the Euclidean
block is positive definite because it dominates a positive multiple of the entry
mean — the Euclidean cube is not contained in the window, so this, and not the
window estimate, is the route to its definedness.
-/

namespace Homogenization
namespace HighContrast
namespace Persistence

open MeasureTheory

open scoped MatrixOrder Matrix

noncomputable section

variable {d : ℕ}

/-! ## The reference block measured against a positive block -/

/-- **The entry ratio is a Loewner bound.**  The scalar size
`blockSize E F = |F^{-1/2}EF^{-1/2}|` is the least nonnegative `t` with
`E ≤ tF`, so in particular it is one. -/
theorem toFullBlockMat_le_blockSize_smul {E F : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    toFullBlockMat E ≤ blockSize E F • toFullBlockMat F := by
  have hEfull := posDef_toFullBlockMat hE hEpd
  rw [blockSize_eq_relSize hE hF hFpd hEfull.posSemidef]
  exact le_relSize_smul hEfull.posSemidef (posDef_toFullBlockMat hF hFpd)

/-- **An error in units of the reference block, congruenced by a positive
block.**  A dilation `c𝐄` of the reference block whose congruenced size `cΛ` is
below `η` is below `ηF`. -/
theorem toFullBlockMat_blockScale_le_smul {E F : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E) (hF : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) {c eta : ℝ} (hc : 0 ≤ c)
    (hgap : c * blockSize E F ≤ eta) :
    toFullBlockMat (blockScale c E) ≤ eta • toFullBlockMat F := by
  rw [toFullBlockMat_blockScale]
  calc c • toFullBlockMat E ≤ c • (blockSize E F • toFullBlockMat F) :=
        smul_le_smul_of_le hc (toFullBlockMat_le_blockSize_smul hE hEpd hF hFpd)
    _ = (c * blockSize E F) • toFullBlockMat F := smul_smul _ _ _
    _ ≤ eta • toFullBlockMat F :=
        smul_le_smul_of_le_right (posDef_toFullBlockMat hF hFpd).posSemidef hgap

/-- Enlarging the scalar of a dilation of a positive block preserves a Loewner
upper bound. -/
theorem blockMatLoewnerLE_blockScale_mono {A B : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hB : IsSymmetricBlockMat B) (hBpd : Book.Ch02.BlockPosDef B) {c₁ c₂ : ℝ}
    (hc : c₁ ≤ c₂) (h : BlockMatLoewnerLE A (blockScale c₁ B)) :
    BlockMatLoewnerLE A (blockScale c₂ B) := by
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale]
  refine le_trans ?_
    (smul_le_smul_of_le_right (posDef_toFullBlockMat hB hBpd).posSemidef hc)
  have h' := le_of_blockMatLoewnerLE hA (isSymmetricBlockMat_blockScale c₁ hB) h
  rwa [toFullBlockMat_blockScale] at h'

/-! ## The two absorptions -/

/-- **The upper absorption**, giving the upper Euclidean comparison: an adapter
comparison `A ≤ B + c𝐄` whose error is below `ηB` reads as `A ≤ (1+η)B`. -/
theorem blockMatLoewnerLE_one_add {A B E : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hB : IsSymmetricBlockMat B) (hE : IsSymmetricBlockMat E) {c eta : ℝ}
    (hsub : BlockMatLoewnerLE (blockSub A B) (blockScale c E))
    (herr : toFullBlockMat (blockScale c E) ≤ eta • toFullBlockMat B) :
    BlockMatLoewnerLE A (blockScale (1 + eta) B) := by
  have hsub' : toFullBlockMat A - toFullBlockMat B ≤ eta • toFullBlockMat B := by
    rw [← Recurrence.toFullBlockMat_blockSub]
    exact le_trans (le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockSub hA hB)
      (isSymmetricBlockMat_blockScale c hE) hsub) herr
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale]
  refine Matrix.le_iff.mpr ?_
  have hrw : (1 + eta) • toFullBlockMat B - toFullBlockMat A =
      eta • toFullBlockMat B - (toFullBlockMat A - toFullBlockMat B) := by
    rw [add_smul, one_smul]; abel
  rw [hrw]
  exact Matrix.le_iff.mp hsub'

/-- **The lower absorption**, giving the lower Euclidean comparison: an adapter
comparison `C ≤ A + c𝐄` in the wrong direction, whose error is below `η₋B`,
becomes a lower bound for `A` once the persistence clause `B ≤ ϱ C` is available.
Rearranging gives `(ϱ^{-1} - η₋)B ≤ A`, and the tolerance conditions
`e.response.transfer.tolerances` weaken the scalar to the symmetric one. -/
theorem blockMatLoewnerLE_one_sub {A B C E : BlockMat d} (hA : IsSymmetricBlockMat A)
    (hB : IsSymmetricBlockMat B) (hC : IsSymmetricBlockMat C) (hE : IsSymmetricBlockMat E)
    (hBpd : Book.Ch02.BlockPosDef B) {c etaMinus ratio eta : ℝ} (hratio : 0 < ratio)
    (hsub : BlockMatLoewnerLE (blockSub C A) (blockScale c E))
    (herr : toFullBlockMat (blockScale c E) ≤ etaMinus • toFullBlockMat B)
    (hpers : BlockMatLoewnerLE B (blockScale ratio C))
    (htol : eta ≤ ratio⁻¹ - etaMinus) :
    BlockMatLoewnerLE (blockScale eta B) A := by
  have hsub' : toFullBlockMat C - toFullBlockMat A ≤ etaMinus • toFullBlockMat B := by
    rw [← Recurrence.toFullBlockMat_blockSub]
    exact le_trans (le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockSub hC hA)
      (isSymmetricBlockMat_blockScale c hE) hsub) herr
  have hpers' : toFullBlockMat B ≤ ratio • toFullBlockMat C := by
    have h := le_of_blockMatLoewnerLE hB (isSymmetricBlockMat_blockScale ratio hC) hpers
    rwa [toFullBlockMat_blockScale] at h
  -- the entry mean, from below, in terms of the Euclidean block and itself
  have hchain : toFullBlockMat B ≤
      ratio • toFullBlockMat A + (ratio * etaMinus) • toFullBlockMat B := by
    refine le_trans hpers' (Matrix.le_iff.mpr ?_)
    have hscaled : ratio • (toFullBlockMat C - toFullBlockMat A) ≤
        ratio • (etaMinus • toFullBlockMat B) := smul_le_smul_of_le hratio.le hsub'
    have hrw : ratio • toFullBlockMat A + (ratio * etaMinus) • toFullBlockMat B -
        ratio • toFullBlockMat C =
          ratio • (etaMinus • toFullBlockMat B) -
            ratio • (toFullBlockMat C - toFullBlockMat A) := by
      rw [smul_sub, smul_smul]; abel
    rw [hrw]
    exact Matrix.le_iff.mp hscaled
  -- the rearrangement
  have hrear : (1 - ratio * etaMinus) • toFullBlockMat B ≤ ratio • toFullBlockMat A := by
    refine Matrix.le_iff.mpr ?_
    have hrw : ratio • toFullBlockMat A - (1 - ratio * etaMinus) • toFullBlockMat B =
        ratio • toFullBlockMat A + (ratio * etaMinus) • toFullBlockMat B -
          toFullBlockMat B := by
      rw [sub_smul, one_smul]; abel
    rw [hrw]
    exact Matrix.le_iff.mp hchain
  have hdiv : (ratio⁻¹ * (1 - ratio * etaMinus)) • toFullBlockMat B ≤ toFullBlockMat A := by
    have h := smul_inv_le_of_le_smul hratio hrear
    rwa [smul_smul] at h
  have heq : ratio⁻¹ * (1 - ratio * etaMinus) = ratio⁻¹ - etaMinus := by
    rw [mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hratio), one_mul]
  rw [heq] at hdiv
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_blockScale]
  exact le_trans
    (smul_le_smul_of_le_right (posDef_toFullBlockMat hB hBpd).posSemidef htol) hdiv

/-! ## The Euclidean imbalance -/

/-- **The Euclidean imbalance** after the transfer: the near-isometric comparison
`e.global.selection.metric.comparison` at the sandwich of
`e.response.transfer.block.comparison`.  The lower half of the sandwich supplies
the positive definiteness of the Euclidean block, which is not available from
the window estimate. -/
theorem blockImbalance_le_of_near_isometry (hd : 2 ≤ d) {A B : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B)
    (hBpd : Book.Ch02.BlockPosDef B) {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (hlow : BlockMatLoewnerLE (blockScale (1 - eta) B) A)
    (hhigh : BlockMatLoewnerLE A (blockScale (1 + eta) B)) :
    blockImbalance A ≤ (1 + eta) ^ 3 / (1 - eta) * blockImbalance B := by
  have hBfull := posDef_toFullBlockMat hB hBpd
  have hlow' : (1 - eta) • toFullBlockMat B ≤ toFullBlockMat A := by
    have h := le_of_blockMatLoewnerLE (isSymmetricBlockMat_blockScale (1 - eta) hB) hA hlow
    rwa [toFullBlockMat_blockScale] at h
  have hhigh' : toFullBlockMat A ≤ (1 + eta) • toFullBlockMat B := by
    have h := le_of_blockMatLoewnerLE hA (isSymmetricBlockMat_blockScale (1 + eta) hB) hhigh
    rwa [toFullBlockMat_blockScale] at h
  have hAfull : (toFullBlockMat A).PosDef :=
    posDef_of_posDef_le (posDef_smul hBfull (by linarith only [heta1])) hlow'
  exact (canonNearIsometry hd hBfull hAfull heta0 heta1 hlow' hhigh').1

/-! ## The Euclidean transfer -/

/-- **The Euclidean transfer of the entry mean**: the near-isometry
`e.response.transfer.block.comparison` and the Euclidean imbalance after the
transfer, from the forward and reverse adapted-Euclidean comparisons read on
their two generation chains, their congruenced error bounds, and the adapted
imbalance hypothesis `e.response.adapted.conclusion`.

The two errors enter only through their congruenced sizes, so the argument is
insensitive to how the gaps were chosen; the tolerance conditions
`e.response.transfer.tolerances` are what make the two one-sided bounds
symmetric. -/
theorem euclidean_transfer (hd : 2 ≤ d) {P : Measure (CoeffSpace d)}
    [IsProbabilityMeasure P] (hstat : HCPoly.Frozen.IsStationaryLaw P) {E : BlockMat d}
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E) {jStar : ℤ} {q : Mat d}
    (hq : IsRoundedGrid jStar q) {t : ℤ} (hjt : jStar ≤ t)
    (hfin : HasFiniteAdaptedMean P q t) {deltaAd : ℝ} (hdeltaAd : 0 ≤ deltaAd)
    (himb : blockImbalance (adaptedMean P q t) ≤ 1 + deltaAd) {ment maux : ℤ}
    (htmaux : t ≤ maux) {cf cr : ℝ} (hcf : 0 ≤ cf) (hcr : 0 ≤ cr)
    (hfwd : BlockMatLoewnerLE
      (blockSub (annealedBlock P (centeredCube d ment)) (adaptedMean P q t))
      (blockScale cf E))
    (hrev : BlockMatLoewnerLE
      (blockSub (adaptedMean P q maux) (annealedBlock P (centeredCube d ment)))
      (blockScale cr E))
    {etaPlus etaMinus etaIso : ℝ}
    (hgapf : cf * blockSize E (adaptedMean P q t) ≤ etaPlus)
    (hgapr : cr * blockSize E (adaptedMean P q t) ≤ etaMinus)
    (hetaIso0 : 0 ≤ etaIso) (hetaIso1 : etaIso < 1) (hetaPlusIso : etaPlus ≤ etaIso)
    (hetaMinusIso : 1 - etaIso ≤ (1 + deltaAd) ^ (-(d : ℤ)) - etaMinus) :
    BlockMatLoewnerLE (blockScale (1 - etaIso) (adaptedMean P q t))
        (annealedBlock P (centeredCube d ment)) ∧
      BlockMatLoewnerLE (annealedBlock P (centeredCube d ment))
        (blockScale (1 + etaIso) (adaptedMean P q t)) ∧
      blockImbalance (annealedBlock P (centeredCube d ment)) ≤
        (1 + etaIso) ^ 3 / (1 - etaIso) * blockImbalance (adaptedMean P q t) := by
  haveI : NeZero d := ⟨by omega⟩
  have hEtsym := Recurrence.isSymmetricBlockMat_adaptedMean P q t
  have hEasym := Recurrence.isSymmetricBlockMat_adaptedMean P q maux
  have hFsym := Recurrence.isSymmetricBlockMat_annealedBlock P (centeredCube d ment)
  have hEtpd : Book.Ch02.BlockPosDef (adaptedMean P q t) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq t hfin
  -- the two errors, congruenced by the entry mean
  have herrf := toFullBlockMat_blockScale_le_smul hE hEpd hEtsym hEtpd hcf hgapf
  have herrr := toFullBlockMat_blockScale_le_smul hE hEpd hEtsym hEtpd hcr hgapr
  -- the upper half
  have hupper : BlockMatLoewnerLE (annealedBlock P (centeredCube d ment))
      (blockScale (1 + etaIso) (adaptedMean P q t)) :=
    blockMatLoewnerLE_blockScale_mono hFsym hEtsym hEtpd
      (by linarith only [hetaPlusIso])
      (blockMatLoewnerLE_one_add hFsym hEtsym hE hfwd herrf)
  -- the lower half, through the persistence clause at the auxiliary scale
  have hratio : (0 : ℝ) < (1 + deltaAd) ^ d := pow_pos (by linarith only [hdeltaAd]) d
  have htol : 1 - etaIso ≤ ((1 + deltaAd) ^ d)⁻¹ - etaMinus := by
    rwa [zpow_neg, zpow_natCast] at hetaMinusIso
  have hlower : BlockMatLoewnerLE (blockScale (1 - etaIso) (adaptedMean P q t))
      (annealedBlock P (centeredCube d ment)) :=
    blockMatLoewnerLE_one_sub hFsym hEtsym hEasym hE hEtpd hratio hrev herrr
      ((adapted_persistence hd hstat hq hjt hfin himb htmaux).2) htol
  exact ⟨hlower, hupper,
    blockImbalance_le_of_near_isometry hd hFsym hEtsym hEtpd hetaIso0 hetaIso1 hlower hupper⟩

end

end Persistence
end HighContrast
end Homogenization
