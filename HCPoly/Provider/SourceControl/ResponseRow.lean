/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.SourceControl.ResponseRowSeries
import HCPoly.Provider.Recurrence.AdaptedCell
import HCPoly.Provider.Sharp.ReflectionOrder
import HCPoly.Geometry.AnnealedBlockBridge

/-!
# The all-earlier response row of `e.source.adapted.bound`

The all-earlier source row at the response scale is the third block of the
source estimate `e.source.adapted.bound`: for `j_* \leq s < t` with `\cus_s^{\mathbf q}`
inside the window and `\lambda > g`, the scale-weighted sum of the *averaged*
annealed responses of the aligned cells whose centres lie in `\cus_s^{\mathbf q}`
is below `B_{\mathbf q}\E[Y_P](3^{\lambda-g}-1)^{-1}3^{-\lambda(s-j_*)}\mathbf E`,
and the adjoint row holds with `(\bfA,\mathbf E)` replaced by
`(\bfA_*^{-1},\mathbf E_*^{-1})`.

The printed proof is three moves, and this file is those three
moves.

*The cell bound below the burn.*  `e.source.adapted.bound` is the
pathwise bound with the burn discount `3^{g(j_*-a)_+}` retained; every earlier
consumer of the window multiplier read it at or above the alignment scale, where
the discount is one, so the terminal comparison discards it.  Here the scales are
strictly below the alignment and the discount is the whole point, so the
comparison is taken with the factor kept: the pathwise bound integrated against
the law is the annealed bound at `B_{\mathbf q}3^{g(j_*-k)}\E[Y_P]`.

*The row is a quadratic form.*  The Loewner order on doubled blocks *is* the
inequality of doubled quadratic forms, so the frozen row — which is stated on
the scalar `X \cdot \bfA X` rather than on the matrices — is the cell bound read
at one vector.  The aligned cell `z + \cus_k^{\mathbf q}` is the translate of the
adapted cell by its own centre, and it lies in the window because it lies in
`\cus_s^{\mathbf q}`: that containment is the child-in-parent lemma
`Recurrence.adaptedCellAt_subset_adaptedCell`, whose hypothesis is exactly the
membership of the centre that the frozen statement's index set `Ctr` is defined
by.  The average over the finite centre set is then below the same bound, the
empty average being zero by the convention `(0:ℝ)^{-1} = 0`.

*The series.*  `ResponseRowSeries` sums the scale weights against the burn
discounts to the printed `3^{-\lambda(s-j_*)}(3^{\lambda-g}-1)^{-1}`.

The adjoint row is not a second argument.  The printed proof says *"the identity
`\bfA_*^{-1} = \mathbf R\bfA\mathbf R` proves its adjoint analogue"*, and that is
literally what happens: the annealed sharp adjoint is the block reflection of the
annealed block, the dual reference block is the reflection of the reference
block, and the reflection acts on the doubled quadratic form by swapping the
halves of the vector.  The adjoint row at `X` is therefore the primal row at the
swapped vector, with no estimate repeated.

Neither row consumes the lower cut `Klo < j_*` of the frozen statement's
partial-sum form: the bound holds for every cut, the sum being empty at or above
the alignment scale.  Nor is the terminal scale bound `s < t` used.  Beyond
those two, clause B consumes none of the frozen statement's stationarity, its
cross-grid data `(K_{hop}, \mathbf q')`, its target family `\mathcal W`, its
decay exponent `\rho`, its buffer `\ell_0`, its second and terminal witnesses,
or the normalization of the law: the mean `\E[Y_P]` enters only through
`0 \leq \E[Y_P]`, which holds for every measure because the multiplier is
pointwise at least one.  Of the coarse ellipticity assumption only
`refBlock_isSymm` and `refBlock_posDef` are read.
-/

namespace Homogenization
namespace HighContrast
namespace SourceControl

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The average over a finite index set -/

/-- **A finite average of quantities below a nonnegative bound is below that
bound.**  The empty average is zero by the convention `(0:ℝ)^{-1} = 0`, which is
why the bound must be nonnegative; this is the degenerate instantiation the
printed row allows, an all-earlier scale whose cells miss
`\cus_s^{\mathbf q}`. -/
theorem inv_card_mul_sum_le {ι : Type*} (T : Finset ι) (f : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hf : ∀ w ∈ T, f w ≤ c) : ((T.card : ℝ)⁻¹ * ∑ w ∈ T, f w) ≤ c := by
  rcases Finset.eq_empty_or_nonempty T with rfl | hT
  · simpa using hc
  · have hcard : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hT
    have hsum : ∑ w ∈ T, f w ≤ (T.card : ℝ) * c := by
      refine le_trans (Finset.sum_le_sum hf) (le_of_eq ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le))
      (le_of_eq ?_)
    field_simp

/-! ## The sharp adjoint of the annealed block -/

/-- **The annealed sharp adjoint is the reflection of the annealed block**, the
printed identity `\bfA_*^{-1} = \mathbf R\bfA\mathbf R` at the level of
expectations: the reflection permutes entries, so it commutes with the
entrywise expectation. -/
theorem annealedStarInv_eq_blockReflect (P : Measure (CoeffSpace d))
    (U : Set (Vec d)) : annealedStarInv P U = blockReflect (annealedBlock P U) :=
  rfl

/-! ## The annealed cell bound with the burn discount retained -/

variable {P : Measure (CoeffSpace d)} {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ}
  {K Cd : ℝ} {jStar M : ℤ} {Y : CoeffSpace d → ℝ}

/-- **The annealed cell bound below the burn**
`\E[\bfA(y + \cus_r^{\mathbf s})] \leq B_{\mathbf s}3^{g(j_*-r)_+}\E[Y_P]\mathbf E`:
the pathwise bound of `e.source.adapted.bound` integrated against the
law, with the burn discount retained.  At or above the alignment scale the
discount is one and this reduces to the terminal comparison; the all-earlier row
needs it at the scales strictly below, where it is not. -/
theorem annealedBlock_le_blockScale_burn (hE : IsSymmetricBlockMat E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (r : ℤ) (y : Vec d)
    (hcont : adaptedCellTranslate (roundedGrid jStar nu) r y ⊆ centeredCube d M) :
    BlockMatLoewnerLE
      (annealedBlock P (adaptedCellTranslate (roundedGrid jStar nu) r y))
      (blockScale (boundaryConst Cd g nu * burnDiscount g jStar r * ∫ a, Y a ∂P) E) := by
  have hint := Transport.hasIntegrableCoarseBlock_adaptedCellTranslate hY hnu hq r y hcont
  refine blockMatLoewnerLE_of_le ?_
  rw [toFullBlockMat_annealedBlock hint, toFullBlockMat_blockScale,
    show (boundaryConst Cd g nu * burnDiscount g jStar r * ∫ a, Y a ∂P) •
        toFullBlockMat E =
      ∫ a, (boundaryConst Cd g nu * burnDiscount g jStar r * Y a) •
        toFullBlockMat E ∂P by
      rw [integral_smul_const, integral_const_mul]]
  refine integral_mono' (integrable_toFullBlockMat hint)
    (((Transport.integrable_of_isWindowMultiplier hY).const_mul _).smul_const _) ?_
  filter_upwards
    [Transport.ae_blockMatLoewnerLE_coarseBlock_adaptedCellTranslate hY hnu r y hcont] with a ha
  have h := le_of_blockMatLoewnerLE (isSymmetricBlockMat_coarseBlock _ a)
    (isSymmetricBlockMat_blockScale _ hE) ha
  rwa [toFullBlockMat_blockScale] at h

/-- **The annealed cell bound read as a quadratic form**, on the aligned cell
`z + \cus_k^{\mathbf q}` of the all-earlier scales.  The doubled Loewner order is
the inequality of doubled quadratic forms, and the aligned cell is the translate
of the adapted cell by its own centre. -/
theorem blockVecDot_annealedBlock_adaptedCellAt_le (hE : IsSymmetricBlockMat E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (k : ℤ) (w : Fin d → ℤ)
    (hcont : adaptedCellAt (roundedGrid jStar nu) k w ⊆ centeredCube d M)
    (X : BlockVec d) :
    blockVecDot X (blockMatVecMul
        (annealedBlock P (adaptedCellAt (roundedGrid jStar nu) k w)) X) ≤
      burnDiscount g jStar k *
        (boundaryConst Cd g nu * (∫ a, Y a ∂P) *
          blockVecDot X (blockMatVecMul E X)) := by
  rw [adaptedCellAt_eq_adaptedCellTranslate] at hcont ⊢
  have h := annealedBlock_le_blockScale_burn hE hY hnu hq k
    (adaptedCellCenter (roundedGrid jStar nu) k w) hcont X
  rw [Sharp.blockVecDot_blockMatVecMul_blockScale,
    show (boundaryConst Cd g nu * burnDiscount g jStar k * ∫ a, Y a ∂P) *
        blockVecDot X (blockMatVecMul E X) =
      burnDiscount g jStar k * (boundaryConst Cd g nu * (∫ a, Y a ∂P) *
        blockVecDot X (blockMatVecMul E X)) from by ring] at h
  linarith only [h]

/-! ## The averaged row at one all-earlier scale -/

/-- **The averaged annealed row at one scale below the alignment.**  Every
aligned cell whose centre lies in `\cus_s^{\mathbf q}` lies in it, hence in the
window, so every term of the average obeys the cell bound; the average therefore
obeys it too. -/
theorem inv_card_mul_sum_blockVecDot_le (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {s : ℤ} (hs : jStar ≤ s)
    (hcont : adaptedCell (roundedGrid jStar nu) s ⊆ centeredCube d M)
    {Ctr : ℤ → Finset (Fin d → ℤ)}
    (hCtr : ∀ k : ℤ, k < jStar → ∀ w : Fin d → ℤ,
      w ∈ Ctr k ↔
        adaptedCellCenter (roundedGrid jStar nu) k w ∈
          adaptedCell (roundedGrid jStar nu) s)
    {k : ℤ} (hk : k < jStar) (X : BlockVec d) :
    (((Ctr k).card : ℝ)⁻¹ *
        ∑ w ∈ Ctr k,
          blockVecDot X (blockMatVecMul
            (annealedBlock P (adaptedCellAt (roundedGrid jStar nu) k w)) X)) ≤
      burnDiscount g jStar k *
        (boundaryConst Cd g nu * (∫ a, Y a ∂P) *
          blockVecDot X (blockMatVecMul E X)) := by
  refine inv_card_mul_sum_le _ _ ?_ ?_
  · exact mul_nonneg (Transport.zero_lt_burnDiscount g jStar k).le
      (mul_nonneg (mul_nonneg (Transport.zero_le_boundaryConst hCd hg nu)
        (integral_nonneg fun a => le_trans zero_le_one (hY.one_le a)))
        (Sharp.zero_le_blockVecDot_blockMatVecMul_of_blockPosDef hEpd X))
  · intro w hw
    exact blockVecDot_annealedBlock_adaptedCellAt_le hE hY hnu hq k w
      ((Recurrence.adaptedCellAt_subset_adaptedCell (Recurrence.posDef_of_isRoundedGrid hq)
        (le_trans hk.le hs) ((hCtr k hk w).mp hw)).trans hcont) X

/-! ## The two rows -/

/-- **The all-earlier primal row** at the response scale, in the partial-sum
form of the frozen statement: the scale-weighted sum of the averaged annealed
responses of the all-earlier aligned cells centred in `\cus_s^{\mathbf q}` is
below `B_{\mathbf q}\E[Y_P](3^{\lambda-g}-1)^{-1}3^{-\lambda(s-j_*)}\mathbf E`. -/
theorem response_row (hCd : 0 ≤ Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {s : ℤ} (hs : jStar ≤ s)
    (hcont : adaptedCell (roundedGrid jStar nu) s ⊆ centeredCube d M) {lam : ℝ}
    (hlam : g < lam) {Ctr : ℤ → Finset (Fin d → ℤ)}
    (hCtr : ∀ k : ℤ, k < jStar → ∀ w : Fin d → ℤ,
      w ∈ Ctr k ↔
        adaptedCellCenter (roundedGrid jStar nu) k w ∈
          adaptedCell (roundedGrid jStar nu) s)
    (Klo : ℤ) (X : BlockVec d) :
    ∑ k ∈ Finset.Ico Klo jStar,
        (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) *
          (((Ctr k).card : ℝ)⁻¹ *
            ∑ w ∈ Ctr k,
              blockVecDot X (blockMatVecMul
                (annealedBlock P (adaptedCellAt (roundedGrid jStar nu) k w)) X)) ≤
      boundaryConst Cd g nu * (∫ a, Y a ∂P) / ((3 : ℝ) ^ (lam - g) - 1) *
          (3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) *
        blockVecDot X (blockMatVecMul E X) := by
  have hcoef : (0 : ℝ) ≤ boundaryConst Cd g nu * (∫ a, Y a ∂P) *
      blockVecDot X (blockMatVecMul E X) :=
    mul_nonneg (mul_nonneg (Transport.zero_le_boundaryConst hCd hg nu)
        (integral_nonneg fun a => le_trans zero_le_one (hY.one_le a)))
      (Sharp.zero_le_blockVecDot_blockMatVecMul_of_blockPosDef hEpd X)
  have hstep : ∀ k ∈ Finset.Ico Klo jStar,
      (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) *
          (((Ctr k).card : ℝ)⁻¹ *
            ∑ w ∈ Ctr k,
              blockVecDot X (blockMatVecMul
                (annealedBlock P (adaptedCellAt (roundedGrid jStar nu) k w)) X)) ≤
        ((3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) * burnDiscount g jStar k) *
          (boundaryConst Cd g nu * (∫ a, Y a ∂P) *
            blockVecDot X (blockMatVecMul E X)) := by
    intro k hk
    refine le_trans (mul_le_mul_of_nonneg_left
      (inv_card_mul_sum_blockVecDot_le hCd hg hE hEpd hY hnu hq hs hcont hCtr
        (Finset.mem_Ico.mp hk).2 X)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) (le_of_eq (by ring))
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_mul]
  exact le_trans (mul_le_mul_of_nonneg_right
    (sum_rpow_mul_burnDiscount_le hlam jStar s Klo) hcoef) (le_of_eq (by ring))

/-- **The all-earlier adjoint row**, the printed analogue with `(\bfA,\mathbf E)`
replaced by `(\bfA_*^{-1},\mathbf E_*^{-1})`.  No estimate is repeated: the
annealed sharp adjoint and the dual reference block are the reflections of the
annealed block and the reference block, and the reflection acts on the doubled
quadratic form by swapping the halves of the vector, so this row at `X` is the
primal row at the swapped vector. -/
theorem response_row_adjoint (hCd : 0 ≤ Cd) (hg : g < 1) (hE : IsSymmetricBlockMat E)
    (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) {s : ℤ} (hs : jStar ≤ s)
    (hcont : adaptedCell (roundedGrid jStar nu) s ⊆ centeredCube d M) {lam : ℝ}
    (hlam : g < lam) {Ctr : ℤ → Finset (Fin d → ℤ)}
    (hCtr : ∀ k : ℤ, k < jStar → ∀ w : Fin d → ℤ,
      w ∈ Ctr k ↔
        adaptedCellCenter (roundedGrid jStar nu) k w ∈
          adaptedCell (roundedGrid jStar nu) s)
    (Klo : ℤ) (X : BlockVec d) :
    ∑ k ∈ Finset.Ico Klo jStar,
        (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) *
          (((Ctr k).card : ℝ)⁻¹ *
            ∑ w ∈ Ctr k,
              blockVecDot X (blockMatVecMul
                (annealedStarInv P (adaptedCellAt (roundedGrid jStar nu) k w)) X)) ≤
      boundaryConst Cd g nu * (∫ a, Y a ∂P) / ((3 : ℝ) ^ (lam - g) - 1) *
          (3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) *
        blockVecDot X (blockMatVecMul (blockReflect E) X) := by
  have h := response_row hCd hg hE hEpd hY hnu hq hs hcont hlam hCtr Klo (X.2, X.1)
  simpa only [annealedStarInv_eq_blockReflect, blockVecDot_blockMatVecMul_blockReflect]
    using h

/-! ## The frozen clause -/

/-- **Clause B of `e.source.adapted.bound`**: the all-earlier response row
in both orientations, in the partial-sum form the frozen statement carries.

Neither the terminal scale bound `s < t` nor the lower cut `Klo < j_*` is
consumed; both are carried because the printed statement carries them. -/
theorem response_row_of_isWindowMultiplier (hCd : 0 ≤ Cd) (hg : g < 1)
    (hE : IsSymmetricBlockMat E) (hEpd : Book.Ch02.BlockPosDef E)
    (hY : IsWindowMultiplier P g E Ψ K Cd jStar M Y) {nu : Mat d} (hnu : nu.PosDef)
    (hq : IsRoundedGrid jStar (roundedGrid jStar nu)) (t : ℤ) :
    ∀ s : ℤ, jStar ≤ s → s < t →
      adaptedCell (roundedGrid jStar nu) s ⊆ centeredCube d M →
      ∀ lam : ℝ, g < lam →
        ∀ Ctr : ℤ → Finset (Fin d → ℤ),
          (∀ k : ℤ, k < jStar → ∀ w : Fin d → ℤ,
            w ∈ Ctr k ↔
              adaptedCellCenter (roundedGrid jStar nu) k w ∈
                adaptedCell (roundedGrid jStar nu) s) →
          ∀ Klo : ℤ, Klo < jStar → ∀ X : BlockVec d,
            ∑ k ∈ Finset.Ico Klo jStar,
                (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) *
                  (((Ctr k).card : ℝ)⁻¹ *
                    ∑ w ∈ Ctr k,
                      blockVecDot X (blockMatVecMul
                        (annealedBlock P
                          (adaptedCellAt (roundedGrid jStar nu) k w)) X)) ≤
              boundaryConst Cd g nu * (∫ a, Y a ∂P) / ((3 : ℝ) ^ (lam - g) - 1) *
                  (3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) *
                blockVecDot X (blockMatVecMul E X) ∧
            ∑ k ∈ Finset.Ico Klo jStar,
                (3 : ℝ) ^ (lam * ((k : ℝ) - (s : ℝ))) *
                  (((Ctr k).card : ℝ)⁻¹ *
                    ∑ w ∈ Ctr k,
                      blockVecDot X (blockMatVecMul
                        (annealedStarInv P
                          (adaptedCellAt (roundedGrid jStar nu) k w)) X)) ≤
              boundaryConst Cd g nu * (∫ a, Y a ∂P) / ((3 : ℝ) ^ (lam - g) - 1) *
                  (3 : ℝ) ^ (-lam * ((s : ℝ) - (jStar : ℝ))) *
                blockVecDot X (blockMatVecMul (blockReflect E) X) := by
  intro s hs _hst hcont lam hlam Ctr hCtr Klo _hKlo X
  exact ⟨response_row hCd hg hE hEpd hY hnu hq hs hcont hlam hCtr Klo X,
    response_row_adjoint hCd hg hE hEpd hY hnu hq hs hcont hlam hCtr Klo X⟩

end

end SourceControl
end HighContrast
end Homogenization
