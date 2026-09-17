import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsStatBlock
import HCPoly.Entry.Annealed.AlignedSubdivision

/-!
# The annealed block of a descendant cell depends only on its inner index

In the descendant sum of `p.response.transfer` the terminal cell is cut into the
`3^{(H+n)d}` aligned cells of generation `s - n`, indexed by `3^n w + z` with `w` the index of
the scale-`s` cell containing the descendant and `z` the index of the descendant inside that
cell.  Stationarity acts on the outer index alone: the generation-`s` translation `3^s q w` is
an integer vector once `s ≥ j_*`, the law is invariant under integer translations, and the
recentring `a_- = a - g`, `a_+ = aᵀ + g` adds a constant matrix field, which commutes with
translation.  Hence the annealed block of the descendant cell does not depend on `w`, only on
the inner index `z`.

This is the descendant form of the landed
`annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq`, whose case `n = 0` recovers that statement.
-/

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter measurable_translateCoeff
  translateCoeff)
open Homogenization.HighContrast (adaptedCell adaptedCellTranslate)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- A translated adapted cell is the translate of the centred adapted cell: both are the
image of `⋄_j^q` under `x ↦ y + x`. -/
private theorem adaptedCellTranslate_eq_translateSet {d : ℕ} (q : Mat d) (j : ℤ) (y : Vec d) :
    HighContrast.adaptedCellTranslate q j y = translateSet y (HighContrast.adaptedCell q j) := by
  ext x
  simp only [HighContrast.adaptedCellTranslate, translateSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [← hwxy, add_comm]⟩
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [hwxy, add_comm]⟩

/-- Translation by a sum is the composite of the two translations. -/
private theorem translateSet_add {d : ℕ} (a b : Vec d) (U : Set (Vec d)) :
    translateSet (a + b) U = translateSet a (translateSet b U) := by
  ext x
  simp only [translateSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨y + b, ⟨y, hy, rfl⟩, ?_⟩
    rw [hx]
    abel
  · rintro ⟨y, ⟨y₀, hy₀, hy⟩, hx⟩
    refine ⟨y₀, hy₀, ?_⟩
    rw [hx, hy]
    abel

/-- The centre of the grouped descendant cell is the outer scale-`j` centre plus the inner
scale-`(j - n)` centre: the scaled index `3^n w + z` distributes over the additive and
homogeneous map `matVecMul q`. -/
private theorem adaptedCellCenter_add_scale {d : ℕ} (q : Mat d) (j : ℤ) (n : ℕ)
    (w z : Fin d → ℤ) :
    adaptedCellCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)
      = adaptedCellCenter q j w + adaptedCellCenter q (j - (n : ℤ)) z := by
  have hvec : (fun i => ((3 ^ n * w i + z i : ℤ) : ℝ))
      = (3 : ℝ) ^ n • (fun i => (w i : ℝ)) + (fun i => (z i : ℝ)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  calc
    adaptedCellCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)
        = (3 : ℝ) ^ (j - (n : ℤ))
            • matVecMul q (fun i => ((3 ^ n * w i + z i : ℤ) : ℝ)) := rfl
    _ = (3 : ℝ) ^ (j - (n : ℤ))
            • matVecMul q ((3 : ℝ) ^ n • (fun i => (w i : ℝ)) + (fun i => (z i : ℝ))) := by
          rw [hvec]
    _ = (3 : ℝ) ^ (j - (n : ℤ))
            • (matVecMul q ((3 : ℝ) ^ n • (fun i => (w i : ℝ)))
                + matVecMul q (fun i => (z i : ℝ))) := by
          rw [matVecMul_add]
    _ = (3 : ℝ) ^ (j - (n : ℤ))
            • ((3 : ℝ) ^ n • matVecMul q (fun i => (w i : ℝ))
                + matVecMul q (fun i => (z i : ℝ))) := by
          rw [matVecMul_smul]
    _ = ((3 : ℝ) ^ (j - (n : ℤ)) * (3 : ℝ) ^ n)
            • matVecMul q (fun i => (w i : ℝ))
          + (3 : ℝ) ^ (j - (n : ℤ)) • matVecMul q (fun i => (z i : ℝ)) := by
          rw [smul_add, smul_smul]
    _ = (3 : ℝ) ^ j • matVecMul q (fun i => (w i : ℝ))
          + (3 : ℝ) ^ (j - (n : ℤ)) • matVecMul q (fun i => (z i : ℝ)) := by
          have hpow : (3 : ℝ) ^ (j - (n : ℤ)) * (3 : ℝ) ^ n = (3 : ℝ) ^ j := by
            rw [← zpow_natCast (3 : ℝ) n, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
            congr 1
            omega
          rw [hpow]
    _ = adaptedCellCenter q j w + adaptedCellCenter q (j - (n : ℤ)) z := rfl

/-- The grouped descendant cell is the integer-scale translate of the inner descendant cell by
the outer scale-`j` centre. -/
private theorem adaptedCellAtCenter_descendant_eq_translateSet {d : ℕ} (q : Mat d) (j : ℤ) (n : ℕ)
    (w z : Fin d → ℤ) :
    adaptedCellAtCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)
      = translateSet (adaptedCellCenter q j w) (adaptedCellAtCenter q (j - (n : ℤ)) z) := by
  calc
    adaptedCellAtCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)
        = adaptedCellTranslate q (j - (n : ℤ))
            (adaptedCellCenter q (j - (n : ℤ)) (fun i => 3 ^ n * w i + z i)) := rfl
    _ = adaptedCellTranslate q (j - (n : ℤ))
            (adaptedCellCenter q j w + adaptedCellCenter q (j - (n : ℤ)) z) := by
          rw [adaptedCellCenter_add_scale]
    _ = translateSet (adaptedCellCenter q j w + adaptedCellCenter q (j - (n : ℤ)) z)
            (adaptedCell q (j - (n : ℤ))) := by
          rw [adaptedCellTranslate_eq_translateSet]
    _ = translateSet (adaptedCellCenter q j w)
            (translateSet (adaptedCellCenter q (j - (n : ℤ)) z)
              (adaptedCell q (j - (n : ℤ)))) := by
          rw [translateSet_add]
    _ = translateSet (adaptedCellCenter q j w) (adaptedCellAtCenter q (j - (n : ℤ)) z) := by
          unfold adaptedCellAtCenter
          rw [adaptedCellTranslate_eq_translateSet]

/-- The coarse block of the recentred field `a_- = a - g` on the integer translate of a set is
the coarse block of the translated recentred field on the set.  The recentring subtracts the
constant matrix field `g`, which is unaffected by translation, so the covariance is that of the
coarse block matrix itself. -/
private theorem coarseBlockMatrix_translateSet_intTranslation_respCoeffMinus {d : ℕ}
    (zz : Fin d → ℤ) (V : Set (Vec d)) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (translateSet (Source.AKL.intTranslation zz) V) (respCoeffMinus F a)
      = coarseBlockMatrix V (respCoeffMinus F (translateCoeff zz a)) := by
  rw [coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae zz a.1] with x hxpt
  exact (congrArg (fun M : Mat d => M - respg F) hxpt).symm

/-- The coarse block of the recentred field `a_+ = aᵀ + g` on the integer translate of a set is
the coarse block of the translated recentred field on the set.  The recentring adds the constant
matrix field `g`, which is unaffected by translation, so the covariance is that of the coarse
block matrix itself. -/
private theorem coarseBlockMatrix_translateSet_intTranslation_respCoeffPlus {d : ℕ}
    (zz : Fin d → ℤ) (V : Set (Vec d)) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (translateSet (Source.AKL.intTranslation zz) V) (respCoeffPlus F a)
      = coarseBlockMatrix V (respCoeffPlus F (translateCoeff zz a)) := by
  rw [coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae zz a.1] with x hxpt
  exact (congrArg (fun M : Mat d => matTranspose M + respg F) hxpt).symm

/-- Stationarity of a scalar functional of the coefficient field: precomposing with an integer
translation leaves the `P`-integral unchanged. -/
private theorem integral_comp_translateCoeff_eq_aux {d : ℕ} (P : Measure (CoeffSpace d))
    (hstat : IsStationaryLaw P) (z : Fin d → ℤ) (f : CoeffSpace d → ℝ)
    (hf : AEStronglyMeasurable f P) :
    (∫ a, f (translateCoeff z a) ∂P) = ∫ a, f a ∂P := by
  have h := integral_map (μ := P) (φ := translateCoeff z)
    (measurable_translateCoeff z).aemeasurable (f := f) (by rw [hstat z]; exact hf)
  rw [hstat z] at h
  exact h.symm

/-- Stationarity of a scalar functional of a descendant cell: the outer centre of a scale-`j ≥
j_*` aligned cell is an integer translation and the law is invariant under integer translations,
so the `P`-integral of the functional of the grouped descendant cell equals that of the inner
cell. -/
private theorem integral_descendantCell_eq_aux {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (w z : Fin d → ℤ)
    (G : Set (Vec d) → CoeffSpace d → ℝ)
    (hG : ∀ (zz : Fin d → ℤ) (a : CoeffSpace d),
      G (translateSet (Source.AKL.intTranslation zz)
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)) a
        = G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) (translateCoeff zz a))
    (hmeas : AEStronglyMeasurable
      (G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)) P) :
    (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) a ∂P)
      = ∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) a ∂P := by
  obtain ⟨zz, hzz⟩ := Annealed.adaptedCellCenter_eq_intTranslation jStar m hj w
  have hcongr : (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) a ∂P)
      = ∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
          (translateCoeff zz a) ∂P := by
    apply integral_congr_ae
    filter_upwards with a
    rw [adaptedCellAtCenter_descendant_eq_translateSet, hzz]
    exact hG zz a
  rw [hcongr]
  exact integral_comp_translateCoeff_eq_aux P hstat zz _ hmeas

/-- **The annealed block of a descendant cell is independent of the scale-`j` cell containing
it, minus sign.**  For a stationary law and a scale `j >= j_*`, the annealed block of the
generation-`(j - n)` aligned cell at the grouped index `3^n w + z` is the annealed block of the
generation-`(j - n)` aligned cell at the inner index `z`. -/
theorem annealedBlockOf_descendant_respCoeffMinus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (w z : Fin d → ℤ)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffMinus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffMinus F a)).lowerRight i k) P) :
    ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
            (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F)).upperLeft
        = (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
            (respCoeffMinus F)).upperLeft)
      ∧ ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
            (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F)).lowerRight
        = (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
            (respCoeffMinus F)).lowerRight) := by
  constructor
  · ext i k
    have h := integral_descendantCell_eq_aux P hstat jStar m j hj n w z
      (fun V a => (coarseBlockMatrix V (respCoeffMinus F a)).upperLeft i k)
      (fun zz a => congrArg (fun B : BlockMat d => B.upperLeft i k)
        (coarseBlockMatrix_translateSet_intTranslation_respCoeffMinus zz
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) F a))
      (hmeas i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
              (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F a)).upperLeft i k ∂P := rfl
    have hred' : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffMinus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
              (respCoeffMinus F a)).upperLeft i k ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_descendantCell_eq_aux P hstat jStar m j hj n w z
      (fun V a => (coarseBlockMatrix V (respCoeffMinus F a)).lowerRight i k)
      (fun zz a => congrArg (fun B : BlockMat d => B.lowerRight i k)
        (coarseBlockMatrix_translateSet_intTranslation_respCoeffMinus zz
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) F a))
      (hmeas' i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
              (fun i => 3 ^ n * w i + z i)) (respCoeffMinus F a)).lowerRight i k ∂P := rfl
    have hred' : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffMinus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
              (respCoeffMinus F a)).lowerRight i k ∂P := rfl
    rw [hred, hred']
    exact h

/-- **The annealed block of a descendant cell is independent of the scale-`j` cell containing
it, plus sign.**  The adjoint twin of `annealedBlockOf_descendant_respCoeffMinus_eq`, for the
recentred family `a_+ = a^t + g`. -/
theorem annealedBlockOf_descendant_respCoeffPlus_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (n : ℕ) (w z : Fin d → ℤ)
    (hmeas : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffPlus F a)).upperLeft i k) P)
    (hmeas' : ∀ i k : Fin d, AEStronglyMeasurable (fun a =>
      (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffPlus F a)).lowerRight i k) P) :
    ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
            (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F)).upperLeft
        = (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
            (respCoeffPlus F)).upperLeft)
      ∧ ((annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
            (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F)).lowerRight
        = (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
            (respCoeffPlus F)).lowerRight) := by
  constructor
  · ext i k
    have h := integral_descendantCell_eq_aux P hstat jStar m j hj n w z
      (fun V a => (coarseBlockMatrix V (respCoeffPlus F a)).upperLeft i k)
      (fun zz a => congrArg (fun B : BlockMat d => B.upperLeft i k)
        (coarseBlockMatrix_translateSet_intTranslation_respCoeffPlus zz
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) F a))
      (hmeas i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
              (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F a)).upperLeft i k ∂P := rfl
    have hred' : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffPlus F)).upperLeft i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
              (respCoeffPlus F a)).upperLeft i k ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_descendantCell_eq_aux P hstat jStar m j hj n w z
      (fun V a => (coarseBlockMatrix V (respCoeffPlus F a)).lowerRight i k)
      (fun zz a => congrArg (fun B : BlockMat d => B.lowerRight i k)
        (coarseBlockMatrix_translateSet_intTranslation_respCoeffPlus zz
          (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z) F a))
      (hmeas' i k)
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
        (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ))
              (fun i => 3 ^ n * w i + z i)) (respCoeffPlus F a)).lowerRight i k ∂P := rfl
    have hred' : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
        (respCoeffPlus F)).lowerRight i k
          = ∫ a, (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) (j - (n : ℤ)) z)
              (respCoeffPlus F a)).lowerRight i k ∂P := rfl
    rw [hred, hred']
    exact h

end

end Homogenization.HighContrast.Multiscale
