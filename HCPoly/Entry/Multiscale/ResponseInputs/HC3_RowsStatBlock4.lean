import HCPoly.Entry.Multiscale.ResponseInputs.HC3_RowsStatBlock

/-!
# The whole annealed block of an aligned cell is cell-independent

For a stationary law `P` and a scale `j` above `j_*`, every aligned cell of the generation is an
integer translate of the centred adapted cell, the law is invariant under integer translations,
and the recentring of `p.response.transfer` subtracts (respectively adds) a constant matrix field,
which commutes with translation.  Consequently the whole annealed block of the recentred field
`a_- = a - g` or `a_+ = aᵀ + g` is the same `2d`-by-`2d` matrix at every cell of the generation.

`HC3_RowsStatBlock` records this for the two diagonal sub-blocks only.  The mean cancellation of
`p.response.transfer` — "the constant cell means cancel after expectation, because the scale-`s`
translations are integral" — needs the whole block, because the annealed cell mean of the
optimizer state is `x + R 𝐀 x` and the off-diagonal sub-blocks enter it.  This file supplies the
off-diagonal half and packages the four fields into a single block equality.
-/

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter measurable_translateCoeff
  translateCoeff)
namespace Homogenization.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- A translated adapted cell is the translate of the centred adapted cell: both are the image of
`⋄_j^q` under `x ↦ y + x`. -/
private theorem adaptedCellTranslate_eq_translateSet {d : ℕ} (q : Mat d) (j : ℤ) (y : Vec d) :
    HighContrast.adaptedCellTranslate q j y = translateSet y (HighContrast.adaptedCell q j) := by
  ext x
  simp only [HighContrast.adaptedCellTranslate, translateSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [← hwxy, add_comm]⟩
  · rintro ⟨w, hw, hwxy⟩
    exact ⟨w, hw, by rw [hwxy, add_comm]⟩

/-- The coarse block of the recentred field `a_- = a - g` on an integer translate of a cell is the
coarse block of the translated recentred field on the cell.  The recentring subtracts the constant
matrix field `g`, which is unaffected by translation, so the covariance is that of the coarse block
matrix itself. -/
private theorem coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus {d : ℕ}
    (q : Mat d) (j : ℤ) (z : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCellTranslate q j (Source.AKL.intTranslation z))
        (respCoeffMinus F a)
      = coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffMinus F (translateCoeff z a)) := by
  rw [adaptedCellTranslate_eq_translateSet,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae z a.1] with x hxpt
  exact (congrArg (fun M : Mat d => M - respg F) hxpt).symm

/-- The coarse block of the recentred field `a_+ = aᵀ + g` on an integer translate of a cell is the
coarse block of the translated recentred field on the cell.  The recentring adds the constant matrix
field `g`, which is unaffected by translation, so the covariance is that of the coarse block matrix
itself. -/
private theorem coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus {d : ℕ}
    (q : Mat d) (j : ℤ) (z : Fin d → ℤ) (F : BlockMat d) (a : CoeffSpace d) :
    coarseBlockMatrix (HighContrast.adaptedCellTranslate q j (Source.AKL.intTranslation z))
        (respCoeffPlus F a)
      = coarseBlockMatrix (HighContrast.adaptedCell q j) (respCoeffPlus F (translateCoeff z a)) := by
  rw [adaptedCellTranslate_eq_translateSet,
    coarseBlockMatrix_translateSet_eq_translateCoeffField]
  apply coarseBlockMatrix_congr_of_ae_eq
  apply ae_restrict_of_ae
  filter_upwards [Source.AKL.translateField_ae z a.1] with x hxpt
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

/-- Stationarity of a scalar functional of an aligned cell: an aligned cell is an integer
translate of the centred cell, and the law is invariant under integer translations, so the
`P`-integral of the functional is the same at every aligned cell of the scale. -/
private theorem integral_cellFunctional_adaptedCellAtCenter_eq_aux {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (G : Set (Vec d) → CoeffSpace d → ℝ)
    (hG : ∀ (z : Fin d → ℤ) (a : CoeffSpace d),
      G (HighContrast.adaptedCellTranslate (explicitRoundedGrid jStar m) j (Source.AKL.intTranslation z))
          a
        = G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a))
    (hmeas : AEStronglyMeasurable (G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)) P) :
    (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) a ∂P)
      = ∫ a, G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) a ∂P := by
  obtain ⟨z, hz⟩ := Annealed.adaptedCellCenter_eq_intTranslation jStar m hj w
  have hcongr : (∫ a, G (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) a ∂P) =
      ∫ a, G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a) ∂P := by
    apply integral_congr_ae
    filter_upwards with a
    change G (HighContrast.adaptedCellTranslate (explicitRoundedGrid jStar m) j
          (adaptedCellCenter (explicitRoundedGrid jStar m) j w)) a
        = G (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a)
    rw [hz]
    exact hG z a
  rw [hcongr]
  exact integral_comp_translateCoeff_eq_aux P hstat z _ hmeas

/-- Stationarity of one entry of an aligned-cell block: if the block function reads a translated
cell as the centred cell read at the translated coefficient field, then the `P`-integral of any
`blockMatEntry` of the block is the same at every aligned cell of generation `j ≥ j_*`. -/
private theorem integral_cellEntry_adaptedCellAtCenter_eq {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (B : Set (Vec d) → CoeffSpace d → BlockMat d)
    (hB : ∀ (z : Fin d → ℤ) (a : CoeffSpace d),
      B (HighContrast.adaptedCellTranslate (explicitRoundedGrid jStar m) j (Source.AKL.intTranslation z)) a
        = B (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (translateCoeff z a))
    (α β : BlockCoord d)
    (hmeas : AEStronglyMeasurable
      (fun a => blockMatEntry (B (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) a) α β) P) :
    (∫ a, blockMatEntry (B (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) a) α β ∂P)
      = ∫ a, blockMatEntry (B (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) a) α β ∂P :=
  integral_cellFunctional_adaptedCellAtCenter_eq_aux P hstat jStar m j hj w
    (fun V a => blockMatEntry (B V a) α β)
    (fun z a => congrArg (fun M : BlockMat d => blockMatEntry M α β) (hB z a))
    hmeas

/-- **The whole annealed block of the recentred field is the same on every aligned cell, minus
sign.**  For a stationary law `P` and the recentred coefficient `a_- = a - g` of
`p.response.transfer`, the `P`-entrywise annealed block of the pathwise coarse block on an aligned
cell of scale `j ≥ j_*` is the annealed block of the centred cell, independently of the cell index
`w`.  This is the full `BlockMat` form, off-diagonal sub-blocks included. -/
theorem annealedBlockOf_adaptedCellAtCenter_respCoeffMinus_eq_full {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (hmeas : ∀ (α β : BlockCoord d),
      AEStronglyMeasurable (fun a => blockMatEntry
        (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
          (respCoeffMinus F a)) α β) P) :
    annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) (respCoeffMinus F)
      = annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (respCoeffMinus F) := by
  apply blockMat_ext
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffMinus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inl i) (Sum.inl k) (hmeas (Sum.inl i) (Sum.inl k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).upperLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffMinus F a)) (Sum.inl i) (Sum.inl k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).upperLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffMinus F a)) (Sum.inl i) (Sum.inl k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffMinus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inl i) (Sum.inr k) (hmeas (Sum.inl i) (Sum.inr k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).upperRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffMinus F a)) (Sum.inl i) (Sum.inr k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).upperRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffMinus F a)) (Sum.inl i) (Sum.inr k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffMinus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inr i) (Sum.inl k) (hmeas (Sum.inr i) (Sum.inl k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).lowerLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffMinus F a)) (Sum.inr i) (Sum.inl k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).lowerLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffMinus F a)) (Sum.inr i) (Sum.inl k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffMinus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffMinus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inr i) (Sum.inr k) (hmeas (Sum.inr i) (Sum.inr k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffMinus F)).lowerRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffMinus F a)) (Sum.inr i) (Sum.inr k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffMinus F)).lowerRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffMinus F a)) (Sum.inr i) (Sum.inr k) ∂P := rfl
    rw [hred, hred']
    exact h

/-- **The whole annealed block of the recentred field is the same on every aligned cell, plus
sign.**  For a stationary law `P` and the recentred coefficient `a_+ = aᵀ + g` of
`p.response.transfer`, the `P`-entrywise annealed block of the pathwise coarse block on an aligned
cell of scale `j ≥ j_*` is the annealed block of the centred cell, independently of the cell index
`w`.  This is the full `BlockMat` form, off-diagonal sub-blocks included. -/
theorem annealedBlockOf_adaptedCellAtCenter_respCoeffPlus_eq_full {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P) (jStar : ℕ) (m : Mat d)
    (F : BlockMat d) (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ)
    (hmeas : ∀ (α β : BlockCoord d),
      AEStronglyMeasurable (fun a => blockMatEntry
        (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
          (respCoeffPlus F a)) α β) P) :
    annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) (respCoeffPlus F)
      = annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j) (respCoeffPlus F) := by
  apply blockMat_ext
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffPlus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inl i) (Sum.inl k) (hmeas (Sum.inl i) (Sum.inl k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).upperLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffPlus F a)) (Sum.inl i) (Sum.inl k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).upperLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffPlus F a)) (Sum.inl i) (Sum.inl k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffPlus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inl i) (Sum.inr k) (hmeas (Sum.inl i) (Sum.inr k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).upperRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffPlus F a)) (Sum.inl i) (Sum.inr k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).upperRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffPlus F a)) (Sum.inl i) (Sum.inr k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffPlus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inr i) (Sum.inl k) (hmeas (Sum.inr i) (Sum.inl k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).lowerLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffPlus F a)) (Sum.inr i) (Sum.inl k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).lowerLeft i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffPlus F a)) (Sum.inr i) (Sum.inl k) ∂P := rfl
    rw [hred, hred']
    exact h
  · ext i k
    have h := integral_cellEntry_adaptedCellAtCenter_eq P hstat jStar m j hj w
      (fun V a => coarseBlockMatrix V (respCoeffPlus F a))
      (fun z a =>
        coarseBlockMatrix_adaptedCellTranslate_respCoeffPlus (explicitRoundedGrid jStar m) j z F a)
      (Sum.inr i) (Sum.inr k) (hmeas (Sum.inr i) (Sum.inr k))
    have hred : (annealedBlockOf P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
        (respCoeffPlus F)).lowerRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w)
              (respCoeffPlus F a)) (Sum.inr i) (Sum.inr k) ∂P := rfl
    have hred' : (annealedBlockOf P (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
        (respCoeffPlus F)).lowerRight i k
          = ∫ a, blockMatEntry (coarseBlockMatrix (HighContrast.adaptedCell (explicitRoundedGrid jStar m) j)
              (respCoeffPlus F a)) (Sum.inr i) (Sum.inr k) ∂P := rfl
    rw [hred, hred']
    exact h

end

end Homogenization.HighContrast.Multiscale
