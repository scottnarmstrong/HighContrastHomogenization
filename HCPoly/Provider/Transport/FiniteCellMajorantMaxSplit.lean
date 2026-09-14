/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.CellMajorantSplit
import HCPoly.Provider.Transport.FiniteMajorantMaxSplit

/-!
# The three shared maxima of a finite cell-majorant family

This module packages the mechanical passage from the centered filling formula
for every target cell to the three pathwise maxima used by the inherited,
fresh, and below-start estimates.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix

noncomputable section

variable {d : ℕ}

/-- Split every member of a finite family of cell majorants at one checkpoint,
then charge one maximum for each of the inherited, fresh, and source pieces. -/
theorem finite_cell_majorant_three_max_moment_le [NeZero d]
    {iota : Type*} [DecidableEq iota]
    {P : Measure (CoeffSpace d)} {Q : ℕ} (hQ : 2 ≤ Q)
    (hQeven : Even Q) (s : Finset iota) (hs : s.Nonempty)
    (wt : iota → ℝ) (hwt : ∀ i ∈ s, 0 ≤ wt i)
    {q : Mat d} (hq : q.PosDef) {jStar b : ℤ} (hjb : jStar ≤ b)
    (lev : iota → ℤ)
    (Z : iota → ℤ → Finset (Fin d → ℤ)) (c : iota → ℤ → ℝ)
    (G : iota → CoeffSpace d → BlockMat d) (KG : iota → BlockMat d)
    (E F : BlockMat d) (src : iota → CoeffSpace d → ℝ)
    (hE : IsSymmetricBlockMat E)
    (hG : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (G i x))
    (hKG : ∀ i ∈ s, IsSymmetricBlockMat (KG i))
    (hcentered : ∀ i ∈ s, ∀ᵐ x ∂P,
      toFullBlockMat (blockSub (G i x) (KG i)) =
        (∑ r ∈ Finset.Icc jStar (lev i), ∑ w ∈ Z i r,
          c i r • toFullBlockMat
            (blockSub (coarseBlock (adaptedCellAt q r w) x)
              (adaptedMean P q r))) +
          src i x • toFullBlockMat E) :
    ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i =>
        wt i * schattenSize (Q : ℝ) (blockSub (G i x) (KG i)) F) ^
          (Q : ℝ) ∂P ≤
      ENNReal.ofReal ((2 * (d : ℝ)) ^ 2) ^ (Q : ℝ) *
        ((2 : ℝ≥0∞) ^ ((Q : ℝ) - 1)) ^ 2 *
          ((∫⁻ x, ENNReal.ofReal (s.sup' hs fun i =>
              wt i * schattenSize (Q : ℝ)
                (ofFullBlockMat
                  (∑ r ∈ Finset.Icc jStar (min b (lev i)), ∑ w ∈ Z i r,
                    c i r • toFullBlockMat
                      (blockSub (coarseBlock (adaptedCellAt q r w) x)
                        (adaptedMean P q r)))) F) ^ (Q : ℝ) ∂P) +
            (∫⁻ x, ENNReal.ofReal (s.sup' hs fun i =>
              wt i * schattenSize (Q : ℝ)
                (ofFullBlockMat
                  (∑ r ∈ Finset.Icc (b + 1) (lev i), ∑ w ∈ Z i r,
                    c i r • toFullBlockMat
                      (blockSub (coarseBlock (adaptedCellAt q r w) x)
                        (adaptedMean P q r)))) F) ^ (Q : ℝ) ∂P) +
            ∫⁻ x, ENNReal.ofReal (s.sup' hs fun i =>
              wt i * schattenSize (Q : ℝ) (blockScale (src i x) E) F) ^
                (Q : ℝ) ∂P) := by
  let A : iota → CoeffSpace d → BlockMat d := fun i x => ofFullBlockMat
    (∑ r ∈ Finset.Icc jStar (min b (lev i)), ∑ w ∈ Z i r,
      c i r • toFullBlockMat
        (blockSub (coarseBlock (adaptedCellAt q r w) x) (adaptedMean P q r)))
  let B : iota → CoeffSpace d → BlockMat d := fun i x => ofFullBlockMat
    (∑ r ∈ Finset.Icc (b + 1) (lev i), ∑ w ∈ Z i r,
      c i r • toFullBlockMat
        (blockSub (coarseBlock (adaptedCellAt q r w) x) (adaptedMean P q r)))
  let C : iota → CoeffSpace d → BlockMat d := fun i x => blockScale (src i x) E
  let GC : iota → CoeffSpace d → BlockMat d := fun i x => blockSub (G i x) (KG i)
  let u : CoeffSpace d → ℝ≥0∞ := fun x => ENNReal.ofReal
    (s.sup' hs fun i => wt i * schattenSize (Q : ℝ) (A i x) F)
  let v : CoeffSpace d → ℝ≥0∞ := fun x => ENNReal.ofReal
    (s.sup' hs fun i => wt i * schattenSize (Q : ℝ) (B i x) F)
  let w : CoeffSpace d → ℝ≥0∞ := fun x => ENNReal.ofReal
    (s.sup' hs fun i => wt i * schattenSize (Q : ℝ) (C i x) F)
  have hAsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (A i x) := by
    intro i hi x
    simp only [A]
    refine isSymmetricBlockMat_of_isSymm ?_
    ext alpha beta
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun z _ =>
      congrArg _ ((isSymm_toFullBlockMat_of_isSymmetricBlockMat
        (Recurrence.isSymmetricBlockMat_coarseBlock_sub x
          (Recurrence.isSymmetricBlockMat_adaptedMean P q r))).apply alpha beta)
  have hBsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (B i x) := by
    intro i hi x
    simp only [B]
    refine isSymmetricBlockMat_of_isSymm ?_
    ext alpha beta
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun z _ =>
      congrArg _ ((isSymm_toFullBlockMat_of_isSymmetricBlockMat
        (Recurrence.isSymmetricBlockMat_coarseBlock_sub x
          (Recurrence.isSymmetricBlockMat_adaptedMean P q r))).apply alpha beta)
  have hCsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (C i x) := by
    intro i hi x
    exact isSymmetricBlockMat_blockScale _ hE
  have hGCsym : ∀ i ∈ s, ∀ x, IsSymmetricBlockMat (GC i x) := by
    intro i hi x
    exact isSymmetricBlockMat_blockSub (hG i hi x) (hKG i hi)
  have hsplit : ∀ i ∈ s, ∀ᵐ x ∂P,
      toFullBlockMat (GC i x) =
        toFullBlockMat (A i x) + toFullBlockMat (B i x) +
          toFullBlockMat (C i x) := by
    intro i hi
    simpa only [A, B, C, GC] using
      (cell_majorant_centered_split (P := P) (q := q) (jStar := jStar)
        (b := b) (j := lev i) hjb (Z := Z i) (c := c i)
        (G := G i) (KG := KG i) (E := E) (src := src i) (hcentered i hi))
  have hu : ∀ i ∈ s, ∀ x,
      ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (A i x) F) ≤ u x := by
    intro i hi x
    simp only [u]
    exact ENNReal.ofReal_le_ofReal
      (Finset.le_sup' (fun k => wt k * schattenSize (Q : ℝ) (A k x) F) hi)
  have hv : ∀ i ∈ s, ∀ x,
      ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (B i x) F) ≤ v x := by
    intro i hi x
    simp only [v]
    exact ENNReal.ofReal_le_ofReal
      (Finset.le_sup' (fun k => wt k * schattenSize (Q : ℝ) (B k x) F) hi)
  have hw' : ∀ i ∈ s, ∀ x,
      ENNReal.ofReal (wt i * schattenSize (Q : ℝ) (C i x) F) ≤ w x := by
    intro i hi x
    simp only [w]
    exact ENNReal.ofReal_le_ofReal
      (Finset.le_sup' (fun k => wt k * schattenSize (Q : ℝ) (C k x) F) hi)
  have hAentry : ∀ i ∈ s, ∀ alpha beta : BlockCoord d,
      AEStronglyMeasurable (fun x => toFullBlockMat (A i x) alpha beta) P := by
    intro i hi alpha beta
    simp only [A, toFullBlockMat_ofFullBlockMat, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine Finset.aestronglyMeasurable_fun_sum _ fun r _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun z _ => ?_
    have hm := Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq r z alpha beta
    have hm' : AEStronglyMeasurable
        (fun x => toFullBlockMat (coarseBlock (adaptedCellAt q r z) x) alpha beta) P := by
      simpa only [toFullBlockMat_eq_blockMatEntry] using hm
    have hsub : AEStronglyMeasurable (fun x => toFullBlockMat
        (blockSub (coarseBlock (adaptedCellAt q r z) x)
          (adaptedMean P q r)) alpha beta) P := by
      simpa only [Recurrence.toFullBlockMat_blockSub_apply] using!
        hm'.sub (aestronglyMeasurable_const
          (b := toFullBlockMat (adaptedMean P q r) alpha beta))
    exact hsub.const_mul (c i r)
  have hBentry : ∀ i ∈ s, ∀ alpha beta : BlockCoord d,
      AEStronglyMeasurable (fun x => toFullBlockMat (B i x) alpha beta) P := by
    intro i hi alpha beta
    simp only [B, toFullBlockMat_ofFullBlockMat, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine Finset.aestronglyMeasurable_fun_sum _ fun r _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun z _ => ?_
    have hm := Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq r z alpha beta
    have hm' : AEStronglyMeasurable
        (fun x => toFullBlockMat (coarseBlock (adaptedCellAt q r z) x) alpha beta) P := by
      simpa only [toFullBlockMat_eq_blockMatEntry] using hm
    have hsub : AEStronglyMeasurable (fun x => toFullBlockMat
        (blockSub (coarseBlock (adaptedCellAt q r z) x)
          (adaptedMean P q r)) alpha beta) P := by
      simpa only [Recurrence.toFullBlockMat_blockSub_apply] using!
        hm'.sub (aestronglyMeasurable_const
          (b := toFullBlockMat (adaptedMean P q r) alpha beta))
    exact hsub.const_mul (c i r)
  have huMeas : AEMeasurable (fun x => u x ^ (Q : ℝ)) P := by
    have hcell : ∀ i ∈ s, AEStronglyMeasurable
        (fun x => wt i * schattenSize (Q : ℝ) (A i x) F) P := by
      intro i hi
      exact (aestronglyMeasurable_schattenSize (F := F) hQeven
        (hAsym i hi) (hAentry i hi)).const_mul (wt i)
    have hsup : AEMeasurable (s.sup' hs fun i x =>
        wt i * schattenSize (Q : ℝ) (A i x) F) P :=
      Finset.sup'_induction hs (fun i x =>
          wt i * schattenSize (Q : ℝ) (A i x) F)
        (fun (_f : CoeffSpace d → ℝ) (hf : AEMeasurable _f P)
            (_g : CoeffSpace d → ℝ) (hg : AEMeasurable _g P) => hf.sup hg)
        (fun i hi => (hcell i hi).aemeasurable)
    have huBase : AEMeasurable u P := by
      simp only [u]
      have hscalar : AEMeasurable (fun x => s.sup' hs fun i =>
          wt i * schattenSize (Q : ℝ) (A i x) F) P := by
        rw [show (fun x => s.sup' hs fun i =>
            wt i * schattenSize (Q : ℝ) (A i x) F) =
          s.sup' hs (fun i x => wt i * schattenSize (Q : ℝ) (A i x) F) by
            funext x
            rw [Finset.sup'_apply]]
        exact hsup
      exact ENNReal.measurable_ofReal.comp_aemeasurable hscalar
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable huBase
  have hvMeas : AEMeasurable (fun x => v x ^ (Q : ℝ)) P := by
    have hcell : ∀ i ∈ s, AEStronglyMeasurable
        (fun x => wt i * schattenSize (Q : ℝ) (B i x) F) P := by
      intro i hi
      exact (aestronglyMeasurable_schattenSize (F := F) hQeven
        (hBsym i hi) (hBentry i hi)).const_mul (wt i)
    have hsup : AEMeasurable (s.sup' hs fun i x =>
        wt i * schattenSize (Q : ℝ) (B i x) F) P :=
      Finset.sup'_induction hs (fun i x =>
          wt i * schattenSize (Q : ℝ) (B i x) F)
        (fun (_f : CoeffSpace d → ℝ) (hf : AEMeasurable _f P)
            (_g : CoeffSpace d → ℝ) (hg : AEMeasurable _g P) => hf.sup hg)
        (fun i hi => (hcell i hi).aemeasurable)
    have hvBase : AEMeasurable v P := by
      simp only [v]
      have hscalar : AEMeasurable (fun x => s.sup' hs fun i =>
          wt i * schattenSize (Q : ℝ) (B i x) F) P := by
        rw [show (fun x => s.sup' hs fun i =>
            wt i * schattenSize (Q : ℝ) (B i x) F) =
          s.sup' hs (fun i x => wt i * schattenSize (Q : ℝ) (B i x) F) by
            funext x
            rw [Finset.sup'_apply]]
        exact hsup
      exact ENNReal.measurable_ofReal.comp_aemeasurable hscalar
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hvBase
  have hmain := finite_majorant_three_max_moment_le s hs hQ wt hwt A B C GC F
    hAsym hBsym hCsym hGCsym hsplit hu hv hw' huMeas hvMeas
  simpa only [A, B, C, GC, u, v, w] using hmain

end

end Transport
end HighContrast
end Homogenization
