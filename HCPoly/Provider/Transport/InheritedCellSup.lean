/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/
import HCPoly.Provider.Transport.InheritedRowEnvelope
import HCPoly.Provider.Transport.CenteredSplit

/-!
# One inherited cell against the global ancestor supremum

The rows of one maximal filling at or below the checkpoint are bounded
pathwise by the single global family of checkpoint-ancestor statistics.  The
uniform row envelope is kept outside that supremum, which is the key to paying
the inherited fluctuation only once.
-/

namespace Homogenization
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The inherited part of one cell majorant is bounded by the global ancestor
supremum with the uniform `3^{rhoMax (b-j)}` envelope. -/
theorem inherited_cell_schatten_le [NeZero d] {Q rhoMax lam C : ℝ}
    (hQ : 0 < Q) {P : Measure (CoeffSpace d)} {q : Mat d}
    {jStar b j : ℤ} (hjj : jStar ≤ j) (hrho : rhoMax < 1)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    (hbpd : Book.Ch02.BlockPosDef (adaptedMean P q b))
    (hlam : 0 ≤ lam)
    (hEbF : toFullBlockMat (adaptedMean P q b) ≤ lam • toFullBlockMat F)
    {Z : ℤ → Finset (Fin d → ℤ)} {c : ℤ → ℝ}
    (hc : ∀ r, 0 ≤ c r)
    (hmass : ∑ r ∈ Finset.Icc jStar j, ∑ _w ∈ Z r, c r ≤ 1)
    (hrow : ∀ r ∈ Finset.Icc jStar j, r < j →
      (∑ _w ∈ Z r, c r) ≤ C * (3 : ℝ) ^ ((r : ℝ) - (j : ℝ)))
    {Zanc : Finset (Fin d → ℤ)}
    {anc : ℤ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hancmem : ∀ r ∈ Finset.Icc jStar (min b j), ∀ w ∈ Z r, anc r w ∈ Zanc)
    (hancsub : ∀ r ∈ Finset.Icc jStar (min b j), ∀ w ∈ Z r,
      adaptedCellAt q r w ⊆ adaptedCellAt q b (anc r w))
    (x : CoeffSpace d) :
    ENNReal.ofReal (schattenSize Q
        (ofFullBlockMat (∑ r ∈ Finset.Icc jStar (min b j), ∑ w ∈ Z r,
          c r • toFullBlockMat (blockSub
            (coarseBlock (adaptedCellAt q r w) x) (adaptedMean P q r)))) F) ≤
      ENNReal.ofReal (((2 * (d : ℝ)) ^ Q⁻¹ * lam *
          (max 1 C * (1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax))))) *
            (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ))))) *
        (⨆ vB ∈ Zanc, ⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b)
            (w : Fin d → ℤ) (_ : adaptedCellAt q r w ⊆ adaptedCellAt q b vB),
          ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
            blockSize (blockSub (adaptedResponse q r w x) (adaptedMean P q r))
              (adaptedMean P q b))) := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hbsym : IsSymmetricBlockMat (adaptedMean P q b) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q b
  have hK0 : 0 ≤ (2 * (d : ℝ)) ^ Q⁻¹ := Real.rpow_nonneg (by positivity) _
  have hcellsym : ∀ r w, IsSymmetricBlockMat
      (blockSub (coarseBlock (adaptedCellAt q r w) x) (adaptedMean P q r)) :=
    fun r w => Recurrence.isSymmetricBlockMat_coarseBlock_sub x
      (Recurrence.isSymmetricBlockMat_adaptedMean P q r)
  let R : Finset ℤ := Finset.Icc jStar (min b j)
  let S : BlockMat d := ofFullBlockMat (∑ r ∈ R, ∑ w ∈ Z r,
    c r • toFullBlockMat (blockSub
      (coarseBlock (adaptedCellAt q r w) x) (adaptedMean P q r)))
  let bs : ℤ → (Fin d → ℤ) → ℝ := fun r w =>
    blockSize (blockSub (coarseBlock (adaptedCellAt q r w) x)
      (adaptedMean P q r)) (adaptedMean P q b)
  let X : ℝ≥0∞ := ⨆ vB ∈ Zanc, ⨆ (r : ℤ) (_ : jStar ≤ r) (_ : r ≤ b)
      (w : Fin d → ℤ) (_ : adaptedCellAt q r w ⊆ adaptedCellAt q b vB),
    ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) *
      blockSize (blockSub (adaptedResponse q r w x) (adaptedMean P q r))
        (adaptedMean P q b))
  have hSsym : IsSymmetricBlockMat S := by
    simp only [S]
    refine isSymmetricBlockMat_of_isSymm ?_
    ext γ δ
    simp only [Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun w _ =>
      congrArg _ ((isSymm_toFullBlockMat_of_isSymmetricBlockMat
        (hcellsym r w)).apply γ δ)
  have hbs0 : ∀ r w, 0 ≤ bs r w := fun r w =>
    PortableHistory.blockSize_nonneg (hcellsym r w) hbsym hbpd
  have hblock : blockSize S (adaptedMean P q b) ≤
      ∑ r ∈ R, ∑ w ∈ Z r, c r * bs r w := by
    simp only [S, bs]
    exact blockSize_filling_sum_le hbsym hbpd
      (fun r _ => hc r) (fun r w => hcellsym r w)
  have hreal : schattenSize Q S F ≤
      (2 * (d : ℝ)) ^ Q⁻¹ * lam * ∑ r ∈ R, ∑ w ∈ Z r, c r * bs r w := by
    have h1 := PortableHistory.schattenSize_le_blockSize hSsym hFsym hFpd hQ
    have h2 := PortableHistory.blockSize_le_mul_blockSize hSsym hbsym hbpd hFsym hFpd hlam hEbF
    have h3' : blockSize S F ≤ lam * ∑ r ∈ R, ∑ w ∈ Z r, c r * bs r w :=
      h2.trans (mul_le_mul_of_nonneg_left hblock hlam)
    have h4 := mul_le_mul_of_nonneg_left h3' hK0
    linarith only [h1, h4]
  have hcellX : ∀ r ∈ R, ∀ w ∈ Z r,
      ENNReal.ofReal (c r * bs r w) ≤
        ENNReal.ofReal (c r * (3 : ℝ) ^
          (rhoMax * ((b : ℝ) - (r : ℝ)))) * X := by
    intro r hr w hw
    have hwt : 0 ≤ (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) :=
      Real.rpow_nonneg h3.le _
    have hsplit : ENNReal.ofReal (c r * bs r w) =
        ENNReal.ofReal (c r * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ)))) *
          ENNReal.ofReal ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) * bs r w) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (hc r) hwt)]
      congr 1
      rw [show c r * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) *
            ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) * bs r w) =
          c r * ((3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) *
            (3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ)))) * bs r w by ring]
      rw [← Real.rpow_add h3]
      ring_nf
      rw [Real.rpow_zero, mul_one]
    have hsup : ENNReal.ofReal
        ((3 : ℝ) ^ (-rhoMax * ((b : ℝ) - (r : ℝ))) * bs r w) ≤ X := by
      have hrmem : r ∈ Finset.Icc jStar (min b j) := hr
      have hrlo : jStar ≤ r := (Finset.mem_Icc.mp hrmem).1
      have hrhi : r ≤ b := (Finset.mem_Icc.mp hrmem).2.trans (min_le_left _ _)
      exact le_iSup_of_le (anc r w) (le_iSup_of_le (hancmem r hr w hw)
        (le_iSup_of_le r (le_iSup_of_le hrlo (le_iSup_of_le hrhi
          (le_iSup_of_le w (le_iSup_of_le (hancsub r hr w hw) le_rfl))))))
    rw [hsplit]
    exact mul_le_mul' le_rfl hsup
  have hsumX : ENNReal.ofReal (∑ r ∈ R, ∑ w ∈ Z r, c r * bs r w) ≤
      ENNReal.ofReal (∑ r ∈ R, ∑ _w ∈ Z r,
        c r * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ)))) * X := by
    rw [ENNReal.ofReal_sum_of_nonneg fun r _ =>
      Finset.sum_nonneg fun w _ => mul_nonneg (hc r) (hbs0 r w)]
    have hrowX : ∀ r ∈ R,
        ENNReal.ofReal (∑ w ∈ Z r, c r * bs r w) ≤
          ENNReal.ofReal (∑ _w ∈ Z r,
            c r * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ)))) * X := by
      intro r hr
      rw [ENNReal.ofReal_sum_of_nonneg fun w _ => mul_nonneg (hc r) (hbs0 r w),
        ENNReal.ofReal_sum_of_nonneg fun _ _ =>
          mul_nonneg (hc r) (Real.rpow_nonneg h3.le _), Finset.sum_mul]
      exact Finset.sum_le_sum fun w hw => hcellX r hr w hw
    refine (Finset.sum_le_sum hrowX).trans_eq ?_
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun r _ =>
      Finset.sum_nonneg fun _ _ => mul_nonneg (hc r) (Real.rpow_nonneg h3.le _)]
  have hW : ∑ r ∈ R, ∑ _w ∈ Z r,
        c r * (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (r : ℝ))) ≤
      max 1 C * (1 / (1 - (3 : ℝ) ^ (-(1 - rhoMax)))) *
        (3 : ℝ) ^ (rhoMax * ((b : ℝ) - (j : ℝ))) := by
    have hW' := inherited_row_mass_envelope (b := b) hrho hjj
      (m := fun r => ∑ _w ∈ Z r, c r)
      (fun r => Finset.sum_nonneg fun _ _ => hc r) hmass hrow
    simpa only [R, Finset.sum_mul] using hW'
  have hcoef0 : 0 ≤ (2 * (d : ℝ)) ^ Q⁻¹ * lam := mul_nonneg hK0 hlam
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  rw [ENNReal.ofReal_mul hcoef0]
  refine (mul_le_mul' le_rfl hsumX).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hcoef0]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hW hcoef0)) le_rfl

end

end Transport
end HighContrast
end Homogenization
