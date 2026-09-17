import HCPoly.Entry.Annealed.ParentChildBlocks
import HCPoly.Entry.Annealed.RecurrenceTransport
import HCPoly.Entry.Analysis.SchattenCongruence
import HCPoly.Entry.MatrixAveraging
import HCPoly.Entry.PositiveGap

/-!
# The parent–child recurrence

Near `p.fixed.geometry.parent.child.recurrence`. The aligned children supply the actual average,
its expectation and order. Matrix averaging at the child normalization,
sharp normalization transport, and the positive-gap estimate give
the recurrence with the two printed coefficients. The ordered-mean
analysis supplies the full trace/determinant estimate and nonnegative loss.

All moment membership and both mean positive-definiteness proofs are derived
from the standing law. The helper with an averaging premise is discharged
by the ordinary endpoint here and by the exact averaging result.
The latter returns the very same source constant and passes
its threshold premise straight through.

-/

open Homogenization.HighContrast (CoeffSpace adaptedMean blockPosDef_annealedBlock blockSub
  blockTrace coarseBlock isSymmetricBlockMat_coarseBlockMatrix matSqrt normalizedBlock)
open Homogenization.HighContrast (adaptedCell adaptedCellTranslate)
namespace Homogenization.HighContrast.Annealed
open MeasureTheory Geometry Analysis
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
noncomputable section

variable {d : ℕ}

/-- Full coordinates preserve block subtraction. -/
theorem fullBlock_blockSub (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

/-- Deterministic normalization is linear in the matrix being normalized. -/
theorem normalizedBlock_blockSub (A B R : BlockMat d) :
    normalizedBlock (blockSub A B) R =
      blockSub (normalizedBlock A R) (normalizedBlock B R) := by
  unfold normalizedBlock
  rw [fullBlock_blockSub, mul_sub, sub_mul]
  rfl

/-- Centering commutes with a nonempty equal-weight full-matrix average. -/
theorem fullBlock_average_sub {ι : Type*} (Z : Finset ι) (hZ : Z.Nonempty)
    (A : ι → FullBlockMat d) (C : FullBlockMat d) :
    (Z.card : ℝ)⁻¹ • ∑ z ∈ Z, (A z - C) =
      (Z.card : ℝ)⁻¹ • ∑ z ∈ Z, A z - C := by
  have hcard : (Z.card : ℝ) ≠ 0 := by exact_mod_cast hZ.card_pos.ne'
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_sub, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Pull normalization and centering through the actual finite average. -/
theorem normalizedBlock_average_sub {ι : Type*} (Z : Finset ι) (hZ : Z.Nonempty)
    (A : ι → BlockMat d) (C R : BlockMat d) :
    ofFullBlockMat ((Z.card : ℝ)⁻¹ •
      ∑ z ∈ Z, toFullBlockMat (normalizedBlock (blockSub (A z) C) R)) =
    normalizedBlock (blockSub
      (ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ z ∈ Z, toFullBlockMat (A z))) C) R := by
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat, fullBlock_blockSub]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  simp_rw [Matrix.mul_sub, Matrix.sub_mul]
  exact fullBlock_average_sub Z hZ _ _

/-- Actual expectation commutes with normalization when every entry is integrable. -/
theorem integral_normalizedBlock {P : Measure (CoeffSpace d)}
    {X : CoeffSpace d → BlockMat d}
    (hX : ∀ α β, Integrable (fun a => blockMatEntry (X a) α β) P) (R : BlockMat d) :
    ofFullBlockMat (fun α β => ∫ a,
      blockMatEntry (normalizedBlock (X a) R) α β ∂P) =
    normalizedBlock (ofFullBlockMat (fun α β => ∫ a, blockMatEntry (X a) α β ∂P)) R := by
  simp only [normalizedBlock, blockMatEntry_ofFullBlockMat]
  rw [integral_fullBlock_mul hX,
    toFullBlockMat_ofFullBlockMat (fun α β => ∫ a, blockMatEntry (X a) α β ∂P)]
  rfl

/-- The parent-normalized mean trace gap is bounded by the printed exponential term. -/
theorem recurrence_gap_term_le (d : ℕ) {N Δ : ℝ} (hN : 2 ≤ N) (hΔ : 0 ≤ Δ)
    (M : BlockMat d) (hM : IsSymmetricBlockMat M)
    (hIM : BlockMatLoewnerLE (Book.Ch02.blockIdentity d) M)
    (hnorm : blockOpNorm M ≤ Real.exp Δ)
    (htrace : blockTrace (blockSub M (Book.Ch02.blockIdentity d)) ≤ Real.exp Δ - 1) :
    2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) * blockOpNorm M ^ (1 - N⁻¹) *
      blockTrace (blockSub M (Book.Ch02.blockIdentity d)) ^ N⁻¹ ≤
    2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) * Real.exp ((1 - N⁻¹) * Δ) *
      (Real.exp Δ - 1) ^ N⁻¹ := by
  have hN1 : (1 : ℝ) ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans hN
  have hNi : 0 ≤ N⁻¹ := inv_nonneg.mpr (zero_le_one.trans hN1)
  have hNi1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have htrace0 := blockTrace_identity_sub_nonneg M hM hIM
  have hgain : 0 ≤ Real.exp Δ - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hΔ)
  have hc : 0 ≤ 2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) :=
    mul_nonneg (by norm_num) (add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hop : blockOpNorm M ^ (1 - N⁻¹) ≤ Real.exp ((1 - N⁻¹) * Δ) := by
    calc
      _ ≤ (Real.exp Δ) ^ (1 - N⁻¹) :=
        Real.rpow_le_rpow (norm_nonneg _) hnorm (sub_nonneg.mpr hNi1)
      _ = _ := by rw [← Real.exp_mul, mul_comm Δ]
  calc
    _ ≤ 2 * (1 + (d : ℝ) ^ (1 - N⁻¹)) * blockOpNorm M ^ (1 - N⁻¹) *
        (Real.exp Δ - 1) ^ N⁻¹ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow htrace0 htrace hNi)
        (mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _))
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hop hc)
      (Real.rpow_nonneg hgain _)

/-- The aligned cardinality produces exactly the printed real-power decay. -/
theorem alignedChildren_card_decay {d : ℕ} (q : Mat d) (hq : IsUnit q) (j h : ℤ)
    (hh : 0 ≤ h) :
    ((alignedChildren q j h.toNat).card : ℝ) ^ ((1 : ℝ) / 2) =
      ((3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)))⁻¹ := by
  rw [alignedChildren_card q hq, Nat.cast_pow, Nat.cast_ofNat,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  rw [Nat.cast_mul]
  have hcast : (h.toNat : ℝ) = (h : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hh : (h.toNat : ℤ) = h)
  rw [hcast]
  ring

/-- Normalization preserves the block order, with a genuine positive normalizer. -/
theorem normalizedBlock_loewnerLE {A B R : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B)
    (hR : (toFullBlockMat R).PosDef) (hAB : BlockMatLoewnerLE A B) :
    BlockMatLoewnerLE (normalizedBlock A R) (normalizedBlock B R) := by
  have hs : (matSqrt (toFullBlockMat R)⁻¹).IsHermitian :=
    (Multiscale.matSqrt_inv_posDef_full hR).isHermitian
  have hst : (matSqrt (toFullBlockMat R)⁻¹)ᵀ = matSqrt (toFullBlockMat R)⁻¹ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hs.eq]
  have ht := blockMatLoewnerLE_congr_le hA hB hAB (matSqrt (toFullBlockMat R)⁻¹)
  rw [hst] at ht
  exact ht

/-- Normalization preserves positive semidefiniteness in the block order. -/
theorem normalizedBlock_nonneg {A R : BlockMat d}
    (hA : (toFullBlockMat A).PosSemidef) (hR : (toFullBlockMat R).PosDef) :
    BlockMatLoewnerLE (ofFullBlockMat 0) (normalizedBlock A R) := by
  have hs : (matSqrt (toFullBlockMat R)⁻¹).IsHermitian :=
    (Multiscale.matSqrt_inv_posDef_full hR).isHermitian
  have hp := hA.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat R)⁻¹)
  rw [hs.eq] at hp
  exact blockMatLoewnerLE_of_le hp.nonneg

/-- Assemble the recurrence from the actual averaging inequality on the aligned children.
The averaging input is discharged by the ordinary endpoint below and by the exact
averaging result. -/
theorem parent_child_recurrence_of_averaging (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) (hP : IsProbabilityMeasure P)
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (N : ℕ) (hN : 2 ≤ N)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j h : ℤ) (hjgen : (jStar : ℤ) ≤ j) (hh : 1 ≤ h)
    (havg : let q := explicitRoundedGrid jStar m
      let Z := alignedChildren q j h.toNat
      ∀ (R : BlockMat d), IsSymmetricBlockMat R → Book.Ch02.BlockPosDef R →
        lqSchattenNorm P (N : ℝ) (fun a => ofFullBlockMat ((Z.card : ℝ)⁻¹ •
          ∑ z ∈ Z, toFullBlockMat (normalizedBlock
            (blockSub (coarseBlock (adaptedCellTranslate q j z) a) (adaptedMean P q j)) R))) ≤
          (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) / (Z.card : ℝ) ^ ((1 : ℝ) / 2) *
            lqSchattenNorm P (N : ℝ) (fun a => normalizedBlock
              (blockSub (coarseBlock (adaptedCell q j) a) (adaptedMean P q j)) R)) :
    lqSchattenNorm P (N : ℝ)
        (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) (j + h)) ≤
      (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) * (1 + (2 * (d : ℝ)) ^ ((N : ℝ))⁻¹) *
            (3 : ℝ) ^ (-((d : ℝ) / 2) * (h : ℝ)) *
            Real.exp (logDetLoss P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
          lqSchattenNorm P (N : ℝ)
            (normalizedFluctuationSelf P (Geometry.explicitRoundedGrid jStar m) j) +
        2 * (1 + (d : ℝ) ^ (1 - ((N : ℝ))⁻¹)) *
            Real.exp
              ((1 - ((N : ℝ))⁻¹) *
                logDetLoss P (Geometry.explicitRoundedGrid jStar m) j (j + h)) *
            (Real.exp (logDetLoss P (Geometry.explicitRoundedGrid jStar m) j (j + h)) - 1) ^
              ((N : ℝ))⁻¹ := by
  let : IsProbabilityMeasure P := hP
  let : NeZero d := ⟨by omega⟩
  let q := explicitRoundedGrid jStar m
  let Z := alignedChildren q j h.toNat
  let Aj := adaptedMean P q j
  let Ak := adaptedMean P q (j + h)
  let G : CoeffSpace d → BlockMat d := fun a => ofFullBlockMat
    ((Z.card : ℝ)⁻¹ • ∑ z ∈ Z, toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a))
  let Fnorm : CoeffSpace d → BlockMat d := fun a =>
    normalizedBlock (coarseBlock (adaptedCell q (j + h)) a) Ak
  let Gnorm : CoeffSpace d → BlockMat d := fun a => normalizedBlock (G a) Ak
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := (by norm_num : (1 : ℝ) ≤ 2).trans hNR
  have hhn : (h.toNat : ℤ) = h := Int.toNat_of_nonneg (by omega)
  have hq : IsUnit q := isUnit_roundedGrid hj hm
  have hZne : Z.Nonempty := alignedChildren_nonempty q j h.toNat
  have hAj := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm j
  have hAk := adaptedMean_posDef d hd P γ E Ψ K S hstat hdag jStar hj m hm (j + h)
  obtain ⟨hIM, hΔ, _, hop, htrace, _⟩ := adaptedMean_order_consequences
    d hd P γ E Ψ K S hstat hdag jStar hj m hm j (j + h) hjgen (by omega)
  have hG : MemLqSchatten P (N : ℝ) G :=
    memLqSchatten_alignedChildren_average hd P γ E Ψ K S hstat hdag
      jStar hj m hm j h.toNat N hN1
  have hAconst : MemLqSchatten P (N : ℝ) (fun _ => Aj) :=
    memLqSchatten_const P hN1 Aj (isSymmetricBlockMat_annealedBlock P _)
  have hX := Source.memLqSchatten_normalizedBlock (hG.sub hAconst hN1) hN1 Aj
  have hFraw : MemLqSchatten P (N : ℝ)
      (fun a => coarseBlock (adaptedCell q (j + h)) a) := by
    simpa only [adaptedCellTranslate_zero] using
      Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
        jStar hj m hm (j + h) 0 N hN1
  have hFmem : MemLqSchatten P (N : ℝ) Fnorm :=
    Source.memLqSchatten_normalizedBlock hFraw hN1 Ak
  have hGmem : MemLqSchatten P (N : ℝ) Gnorm :=
    Source.memLqSchatten_normalizedBlock hG hN1 Ak
  have hAjblock : Book.Ch02.BlockPosDef Aj := by
    have hb := blockPosDef_annealedBlock
      (hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S hstat hdag jStar hj m hm j 0)
      (fun a => blockPosDef_coarseBlock_adapted q hq j 0 a)
    simpa only [adaptedCellTranslate_zero] using! hb
  have hV (r : ℤ) : (fun a => normalizedBlock
      (blockSub (coarseBlock (adaptedCell q r) a) (adaptedMean P q r))
      (adaptedMean P q r)) = normalizedFluctuationSelf P q r := by
    funext a
    simp only [normalizedFluctuationSelf, normalizedFluctuation, adaptedCellTranslate_zero]
  have havg' := havg Aj (isSymmetricBlockMat_annealedBlock P _) hAjblock
  change lqSchattenNorm P (N : ℝ) (fun a => ofFullBlockMat ((Z.card : ℝ)⁻¹ •
      ∑ z ∈ Z, toFullBlockMat (normalizedBlock
        (blockSub (coarseBlock (adaptedCellTranslate q j z) a) Aj) Aj))) ≤ _ at havg'
  simp_rw [normalizedBlock_average_sub Z hZne] at havg'
  rw [hV j] at havg'
  rw [alignedChildren_card_decay q hq j h (by omega)] at havg'
  simp only [div_eq_mul_inv, inv_inv] at havg'
  have htransport := lqSchattenNorm_normalizedBlock_transport_le d hd P γ E Ψ K S
    hstat hdag jStar hj m hm j h.toNat hjgen hN1 (fun a => blockSub (G a) Aj) hX
  rw [hhn] at htransport
  have hGbound := htransport.trans (mul_le_mul_of_nonneg_left havg'
    (Real.exp_pos (logDetLoss P q j (j + h))).le)
  have hEF : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (Fnorm a) α β ∂P) = Book.Ch02.blockIdentity d :=
    integral_normalizedBlock_self d hd P γ E Ψ K S hstat hdag jStar hj m hm (j + h)
  have hEG : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (Gnorm a) α β ∂P) = normalizedMean P q j (j + h) := by
    change ofFullBlockMat (fun α β => ∫ a, blockMatEntry (normalizedBlock (G a) Ak) α β ∂P) = _
    rw [integral_normalizedBlock (hG.integrable_entry hN1)]
    have hmean := integral_alignedChildren_average d hd P γ E Ψ K S hstat hdag
      jStar hj m hm j h.toNat hjgen
    change ofFullBlockMat (fun α β => ∫ a, blockMatEntry (G a) α β ∂P) = Aj at hmean
    rw [hmean]
    rfl
  have hFcenter : (fun a => blockSub (Fnorm a) (Book.Ch02.blockIdentity d)) =
      normalizedFluctuationSelf P q (j + h) := by
    rw [← normalizedMean_self d hd P γ E Ψ K S hstat hdag jStar hj m hm (j + h)]
    change (fun a => blockSub (normalizedBlock _ Ak) (normalizedBlock Ak Ak)) = _
    simp_rw [← normalizedBlock_blockSub]
    exact hV (j + h)
  have hGcenter : (fun a => blockSub (Gnorm a) (normalizedMean P q j (j + h))) =
      (fun a => normalizedBlock (blockSub (G a) Aj) Ak) := by
    funext a
    exact (normalizedBlock_blockSub (G a) Aj Ak).symm
  have hFG : ∀ᵐ a ∂P, BlockMatLoewnerLE (Fnorm a) (Gnorm a) := by
    filter_upwards [hG.symmetric] with a hGa
    have hc := coarseBlock_aligned_children_le q hq j h.toNat a
    rw [hhn] at hc
    exact normalizedBlock_loewnerLE
      (isSymmetricBlockMat_coarseBlockMatrix _ (⇑a.1)) hGa hAk hc
  have hFpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (Fnorm a) :=
    ae_of_all P fun a => normalizedBlock_nonneg
      (coarseBlock_adaptedCell_posSemidef q hq (j + h) a) hAk
  have hGpos : ∀ᵐ a ∂P, BlockMatLoewnerLE (ofFullBlockMat 0) (Gnorm a) := by
    filter_upwards [hFpos, hFG] with a hFa hFGa
    intro x
    exact (hFa x).trans (hFGa x)
  have hgap := Provider.fixed_geometry_positive_gap d hd N hNR P hP
    Fnorm Gnorm hFmem hGmem hFpos hGpos hFG
  rw [hEF, hEG, hFcenter, hGcenter] at hgap
  have hM : IsSymmetricBlockMat (normalizedMean P q j (j + h)) :=
    (toFullBlockMat_isHermitian_iff _).1 (normalizedBlock_posDef Aj Ak hAj hAk).isHermitian
  have hgain := recurrence_gap_term_le d hNR hΔ _ hM hIM hop htrace
  have hcoef : 0 ≤ 1 + (2 * (d : ℝ)) ^ ((N : ℝ))⁻¹ :=
    add_nonneg zero_le_one (Real.rpow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) _)
  refine hgap.trans ((add_le_add (mul_le_mul_of_nonneg_left hGbound hcoef) hgain).trans_eq ?_)
  dsimp only [q]
  simp only [div_eq_mul_inv]
  ac_rfl

end
end Homogenization.HighContrast.Annealed
