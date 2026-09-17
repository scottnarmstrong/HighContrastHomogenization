import HCPoly.Entry.Annealed.AdaptedIntegrability
import HCPoly.Entry.Annealed.AlignedSubdivision
import HCPoly.Entry.Source.CoarseSubadditivity

/-!
# Decreasing actual adapted means

`p.fixed.geometry.parent.child.recurrence`: finite aligned subadditivity, integer stationarity, and genuine
finite entrywise expectations. No averaging, positive-gap, or recurrence
is used in this direction. Equality of generations is included.
-/

open Homogenization.HighContrast.CG

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  adaptedMean annealedBlock blockMatEntry_annealedBlock coarseBlock
  toFullBlockMat_eq_blockMatEntry)
open Homogenization.HighContrast (adaptedCell adaptedCellTranslate centeredCube
  standardCellCenter)
namespace Homogenization.HighContrast.Annealed

open MeasureTheory Geometry Set

noncomputable section

/-- A finite adapted partition satisfies the actual full block inequality. -/
theorem coarseBlock_adapted_finite_partition {d : ℕ} [NeZero d]
    {ι : Type*} {s : Set ι} (hs : s.Finite)
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (y : Vec d)
    (qi : ι → Mat d) (hqi : ∀ i ∈ s, IsUnit (qi i)) (ji : ι → ℤ) (yi : ι → Vec d)
    (a : CoeffSpace d) :
    let W := adaptedCellTranslate q j y
    let U := fun i => adaptedCellTranslate (qi i) (ji i) (yi i)
    (∀ i ∈ s, U i ⊆ W) → s.PairwiseDisjoint U →
      volume (W \ ⋃ i ∈ s, U i) = 0 →
      BlockMatLoewnerLE (coarseBlock W a) (ofFullBlockMat (∑' i : s,
        ((volume (U i)).toReal / (volume W).toReal) • toFullBlockMat (coarseBlock (U i) a))) := by
  intro W U hsub hdisj hnull
  let := hs.fintype
  have hWfin : volume W ≠ ⊤ := volume_adaptedCellTranslate_ne_top q j y
  let : IsFiniteMeasure (volumeMeasureOn W) := ⟨by simpa [volumeMeasureOn] using hWfin.lt_top⟩
  have hWpos : 0 < volume W := by
    dsimp [W]
    rw [volume_adaptedCellTranslate]
    have hdet : q.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det q).mp hq).ne_zero
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr hdet)).ne'
      (ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity)) d).ne'
  have hWvol : (volume W).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hWpos.ne', hWfin⟩
  obtain ⟨lam, Lam, f, _hlam, _hle, hEll, hae⟩ :=
    exists_elliptic_representative_adapted q hq j y a
  apply Source.block_tsum_of_response_partition hs.countable (isOpen_adaptedCellTranslate hq j y)
    hWvol (fun i hi => isOpen_adaptedCellTranslate (hqi i hi) (ji i) (yi i))
    hsub hdisj hnull hEll (coarseBlock W a) (fun i => coarseBlock (U i) a) _ _ (hasSum_fintype _).summable
  · intro p r
    rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae)]
    exact responseJ_eq_coarseBlock_adapted q hq j y a p r
  · intro i hi p r
    rw [← responseJ_congr_of_ae_eq (ae_restrict_of_ae hae)]
    exact responseJ_eq_coarseBlock_adapted (qi i) (hqi i hi) (ji i) (yi i) a p r

/-- Pathwise aligned parent order with the literal finite equal-weight average. -/
theorem coarseBlock_aligned_parent_le {d : ℕ} [NeZero d]
    (q : Mat d) (hq : IsUnit q) (j : ℤ) (h : ℕ) (a : CoeffSpace d) :
    let s := {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)}
    let := (alignedCenterSet_finite_card d j h).1.fintype
    BlockMatLoewnerLE (coarseBlock (adaptedCell q (j + h)) a)
      (ofFullBlockMat (∑ w : s, ((3 : ℝ) ^ (d * h))⁻¹ •
        toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a))) := by
  intro s
  let := (alignedCenterSet_finite_card d j h).1.fintype
  have hW : adaptedCellTranslate q (j + h) 0 = adaptedCell q (j + h) := by
    simp [adaptedCellTranslate]
  obtain ⟨hsub, hdisj, hnull⟩ := aligned_adapted_partition q hq j h
  have hp := coarseBlock_adapted_finite_partition (alignedCenterSet_finite_card d j h).1
    q hq (j + h) 0 (fun _ => q) (fun _ _ => hq) (fun _ => j)
    (fun w => adaptedCellCenter q j w) a
  dsimp only at hp
  rw [hW] at hp
  have hp' := hp hsub hdisj hnull
  change BlockMatLoewnerLE _ (ofFullBlockMat (∑' w : s,
    ((volume (adaptedCellAtCenter q j w)).toReal / (volume (adaptedCell q (j + h))).toReal) •
      toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a))) at hp'
  simpa only [tsum_fintype, aligned_adapted_volume_ratio q hq j h] using hp'

/-- Integer stationarity identifies each aligned child's actual annealed matrix. -/
theorem annealedBlock_adaptedCellAtCenter {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hj : (jStar : ℤ) ≤ j) (w : Fin d → ℤ) :
    annealedBlock P (adaptedCellAtCenter (explicitRoundedGrid jStar m) j w) =
      adaptedMean P (explicitRoundedGrid jStar m) j := by
  obtain ⟨z, hz⟩ := adaptedCellCenter_eq_intTranslation jStar m hj w
  have he := Source.annealedBlock_adapted_add_intTranslation P hstat
    (explicitRoundedGrid jStar m) (isUnit_roundedGrid hjStar hm) j 0 z
  simpa [adaptedCellAtCenter, hz, adaptedCellTranslate, adaptedMean, HighContrast.adaptedCell, HighContrast.centeredCube] using he

/-- Actual adapted annealed blocks decrease across every admissible pair, including j=k. -/
theorem adaptedMean_antitone (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef) (j k : ℤ)
    (hj : (jStar : ℤ) ≤ j) (hjk : j ≤ k) :
    BlockMatLoewnerLE (adaptedMean P (explicitRoundedGrid jStar m) k)
      (adaptedMean P (explicitRoundedGrid jStar m) j) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨h, rfl⟩ : ∃ h : ℕ, k = j + h :=
    ⟨(k - j).toNat, by rw [Int.toNat_of_nonneg (by omega)]; omega⟩
  let q := explicitRoundedGrid jStar m
  let s := {w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + h)}
  let := (alignedCenterSet_finite_card d j h).1.fintype
  let ρ : ℝ := ((3 : ℝ) ^ (d * h))⁻¹
  let B : CoeffSpace d → BlockMat d := fun a =>
    ofFullBlockMat (∑ w : s, ρ • toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a))
  have hc (w : s) : MemLqSchatten P 1 (fun a => coarseBlock (adaptedCellAtCenter q j w) a) :=
    Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
      jStar hjStar m hm j (adaptedCellCenter q j w) 1 le_rfl
  have hB : MemLqSchatten P 1 B := Source.memLqSchatten_finset_sum le_rfl
    Finset.univ (fun _ : s => ρ) (fun w a => coarseBlock (adaptedCellAtCenter q j w) a)
    (fun w _ => hc w)
  have hF : HasIntegrableCoarseBlock P (adaptedCell q (j + h)) := by
    simpa [adaptedCellTranslate] using hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S
      hstat hdag jStar hjStar m hm (j + h) 0
  have hentry (α β : BlockCoord d) : (∫ a, blockMatEntry (B a) α β ∂P) =
      blockMatEntry (adaptedMean P q j) α β := by
    have hw (w : s) : (∫ a, blockMatEntry (coarseBlock (adaptedCellAtCenter q j w) a) α β ∂P) =
        blockMatEntry (adaptedMean P q j) α β := by
      rw [← blockMatEntry_annealedBlock,
        annealedBlock_adaptedCellAtCenter P hstat jStar hjStar m hm j hj w]
    simp only [B, blockMatEntry_ofFullBlockMat, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, toFullBlockMat_eq_blockMatEntry]
    rw [integral_finsetSum _ (fun w _ => ((hc w).integrable_entry le_rfl α β).const_mul ρ)]
    simp only [integral_const_mul, hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : Fintype.card s = 3 ^ (d * h) := by
      rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      exact (alignedCenterSet_finite_card d j h).2
    rw [hcard]
    dsimp [ρ]
    push_cast
    field_simp
  have ho := Analysis.blockMatLoewnerLE_integral hF (hB.integrable_entry le_rfl)
    (ae_of_all P fun a => coarseBlock_aligned_parent_le q (isUnit_roundedGrid hjStar hm) j h a)
  have hleft : ofFullBlockMat (Matrix.of fun α β =>
      ∫ a, blockMatEntry (coarseBlock (adaptedCell q (j + h)) a) α β ∂P) =
      adaptedMean P q (j + h) := by
    rw [← ofFullBlockMat_toFullBlockMat (adaptedMean P q (j + h))]
    congr 1
    funext α β
    exact (blockMatEntry_annealedBlock P _ α β).symm
  have hright : ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (B a) α β ∂P) =
      adaptedMean P q j := by
    rw [← ofFullBlockMat_toFullBlockMat (adaptedMean P q j)]
    congr 1
    funext α β
    exact hentry α β
  rwa [hleft, hright] at ho

end

end Homogenization.HighContrast.Annealed
