import HCPoly.Entry.Annealed.AdaptedIntegrability
import HCPoly.Entry.Annealed.AveragingTransport
import HCPoly.Entry.Annealed.MeanOrder
import HCPoly.Entry.Source.BoundedWindowFiniteness

/-!
# The aligned children of a parent adapted cell

The paper partitions the parent adapted cell `⋄_{j+h}^q` into
`3^{dh}` aligned children `z + ⋄_j^q`, `z` ranging over the physical centres
`3^j q w ∈ 3^j q ℤ^d` whose standard-cell counterpart lies in the parent's centred cube.
`HCPoly.Entry.Annealed.AlignedSubdivision`/`MeanOrder` build this over the *index* `w : Fin d → ℤ`
(via `alignedCenterSet_finite_card`, `coarseBlock_aligned_parent_le`); this file re-indexes it
over the physical *centre* `z : Vec d` as a `Finset (Vec d)`, in the literal shape the averaging
statement's left-hand side takes after `normalizedBlock` is pulled through the finite sum.
-/

open Homogenization.HighContrast (CoeffSpace adaptedCellCenter adaptedMean annealedBlock
  blockMatEntry_annealedBlock coarseBlock isSymmetricBlockMat_coarseBlockMatrix
  toFullBlockMat_eq_blockMatEntry)
open Homogenization.HighContrast (adaptedCell adaptedCellTranslate centeredCube
  standardCellCenter)
namespace Homogenization.HighContrast.Annealed

open MeasureTheory Geometry Set

noncomputable section

variable {d : ℕ}

/-- The `Finset` of physical centres of the scale-`j` children inside `⋄_{j+hn}^q`:
the image, under the aligned centre map `adaptedCellCenter q j`, of the (finite) index set of
`HCPoly.Entry.Annealed.AlignedSubdivision.alignedCenterSet_finite_card`. -/
def alignedChildren (q : Mat d) (j : ℤ) (hn : ℕ) : Finset (Vec d) :=
  (alignedCenterSet_finite_card d j hn).1.toFinset.image (adaptedCellCenter q j)

/-- The aligned children set has the printed cardinality `3^{dh}`. -/
theorem alignedChildren_card (q : Mat d) (hq : IsUnit q) (j : ℤ) (hn : ℕ) :
    (alignedChildren q j hn).card = 3 ^ (d * hn) := by
  unfold alignedChildren
  rw [Finset.card_image_of_injective _ (adaptedCellCenter_injective q j hq)]
  let := (alignedCenterSet_finite_card d j hn).1.fintype
  rw [Set.Finite.card_toFinset, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact (alignedCenterSet_finite_card d j hn).2

/-- The aligned children set is nonempty: the index `w = 0` is always aligned. -/
theorem alignedChildren_nonempty (q : Mat d) (j : ℤ) (hn : ℕ) :
    (alignedChildren q j hn).Nonempty := by
  refine ⟨adaptedCellCenter q j 0, Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
  rw [Set.Finite.mem_toFinset]
  show standardCellCenter j (0 : Fin d → ℤ) ∈ centeredCube d (j + (hn : ℤ))
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (j + (hn : ℤ)) := by positivity
  rw [mem_centeredCube_iff]
  intro i
  have hz : standardCellCenter j (0 : Fin d → ℤ) i = 0 := by simp [standardCellCenter]
  rw [hz]
  constructor <;> nlinarith

/-- Every aligned child's centre lies in the aligned lattice `3^j q ℤ^d`. -/
theorem alignedChildren_subset_lattice (q : Mat d) (j : ℤ) (hn : ℕ) :
    (alignedChildren q j hn : Set (Vec d)) ⊆ adaptedLatticeAtScale q j := by
  intro z hz
  simp only [alignedChildren, Finset.coe_image] at hz
  obtain ⟨w, -, rfl⟩ := hz
  exact ⟨w, rfl⟩

/-- The re-indexed pathwise aligned parent/child order: the majorant is literally the
`(Z.card)⁻¹`-weighted average of the children's coarse response over the physical `Finset`
`alignedChildren q j hn`, matching the averaging statement's left-hand side shape after
`normalizedBlock` is pulled through the finite sum. -/
theorem coarseBlock_aligned_children_le [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ) (hn : ℕ)
    (a : CoeffSpace d) :
    BlockMatLoewnerLE (coarseBlock (adaptedCell q (j + hn)) a)
      (ofFullBlockMat (((alignedChildren q j hn).card : ℝ)⁻¹ •
        ∑ z ∈ alignedChildren q j hn,
          toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a))) := by
  rw [alignedChildren_card q hq j hn, Nat.cast_pow, Nat.cast_ofNat, Finset.smul_sum]
  have hp := coarseBlock_aligned_parent_le q hq j hn a
  let := (alignedCenterSet_finite_card d j hn).1.fintype
  dsimp only at hp
  have hsum : ∑ z ∈ alignedChildren q j hn,
      ((3 : ℝ) ^ (d * hn))⁻¹ • toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a) =
        ∑ w : ↥{w : Fin d → ℤ | standardCellCenter j w ∈ centeredCube d (j + (hn : ℤ))},
          ((3 : ℝ) ^ (d * hn))⁻¹ • toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w.1) a) := by
    unfold alignedChildren
    rw [Finset.sum_image (fun w1 _ w2 _ h => adaptedCellCenter_injective q j hq h)]
    exact Finset.sum_subtype (alignedCenterSet_finite_card d j hn).1.toFinset
      (fun x => (alignedCenterSet_finite_card d j hn).1.mem_toFinset)
      (fun w => ((3 : ℝ) ^ (d * hn))⁻¹ • toFullBlockMat (coarseBlock (adaptedCellAtCenter q j w) a))
  rw [hsum]
  exact hp

/-- Every point of the coarse response of an adapted cell is pathwise positive semidefinite
(entrywise CG block positive-definiteness, `Book.Ch02.BlockPosDef`, transported through
`fullBlock_posDef_of_pos`): the a.e. positive-semidefiniteness the positive-gap argument needs
of its `F`. -/
theorem coarseBlock_adaptedCell_posSemidef [NeZero d] (q : Mat d) (hq : IsUnit q) (j : ℤ)
    (a : CoeffSpace d) :
    (toFullBlockMat (coarseBlock (adaptedCell q j) a)).PosSemidef := by
  have hsymm : IsSymmetricBlockMat (coarseBlock (adaptedCell q j) a) :=
    isSymmetricBlockMat_coarseBlockMatrix (adaptedCell q j) (⇑a.1)
  have hpos : Book.Ch02.BlockPosDef (coarseBlock (adaptedCellTranslate q j 0) a) :=
    blockPosDef_coarseBlock_adapted q hq j 0 a
  rw [adaptedCellTranslate_zero] at hpos
  exact (fullBlock_posDef_of_pos hsymm hpos).posSemidef

/-- The annealed identity: every aligned child, at any generation at or above `jStar`, has the
same annealed matrix as its parent's own generation-`j` adapted mean. -/
theorem annealedBlock_alignedChildren {P : Measure (CoeffSpace d)} (hstat : IsStationaryLaw P)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    {j : ℤ} (hj : (jStar : ℤ) ≤ j) (hn : ℕ) [NeZero d] {z : Vec d}
    (hz : z ∈ alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn) :
    annealedBlock P (adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j z) =
      adaptedMean P (Geometry.explicitRoundedGrid jStar m) j := by
  simp only [alignedChildren, Finset.mem_image, Set.Finite.mem_toFinset] at hz
  obtain ⟨w, -, rfl⟩ := hz
  exact annealedBlock_adaptedCellAtCenter P hstat jStar hjStar m hm j hj w

/-- The aligned-children equal-weight average is in `L^N(S_N)`: the "bounded-window estimate
gives the required integrability" sentence of `p.fixed.geometry.parent.child.recurrence` (`e.source.adapted.bound`), applied
to each child and combined by `Source.memLqSchatten_finset_sum`. No membership premise is added
to any consumer; this is finiteness only. -/
theorem memLqSchatten_alignedChildren_average (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hn : ℕ) (N : ℝ) (hN : 1 ≤ N) :
    MemLqSchatten P N (fun a => ofFullBlockMat
      (((alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn).card : ℝ)⁻¹ •
        ∑ z ∈ alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn,
          toFullBlockMat (coarseBlock
            (adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j z) a))) :=
  by
    have h := Source.memLqSchatten_finset_sum hN
      (alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn)
      (fun _ => ((alignedChildren (Geometry.explicitRoundedGrid jStar m) j hn).card : ℝ)⁻¹)
      (fun z a => coarseBlock (adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m) j z) a)
      (fun z _ => Source.memLqSchatten_coarseBlock_adapted d hd P γ E Ψ K S hstat hdag
        jStar hjStar m hm j z N hN)
    simpa only [Finset.smul_sum] using h

/-- The entrywise expectation of the actual aligned average is the child-scale mean. -/
theorem integral_alignedChildren_average (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hn : ℕ) (hj : (jStar : ℤ) ≤ j) :
    ofFullBlockMat (fun α β => ∫ a, blockMatEntry
      (ofFullBlockMat (((alignedChildren (explicitRoundedGrid jStar m) j hn).card : ℝ)⁻¹ •
        ∑ z ∈ alignedChildren (explicitRoundedGrid jStar m) j hn,
          toFullBlockMat (coarseBlock (adaptedCellTranslate (explicitRoundedGrid jStar m) j z) a)))
      α β ∂P) = adaptedMean P (explicitRoundedGrid jStar m) j := by
  let : NeZero d := ⟨by omega⟩
  let q := explicitRoundedGrid jStar m
  let Z := alignedChildren q j hn
  have hc (z : Vec d) := hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K S
    hstat hdag jStar hjStar m hm j z
  have hcard : (Z.card : ℝ) ≠ 0 := by
    exact_mod_cast (alignedChildren_nonempty q j hn).card_pos.ne'
  rw [← ofFullBlockMat_toFullBlockMat (adaptedMean P q j)]
  congr 1
  funext α β
  have he (z : Vec d) (hz : z ∈ Z) :
      (∫ a, blockMatEntry (coarseBlock (adaptedCellTranslate q j z) a) α β ∂P) =
        blockMatEntry (adaptedMean P q j) α β := by
    rw [← blockMatEntry_annealedBlock,
      annealedBlock_alignedChildren hstat jStar hjStar m hm hj hn hz]
  change (∫ a, blockMatEntry (ofFullBlockMat ((Z.card : ℝ)⁻¹ •
    ∑ z ∈ Z, toFullBlockMat (coarseBlock (adaptedCellTranslate q j z) a))) α β ∂P) = _
  simp only [blockMatEntry_ofFullBlockMat, Matrix.smul_apply, Matrix.sum_apply,
    smul_eq_mul, toFullBlockMat_eq_blockMatEntry]
  rw [integral_const_mul, integral_finsetSum _ (fun z _ => hc z α β)]
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

end

end Homogenization.HighContrast.Annealed
