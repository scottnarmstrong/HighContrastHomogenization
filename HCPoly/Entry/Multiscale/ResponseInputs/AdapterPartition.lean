import HCPoly.Entry.Multiscale.ResponseInputs.AdapterGeometry
import HCPoly.Entry.Multiscale.ResponseInputs.AdapterSummation

open Homogenization.HighContrast (CoeffSpace HasIntegrableCoarseBlock adaptedCellCenter
  annealedBlock blockScale)
open Homogenization.HighContrast (adaptedCellTranslate)
namespace Homogenization.HighContrast.Multiscale.Adapter

open MeasureTheory Geometry
open scoped Matrix.Norms.L2Operator

/-- Annealed comparison from the actual capped maximal-cell partition.
The parent and every child are open affine cubes with integrable entries. -/
theorem partition_comparison {d : ℕ} [NeZero d]
    (P : Measure (CoeffSpace d)) (q q' : Mat d) (hq : IsUnit q) (hq' : IsUnit q')
    (K : ℝ) (hK : 0 ≤ K) (hInv : InverseNormLE (q⁻¹ * q') K)
    (n cap : ℤ) (y : Vec d) (γ : ℝ) (hγ : γ < 1)
    (A E : BlockMat d) (hA : Book.Ch02.BlockPosDef A) (hE : Book.Ch02.BlockPosDef E)
    (c : ℝ) (hc : 0 ≤ c)
    (hWint : HasIntegrableCoarseBlock P (adaptedCellTranslate q' n y))
    (hint : ∀ (r : ℤ) (w : Fin d → ℤ), HasIntegrableCoarseBlock P (adaptedCellAtCenter q r w))
    (hcap : ∀ w : Fin d → ℤ, BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter q cap w)) A)
    (hlow : ∀ (r : ℤ), r < cap → ∀ w : Fin d → ℤ,
      BlockMatLoewnerLE (annealedBlock P (adaptedCellAtCenter q r w))
        (blockScale (c * (3 : ℝ) ^ (γ * ((cap : ℝ) - r))) E)) :
    BlockMatLoewnerLE (annealedBlock P (adaptedCellTranslate q' n y))
      (ofFullBlockMat (toFullBlockMat A +
        (c * ((6 * (d : ℝ) * K * Real.sqrt d) / (1 - (3 : ℝ) ^ (-(1 - γ)))) *
          (3 : ℝ) ^ (-((n : ℝ) - cap))) • toFullBlockMat E)) := by
  classical
  let W := adaptedCellTranslate q' n y
  let s := {p : ℤ × (Fin d → ℤ) | IsMaximalAdaptedCellIn W q cap p.1 p.2}
  let w (i : s) := (volume (adaptedCellAtCenter q i.1.1 i.1.2)).toReal / (volume W).toReal
  have hsub : ∀ i ∈ s, adaptedCellAtCenter q i.1 i.2 ⊆ W := fun _ hi => hi.1.2
  have hdis := pairwiseDisjoint_maximalAdaptedCellPairs W q hq cap
  have hnull := volume_diff_iUnion_maximalAdaptedCells_of_isOpen hq
    (isOpen_adaptedCellTranslate hq' n y) cap
  have hWfin : volume W ≠ ⊤ := volume_adaptedCellTranslate_ne_top q' n y
  have hw : Summable w := (maximal_mass q q' hq hq' n cap y).1
  have hw0 (i) : 0 ≤ w i := by dsimp [w]; positivity
  have hmass : (∑' i, w i) = 1 := (maximal_mass q q' hq hq' n cap y).2
  have hrow (r : ℤ) (hr : r < cap) :
      (∑' i : {i : s // i.1.1 = r}, w i) ≤
        (6 * (d : ℝ) * K * Real.sqrt d) * (3 : ℝ) ^ ((r : ℝ) - n) := by
    have hm := Annealed.bridge_maximal_row_mass W q hq cap r
      (finite_maximalAdaptedCellCenters_of_volume_ne_top hq hWfin cap r) (volume W).toReal
    exact hm.2.trans_le (lower_row_volume hq hq' hK hInv n cap r hr y)
  obtain ⟨hs, ht⟩ := fine_weight_bound w (fun i => i.1.1) hw0 hw cap n
    (6 * (d : ℝ) * K * Real.sqrt d) (by positivity) hrow γ hγ
  apply Annealed.bridge_annealed_partition_bound (Set.to_countable s) P q' hq' n y
    (fun _ => q) (fun _ _ => hq) (fun i => i.1) (fun i => adaptedCellCenter q i.1 i.2)
    _ hsub hdis hnull hWint (fun i _ => hint i.1 i.2)
  intro F
  have hb := finite_block_cap w (fun i => i.1.1)
    (fun i => annealedBlock P (adaptedCellAtCenter q i.1.1 i.1.2)) A E
    hw0 hw hmass.le cap (fun i => i.2.1.1) γ c _ hA hE hc
    (fun i hi => by simpa only [hi] using hcap i.1.2)
    (fun i hi => hlow i.1.1 hi i.1.2) hs ht F
  simpa only [mul_assoc] using! hb

end Homogenization.HighContrast.Multiscale.Adapter
